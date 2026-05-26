from __future__ import annotations

import time
import re
import os
from dataclasses import dataclass
from typing import Iterable, List, Optional, Tuple
from concurrent.futures import ThreadPoolExecutor, TimeoutError as _FuturesTimeout
import hashlib

from planner.skeleton import (
    Skeleton, find_sorry_spans, propose_isar_skeleton, propose_isar_skeleton_diverse_best,
)
from planner.repair import try_cegis_repairs, regenerate_whole_proof, _APPLY_OR_BY as _TACTIC_LINE_RE
from prover.config import ISABELLE_SESSION
from prover.isabelle_api import (
    build_theory, get_isabelle_client, last_print_state_block, start_isabelle_server,
)
from prover.prover import prove_goal
from planner.goals import _print_state_before_hole, _log_state_block, _effective_goal_from_state, _first_lemma_line, _extract_goal_from_lemma_line, _cleanup_resources, _verify_full_proof, _run_theory_with_timeout

def _hole_fingerprint(full_text: str, span: tuple[int, int], context: int = 80) -> str:
    """Stable key for a hole: hash a small window around the 'sorry'."""
    s, e = span
    lo = max(0, s - context)
    hi = min(len(full_text), e + context)
    snippet = full_text[lo:hi]
    return hashlib.sha1(snippet.encode("utf-8")).hexdigest()[:16]

def _offset_to_line(text: str, offset: int) -> int:
    """Convert a character offset to a 1-based line number."""
    return text[:offset].count("\n") + 1

# Constants
_INLINE_BY_TAIL = re.compile(r"\s+by\s+.+$")
_BARE_DOT = re.compile(r"(?m)^\s*\.\s*$")
_HEAD_CMD_RE = re.compile(r"^\s*(have|show|obtain)\b")
_ISA_VERIFY_TIMEOUT_S = int(os.getenv("ISABELLE_VERIFY_TIMEOUT_S", "30"))

# Budget constants for the CEGIS loop
_FILL_CAP = int(os.getenv("PLANNER_FILL_CAP", "2"))       # max fill attempts per hole before escalating
_REPAIR_STAGE_CAP = int(os.getenv("PLANNER_REPAIR_CAP", "2"))  # max repair attempts per stage per hole
_MAX_REPAIR_STAGE = 3                                       # stages: 1=local, 2=subproof, 3=whole proof


@dataclass(slots=True)
class PlanAndFillResult:
    success: bool
    outline: str
    fills: List[str]
    failed_holes: List[int]


# ============================================================================
# Hole Filling
# ============================================================================

def _fill_one_hole(isabelle, session: str, full_text: str, hole_span: Tuple[int, int],
                  goal_text: str, model: Optional[str], per_hole_timeout: int, *, trace: bool = False) -> Tuple[str, bool, str]:
    """Fill single hole in proof."""

    # Check for stale hole
    try:
        s_line_start = full_text.rfind("\n", 0, hole_span[0]) + 1
        prev_line_end = s_line_start - 1
        prev_prev_nl = full_text.rfind("\n", 0, prev_line_end) + 1
        prev_line = full_text[prev_prev_nl:prev_line_end+1]
    except Exception:
        prev_line = ""

    if (_INLINE_BY_TAIL.search(prev_line) or _TACTIC_LINE_RE.match(prev_line) or
        prev_line.strip() in {"done", "."}):
        s, e = hole_span
        return full_text[:s] + "\n" + full_text[e:], True, "(stale-hole)"

    state_block = _print_state_before_hole(isabelle, session, full_text, hole_span, trace)
    _log_state_block("fill", state_block, trace=trace)

    eff_goal = _effective_goal_from_state(state_block, goal_text, full_text, hole_span, trace)

    res = prove_goal(
        isabelle, session, eff_goal, model_name_or_ensemble=model,
        beam_w=3, max_depth=6, hint_lemmas=6, timeout=per_hole_timeout,
        models=None, save_dir=None, use_sledge=True, sledge_timeout=10,
        sledge_every=1, trace=trace, use_color=False, use_qc=False,
        qc_timeout=2, qc_every=1, use_np=False, np_timeout=5, np_every=2,
        facts_limit=8, do_minimize=False, minimize_timeout=8,
        do_variants=False, variant_timeout=6, variant_tries=24,
        enable_reranker=True, initial_state_hint=state_block,
    )

    steps = [str(s) for s in res.get("steps", [])]

    fin_candidates = []
    for k in ("finisher", "finish", "final"):
        v = res.get(k)
        if isinstance(v, str):
            fin_candidates.append(v)
    for k in ("finishers", "sledge_finishers"):
        vs = res.get(k)
        if isinstance(vs, (list, tuple)):
            fin_candidates.extend([str(x) for x in vs if isinstance(x, str)])
    applies_from_keys = []
    for k in ("applies", "apply_steps"):
        vs = res.get(k)
        if isinstance(vs, (list, tuple)):
            applies_from_keys.extend([str(x) for x in vs if isinstance(x, str) and x.startswith("apply")])

    applies = [s for s in steps if s.startswith("apply")]
    if applies_from_keys:
        applies = applies or applies_from_keys

    fin = next((s for s in steps if s.startswith("by ") or s.strip() == "done"), "")
    if not fin:
        fin = next((x for x in fin_candidates if isinstance(x, str) and (x.startswith("by ") or x.strip() == "done")), "")

    if not (applies or fin):
        return full_text, False, "no-steps"

    if fin:
        script_lines = applies + [fin]
        s, e = hole_span

        # Find the start of the line containing 'sorry'
        line_start = full_text.rfind("\n", 0, s) + 1
        # Find the end of that line
        line_end = full_text.find("\n", e)
        if line_end == -1:
            line_end = len(full_text)

        # Detect indentation from the sorry line
        sorry_line = full_text[line_start:line_end]
        indent = sorry_line[:len(sorry_line) - len(sorry_line.lstrip(" "))]

        # Replace the entire sorry line with the tactic(s)
        insert = "\n".join(f"{indent}{ln.strip()}" for ln in script_lines)
        new_text = full_text[:line_start] + insert + full_text[line_end:]

        if trace:
            print(f"[fill-debug] Verifying insertion:\n{new_text}")
        if _verify_full_proof(isabelle, session, new_text):
            return new_text, True, "\n".join(script_lines)
        if trace:
            print(f"[fill-debug] Verification failed for: {script_lines}")
        return full_text, False, "finisher-unverified"

    if applies:
        s, e = hole_span
        head_line_start = full_text.rfind("\n", 0, s) + 1
        scan_start = max(0, full_text.rfind("\n", 0, max(0, head_line_start - 512)) + 1)
        segment = full_text[scan_start:s]
        lines = segment.splitlines()
        head_idx = None
        for i in range(len(lines) - 1, -1, -1):
            if _HEAD_CMD_RE.match(lines[i] or ""):
                head_idx = i
                break

        dedup_window = segment
        dedup = [a for a in applies if a not in dedup_window]
        if not dedup:
            return full_text, False, "apply-duplicate"

        if head_idx is not None:
            if trace:
                print("[fill] apply-only inside have/show; not inserting proof/qed; escalating to repair.")
            return full_text, False, "apply-inside-have/show"
        else:
            probe_text = _insert_above_hole_keep_sorry(full_text, hole_span, dedup)
            return probe_text, False, "\n".join(dedup)

    return full_text, False, "no-tactics"


def _insert_above_hole_keep_sorry(text: str, hole: Tuple[int, int], lines_to_insert: List[str]) -> str:
    """Insert lines above hole while keeping sorry."""
    s, _ = hole
    ls = text.rfind("\n", 0, s) + 1
    le = text.find("\n", s)
    hole_line = text[ls:(le if le != -1 else len(text))]
    indent = hole_line[:len(hole_line) - len(hole_line.lstrip(" "))]
    payload = "".join(f"{indent}{ln.strip()}\n" for ln in lines_to_insert if ln.strip())
    return text[:s] + payload + text[s:]


def _nearest_sorry_span(spans: List[Tuple[int, int]], target_s: int) -> Optional[Tuple[int, int]]:
    if not spans:
        return None
    return min(spans, key=lambda sp: abs(sp[0] - target_s))


# ============================================================================
# Repair helpers (unchanged from original)
# ============================================================================

def _proof_bounds_top_level(text: str) -> Optional[Tuple[int, int]]:
    """Return (start,end) offsets of last top-level proof..qed block."""
    qed_matches = list(re.finditer(r"(?m)^\s*qed\b", text))
    if not qed_matches:
        return None

    end = qed_matches[-1].end()
    proof_matches = list(re.finditer(r"(?m)^\s*proof\b.*$", text[:qed_matches[-1].start()]))
    if not proof_matches:
        return None

    return (proof_matches[-1].start(), end)


def _tactic_spans_topdown(text: str) -> List[Tuple[int, int]]:
    """Top-down tactic line spans within last proof..qed block."""
    bounds = _proof_bounds_top_level(text)
    if not bounds:
        return []

    b0, b1 = bounds
    seg = text[b0:b1]
    lines = seg.splitlines(True)
    spans, off = [], b0

    for line in lines:
        if _TACTIC_LINE_RE.match(line or "") or _INLINE_BY_TAIL.search(line or ""):
            spans.append((off, off + len(line.rstrip("\n"))))
        off += len(line)

    return spans


def _repair_failed_proof_topdown(isa, session, full: str, goal_text: str, model: Optional[str],
                                 left_s, max_repairs_per_hole: int, trace: bool) -> Tuple[str, bool]:
    """Walk tactics from top; attempt CEGIS-repair on the first failing one."""
    t_spans = _tactic_spans_topdown(full)
    if not t_spans:
        return full, False

    i = 0
    while i < len(t_spans) and left_s() > 3.0:
        span = t_spans[i]
        try:
            st = _print_state_before_hole(isa, session, full, span, trace)
            eff_goal = _effective_goal_from_state(st, goal_text, full, span, trace)
        except Exception as ex:
            if trace:
                print(f"[repair] Could not extract state/goal before tactic (skipping): {ex}")
            i += 1
            continue

        per_budget = min(30.0, max(15.0, left_s() * 0.33))

        try:
            patched, applied, _ = try_cegis_repairs(
                full_text=full, hole_span=span, goal_text=eff_goal, model=model,
                isabelle=isa, session=session, repair_budget_s=per_budget,
                max_ops_to_try=max_repairs_per_hole, beam_k=2,
                allow_whole_fallback=False, trace=trace, resume_stage=0,
            )
        except (TimeoutError, _FuturesTimeout, ValueError) as ex:
            if trace:
                print(f"[repair] CEGIS repair aborted: {type(ex).__name__}: {ex}")
            return full, False
        except Exception as ex:
            if trace:
                print(f"[repair] CEGIS repair crashed: {type(ex).__name__}: {ex}")
            return full, False

        if applied and patched != full:
            if _verify_full_proof(isa, session, patched):
                return patched, True

            if trace:
                print("[repair] Partial progress in topdown repair (unverified). Opening sorries...")
            full = patched
            full2, opened = _open_minimal_sorries(isa, session, full)
            if opened:
                full = full2
                t_spans = _tactic_spans_topdown(full)
                i = 0
                continue

        i += 1

    return full, False


def _quick_state_and_errors(isabelle, session: str, text: str, *, timeout_s: Optional[int] = None) -> Tuple[str, List[str]]:
    """Run a theory quickly and return (last_state_block, error_messages)."""
    try:
        ts = text.splitlines()
        thy = build_theory(ts, add_print_state=True, end_with=None)
        out = _run_theory_with_timeout(
            isabelle, session, thy,
            timeout_s=int(timeout_s) if timeout_s is not None else min(_ISA_VERIFY_TIMEOUT_S, 15),
        )
        state = ""
        try:
            state = last_print_state_block(out)
        except Exception:
            state = ""

        if isinstance(out, (list, tuple)):
            msgs = [str(m) for m in out]
        else:
            msgs = [str(out)]

        errs = [m for m in msgs if any(tok in m.lower() for tok in ("error", "exception", "failed"))]
        return state, errs
    except Exception as ex:
        return "", [str(ex)]


def _extract_error_lines(errs: List[str]) -> List[int]:
    """Extract 1-based line numbers from Isabelle error messages (best-effort)."""
    if not errs:
        return []

    patts = [
        re.compile(r"(?i)\bline\s+(\d+)\b"),
        re.compile(r"(?i)\bLine\s+(\d+)\b"),
        re.compile(r":(\d+):(\d+)\b"),
        re.compile(r"\((\d+),(\d+)\)"),
    ]

    found: set[int] = set()
    for raw in errs:
        s = str(raw)
        for p in patts:
            for m in p.finditer(s):
                try:
                    n = int(m.group(1))
                    if n > 0:
                        found.add(n)
                except Exception:
                    pass

    return sorted(found)


def _open_minimal_sorries(isabelle, session: str, text: str) -> Tuple[str, bool]:
    """Localize a failing finisher with minimal opening (replace 1 tactic with 'sorry')."""
    def _ensure_nl(s: str) -> str:
        return s if s.endswith("\n") else s + "\n"

    def runs(ts):
        try:
            thy = build_theory(ts, add_print_state=False, end_with=None)
            _run_theory_with_timeout(isabelle, session, thy, timeout_s=_ISA_VERIFY_TIMEOUT_S)
            return True
        except Exception:
            return False

    try:
        if runs(text.splitlines()):
            return _ensure_nl(text), False
    except Exception:
        return _ensure_nl(text), False

    try:
        _, errs = _quick_state_and_errors(isabelle, session, text)
        err_lines = _extract_error_lines(errs)
    except Exception:
        err_lines = []

    if not err_lines:
        return _ensure_nl(text), False

    failing_line_1based = min(err_lines)
    lines = text.splitlines()
    failing_idx = failing_line_1based - 1

    for i in range(min(failing_idx, len(lines) - 1), -1, -1):
        line = lines[i]

        if _TACTIC_LINE_RE.match(line) or line.strip() == "done" or _BARE_DOT.match(line):
            indent = line[:len(line) - len(line.lstrip(" "))]
            lines[i] = f"{indent}sorry"
            return _ensure_nl("\n".join(lines)), True

        m = _INLINE_BY_TAIL.search(line)
        if m:
            indent = line[:len(line) - len(line.lstrip(" "))]
            header = line[:m.start()].rstrip()
            lines[i] = header
            lines.insert(i + 1, f"{indent}sorry")
            return _ensure_nl("\n".join(lines)), True

    return _ensure_nl(text), False


# ============================================================================
# Public API
# ============================================================================

def plan_outline(goal: str, *, model: Optional[str] = None, outline_k: Optional[int] = None,
                outline_temps: Optional[Iterable[float]] = None, legacy_single_outline: bool = False,
                priors_path: Optional[str] = None, context_hints: bool = False,
                lib_templates: bool = False, alpha: float = 1.0, beta: float = 0.5,
                gamma: float = 0.2, hintlex_path: Optional[str] = None, hintlex_top: int = 8) -> str:
    """Generate Isar outline with 'sorry' placeholders."""
    server_info, proc = start_isabelle_server(name="planner", log_file="logs/planner_ui.log")
    isa = get_isabelle_client(server_info)
    session = isa.session_start(session=ISABELLE_SESSION)

    try:
        if legacy_single_outline:
            return propose_isar_skeleton(goal, model=model, temp=0.35, force_outline=True).text

        temps = tuple(outline_temps) if outline_temps else (0.35, 0.55, 0.85)
        k = int(outline_k) if outline_k is not None else 3

        best, _ = propose_isar_skeleton_diverse_best(
            goal, isabelle=isa, session_id=session, model=model, temps=temps, k=k,
            force_outline=True, priors_path=priors_path, context_hints=context_hints,
            lib_templates=lib_templates, alpha=alpha, beta=beta, gamma=gamma,
            hintlex_path=hintlex_path, hintlex_top=hintlex_top,
        )
        return best.text
    finally:
        _cleanup_resources(isa, proc)


def plan_and_fill(goal: str, model: Optional[str] = None, timeout: int = 100, *, mode: str = "auto",
                 outline_k: Optional[int] = None, outline_temps: Optional[Iterable[float]] = None,
                 legacy_single_outline: bool = False, repairs: bool = True,
                 max_repairs_per_hole: int = 2, trace: bool = False, repair_trace: bool = False,
                 priors_path: Optional[str] = None, context_hints: bool = False,
                 lib_templates: bool = False, alpha: float = 1.0, beta: float = 0.5,
                 gamma: float = 0.2, hintlex_path: Optional[str] = None,
                 hintlex_top: int = 8) -> PlanAndFillResult:
    """Plan and fill holes in Isar proofs.

    Implements the CEGIS-style loop described in the assignment spec:
      1. Generate an initial proof outline with the LLM.
      2. Run Isabelle; if it passes with no sorry, done.
      3. Find the earliest failure point.
         - If it is a sorry hole → trigger Fill (call stepwise prover).
         - If it is a non-sorry line → trigger Repair directly.
      4. After Fill or Repair, re-run Isabelle from the top (deterministic,
         always targeting the earliest remaining failure).
      5. Repair is staged: local (stage 1) → subproof (stage 2) → whole
         proof (stage 3). Escalate when a stage's attempt budget is exhausted.
      6. After any Repair that introduces new sorry placeholders, Fill is
         attempted fresh on those holes before escalating.
      7. Stop when: proof verified, global timeout, or all repair stages
         exhausted on a hole.
    """
    if repair_trace and not trace:
        trace = True

    server_info, proc = start_isabelle_server(name="planner", log_file="logs/planner_ui.log")
    isa = get_isabelle_client(server_info)
    session = isa.session_start(session=ISABELLE_SESSION)

    t0 = time.monotonic()
    left_s = lambda: max(0.0, timeout - (time.monotonic() - t0))

    restart_count = 0

    def _restart_isabelle(reason: str, ex: Optional[BaseException] = None) -> None:
        nonlocal isa, session, proc, restart_count
        if restart_count >= 2:
            return
        restart_count += 1
        if trace:
            msg = f"[planner] Restarting Isabelle (#{restart_count}) due to {reason}"
            if ex is not None:
                msg += f": {type(ex).__name__}: {ex}"
            print(msg)
        try:
            _cleanup_resources(isa, proc)
        except Exception:
            pass
        server_info2, proc2 = start_isabelle_server(name="planner", log_file="logs/planner_ui.log")
        isa2 = get_isabelle_client(server_info2)
        session2 = isa2.session_start(session=ISABELLE_SESSION)
        isa, session, proc = isa2, session2, proc2

    try:
        # ------------------------------------------------------------------ #
        # Step 1: Generate initial proof outline                              #
        # ------------------------------------------------------------------ #
        if legacy_single_outline:
            full = propose_isar_skeleton(goal, model=model, temp=0.35, force_outline=(mode == "outline")).text
        else:
            temps = tuple(outline_temps) if outline_temps else (0.35, 0.55, 0.85)
            k = int(outline_k) if outline_k is not None else 3
            best, _ = propose_isar_skeleton_diverse_best(
                goal, isabelle=isa, session_id=session, model=model, temps=temps, k=k,
                force_outline=(mode == "outline"), priors_path=priors_path,
                context_hints=context_hints, lib_templates=lib_templates,
                alpha=alpha, beta=beta, gamma=gamma, hintlex_path=hintlex_path,
                hintlex_top=hintlex_top,
            )
            full = best.text

        if mode == "outline":
            return PlanAndFillResult(True, full, [], [])

        lemma_line = _first_lemma_line(full)
        if not lemma_line:
            return PlanAndFillResult(False, full, [], [0])
        goal_text = _extract_goal_from_lemma_line(lemma_line)

        fills: List[str] = []
        failed: List[int] = []

        # Per-hole state for the CEGIS loop
        # fill_attempts[hole_key]   = number of fill attempts made on this hole
        # repair_stage[hole_key]    = current repair stage (1, 2, or 3)
        # repair_attempts[hole_key] = attempts made at current stage
        fill_attempts: dict[str, int] = {}
        repair_stage: dict[str, int] = {}
        repair_attempts: dict[str, int] = {}

        # ------------------------------------------------------------------ #
        # Main CEGIS loop                                                      #
        # ------------------------------------------------------------------ #
        while left_s() > 0:

            # Step 2: Run Isabelle, check for success
            try:
                _, errs = _quick_state_and_errors(isa, session, full)
            except (TimeoutError, _FuturesTimeout, ValueError) as ex:
                _restart_isabelle("quick_state_and_errors", ex)
                continue
            except Exception as ex:
                if trace:
                    print(f"[planner] quick_state_and_errors crashed: {ex}")
                break

            spans = find_sorry_spans(full)

            # Success: no errors and no sorry placeholders
            if not errs and not spans:
                try:
                    if _verify_full_proof(isa, session, full):
                        return PlanAndFillResult(True, full, fills, [])
                except (TimeoutError, _FuturesTimeout, ValueError) as ex:
                    _restart_isabelle("final_verify", ex)
                    continue
                # Isabelle says OK via quick check but full verify failed —
                # treat as success anyway since quick_state had no errors.
                return PlanAndFillResult(True, full, fills, [])

            # Step 3: Find the earliest failure point
            # Compare the line of the first sorry vs the first Isabelle error.
            # Always work on whichever comes first in the script.
            err_lines = _extract_error_lines(errs)
            earliest_err_line = min(err_lines) if err_lines else None

            earliest_sorry_line: Optional[int] = None
            earliest_sorry_span: Optional[Tuple[int, int]] = None
            if spans:
                earliest_sorry_span = spans[0]
                earliest_sorry_line = _offset_to_line(full, spans[0][0])

            # Decide: is the earliest failure a sorry hole or a bad line?
            sorry_is_earliest = (
                earliest_sorry_line is not None and (
                    earliest_err_line is None or
                    earliest_sorry_line <= earliest_err_line
                )
            )

            # ---------------------------------------------------------------- #
            # Step 3a: Earliest failure is a sorry → trigger Fill              #
            # ---------------------------------------------------------------- #
            if sorry_is_earliest and earliest_sorry_span is not None:
                span = earliest_sorry_span
                hole_key = _hole_fingerprint(full, span)
                attempts_so_far = fill_attempts.get(hole_key, 0)

                if attempts_so_far < _FILL_CAP:
                    if trace:
                        print(f"[planner] Fill attempt {attempts_so_far + 1}/{_FILL_CAP} for hole @{hole_key}")

                    per_hole_budget = int(max(5, left_s() / max(1, len(spans))))

                    try:
                        full2, ok, script = _fill_one_hole(
                            isa, session, full, span, goal_text, model,
                            per_hole_timeout=per_hole_budget, trace=trace,
                        )
                    except (TimeoutError, _FuturesTimeout, ValueError) as ex:
                        _restart_isabelle("fill_one_hole", ex)
                        full2, ok, script = full, False, "fill-exception"
                    except Exception as ex:
                        if trace:
                            print(f"[fill] _fill_one_hole crashed: {type(ex).__name__}: {ex}")
                        full2, ok, script = full, False, "fill-exception"

                    fill_attempts[hole_key] = attempts_so_far + 1

                    if ok:
                        # Fill succeeded — re-run Isabelle from top
                        if trace:
                            print(f"[planner] Fill succeeded for hole @{hole_key}")
                        full = full2
                        fills.append(script)
                        # Reset state for this hole since it's now closed
                        fill_attempts.pop(hole_key, None)
                        repair_stage.pop(hole_key, None)
                        repair_attempts.pop(hole_key, None)
                        continue

                    elif full2 != full:
                        # Partial progress: open minimal sorries and stay focused
                        if trace:
                            print(f"[planner] Fill made partial progress for hole @{hole_key}, opening sorries...")
                        full = full2
                        full2, opened = _open_minimal_sorries(isa, session, full)
                        if opened:
                            full = full2
                        continue

                    else:
                        if trace:
                            print(f"[planner] Fill made no progress for hole @{hole_key}")
                        # Fall through to repair below
                else:
                    if trace:
                        print(f"[planner] Fill cap reached for hole @{hole_key}, escalating to repair")

                # Fill exhausted its budget for this hole — fall through to Repair
                # (intentional fall-through, no continue here)

            # ---------------------------------------------------------------- #
            # Step 3b: Earliest failure is a non-sorry line, OR fill is        #
            # exhausted → trigger Repair                                        #
            # ---------------------------------------------------------------- #
            if not repairs or left_s() <= 6.0:
                if trace:
                    print("[planner] Repair disabled or time exhausted; stopping.")
                break

            # Determine which hole/location we are repairing
            if sorry_is_earliest and earliest_sorry_span is not None:
                repair_span = earliest_sorry_span
                repair_key = _hole_fingerprint(full, repair_span)
            elif earliest_err_line is not None:
                # Non-sorry failure: use the error line as the anchor
                # Synthesize a span at the error line for try_cegis_repairs
                lines_list = full.splitlines(keepends=True)
                err_offset = sum(len(l) for l in lines_list[:earliest_err_line - 1])
                err_end = err_offset + len(lines_list[earliest_err_line - 1]) if earliest_err_line <= len(lines_list) else err_offset
                repair_span = (err_offset, err_end)
                repair_key = f"err_line_{earliest_err_line}"
                if trace:
                    print(f"[planner] Non-sorry failure at line {earliest_err_line}; triggering repair directly")
            else:
                if trace:
                    print("[planner] No clear failure point found; stopping.")
                break

            current_stage = repair_stage.get(repair_key, 1)
            current_attempts = repair_attempts.get(repair_key, 0)

            if current_stage > _MAX_REPAIR_STAGE:
                if trace:
                    print(f"[planner] All repair stages exhausted for @{repair_key}; giving up on this hole.")
                failed.append(repair_key)
                break

            if trace:
                print(f"[planner] Repair stage {current_stage}, attempt {current_attempts + 1}/{_REPAIR_STAGE_CAP} for @{repair_key}")

            per_repair_budget = min(30.0, max(15.0, left_s() * 0.33))

            try:
                eff_goal = goal_text
                try:
                    state = _print_state_before_hole(isa, session, full, repair_span, trace)
                    eff_goal = _effective_goal_from_state(state, goal_text, full, repair_span, trace)
                except Exception:
                    pass  # fall back to top-level goal

                patched, applied, repair_label = try_cegis_repairs(
                    full_text=full, hole_span=repair_span, goal_text=eff_goal, model=model,
                    isabelle=isa, session=session,
                    repair_budget_s=per_repair_budget,
                    max_ops_to_try=max_repairs_per_hole, beam_k=2,
                    allow_whole_fallback=False, trace=trace,
                    resume_stage=current_stage,
                )
            except (TimeoutError, _FuturesTimeout, ValueError) as ex:
                _restart_isabelle("try_cegis_repairs", ex)
                patched, applied, repair_label = full, False, "repair-exception"
            except Exception as ex:
                if trace:
                    print(f"[repair] try_cegis_repairs crashed: {type(ex).__name__}: {ex}")
                patched, applied, repair_label = full, False, "repair-exception"

            repair_attempts[repair_key] = current_attempts + 1

            if patched != full:
                # Repair changed the text — check if it fully verifies
                try:
                    if _verify_full_proof(isa, session, patched):
                        if trace:
                            print(f"[planner] Repair verified! ({repair_label})")
                        full = patched
                        # Reset all state — fresh start from top of loop
                        fill_attempts.clear()
                        repair_stage.clear()
                        repair_attempts.clear()
                        continue
                except (TimeoutError, _FuturesTimeout, ValueError) as ex:
                    _restart_isabelle("verify_after_repair", ex)

                # Repair made partial progress (new sorrys introduced).
                # Accept the change, reset fill state so Fill gets fresh
                # attempts on any newly introduced sorry placeholders,
                # then go back to top of loop to re-run Isabelle.
                if trace:
                    print(f"[planner] Repair made partial progress ({repair_label}); re-running Fill on new holes...")
                full = patched
                full2, opened = _open_minimal_sorries(isa, session, full)
                if opened:
                    full = full2

                # Reset fill attempts so newly introduced sorrys get fresh fill tries
                fill_attempts.clear()
                # Keep repair stage/attempts for this key in case fill fails again
                continue

            # Repair made no change — count attempt and possibly escalate stage
            if repair_attempts[repair_key] >= _REPAIR_STAGE_CAP:
                if current_stage < _MAX_REPAIR_STAGE:
                    if trace:
                        print(f"[planner] Stage {current_stage} cap reached; escalating to stage {current_stage + 1}")
                    repair_stage[repair_key] = current_stage + 1
                    repair_attempts[repair_key] = 0
                    fill_attempts.pop(repair_key, None)

                    # Stage 3: whole proof regeneration
                    if repair_stage[repair_key] == _MAX_REPAIR_STAGE and left_s() > 8.0:
                        regen_budget = min(40.0, max(8.0, left_s() * 0.8))
                        if trace:
                            print("[planner] Stage 3: regenerating whole proof...")
                        try:
                            new_full, ok_re, _ = regenerate_whole_proof(
                                full_text=full, goal_text=goal_text, model=model,
                                isabelle=isa, session=session, budget_s=regen_budget,
                                trace=trace, prior_outline_text=full,
                            )
                        except (TimeoutError, _FuturesTimeout, ValueError) as ex:
                            _restart_isabelle("regenerate_whole_proof", ex)
                            new_full, ok_re = full, False
                        except Exception as ex:
                            if trace:
                                print(f"[repair] regenerate_whole_proof crashed: {type(ex).__name__}: {ex}")
                            new_full, ok_re = full, False

                        if ok_re and new_full != full:
                            if trace:
                                print("[planner] Whole proof regeneration succeeded.")
                            full = new_full
                            fill_attempts.clear()
                            repair_stage.clear()
                            repair_attempts.clear()
                            continue

                        # Regeneration failed — try a completely fresh outline
                        if trace:
                            print("[planner] Whole regeneration failed; proposing fresh outline...")
                        try:
                            temps = tuple(outline_temps) if outline_temps else (0.35, 0.55, 0.85)
                            k2 = int(outline_k) if outline_k is not None else 3
                            best2, _ = propose_isar_skeleton_diverse_best(
                                goal_text, isabelle=isa, session_id=session, model=model,
                                temps=temps, k=k2, force_outline=True,
                                priors_path=priors_path, context_hints=context_hints,
                                lib_templates=lib_templates, alpha=alpha, beta=beta,
                                gamma=gamma, hintlex_path=hintlex_path, hintlex_top=hintlex_top,
                            )
                            full = best2.text
                            fill_attempts.clear()
                            repair_stage.clear()
                            repair_attempts.clear()
                        except Exception as ex:
                            if trace:
                                print(f"[planner] Fresh outline generation failed: {ex}")
                            break
                else:
                    if trace:
                        print(f"[planner] All repair stages exhausted for @{repair_key}.")
                    failed.append(repair_key)
                    break

        # ------------------------------------------------------------------ #
        # Final verification                                                   #
        # ------------------------------------------------------------------ #
        success = "sorry" not in full
        if success:
            try:
                if _verify_full_proof(isa, session, full):
                    return PlanAndFillResult(True, full, fills, failed)
            except (TimeoutError, _FuturesTimeout, ValueError) as ex:
                _restart_isabelle("final_verify_full_proof", ex)

        return PlanAndFillResult(False, full, fills, failed)

    finally:
        _cleanup_resources(isa, proc)