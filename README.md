# LLM-Powered Isabelle/HOL Theorem Prover

This repository implements an Isabelle/HOL theorem prover guided by Large Language Models (LLMs). It integrates Isabelle's proof engine with LLMs (via Ollama, Gemini CLI, Hugging Face, etc.) to automatically generate and verify proofs.

Built on top of [llm-isabelle](https://github.com/zhehou/llm-isabelle) by Zhe Hou.

---

## Main Additions

This repo completes the WIP features in the original repository and adds several improvements to the planner subsystem:

### 1. CEGIS style Proof Repair Loop (`planner/driver.py`)
Rewrote the main loop in `plan_and_fill` to correctly implement the CEGIS design:
- **Earliest failure routing** — always looks for first Isabelle error in the script, not just the first `sorry` placeholder. Non sorry type failures (bad `have`/`show`, type errors) now trigger Repair directly instead of attempting Fill first.
- **Fill/Repair state separation** — separate tracking of fill attempts, repair stage, and repair attempts per hole, replacing the original tangled state machine.
- **Fill after Repair** — after any Repair that introduces new `sorry` placeholders, fill attempt counts are reset so newly introduced holes get fresh Fill tries before it escalates.

### 2. Fill Insertion Fix (`planner/driver.py`)
Fixed a bug in `_fill_one_hole` where the prover would find a valid tactic but fail to insert it correctly. The original code replaced only the `sorry` token, leaving malformed whitespace. The fix replaces the entire `sorry` line with properly indented tactics which matches Isabelle's expected syntax.

### 3. Repair Stage Escalation Fix (`planner/repair.py`)
Fixed few issues in `try_cegis_repairs` and `_repair_block`:
- Each repair stage will now return immediately on any change, letting the driver re-run Fill before escalating further.
- `_repair_block` now returns the original text on total failure instead of a mutated intermediate state which makes "no progress" detection reliable.
- Stage 3 (whole proof regeneration) is now integrated directly into `try_cegis_repairs` as a natural escalation from stages 1 and 2.

### 4. Case Name Post-Processing (`planner/driver.py`)
Added `_fix_case_names()`, a post-processing step applied to all generated outlines before the CEGIS loop begins. Fixes LLM naming errors:
- `case L` / `case R` → `case left` / `case right` (disjunction)
- `case Zero` / `case Succ` → `case 0` / `case Suc` (natural number induction)


---

## Benchmark Results

Evaluated on HOL test datasets using `qwen2.5-coder:7b` (local, no GPU) on a M3 MacBook Pro with 18GB memory:

| Method | Easy (100 goals) | Mid (50 goals) | Hard (50 goals) |
|---|---|---|---|
| Sledgehammer only (baseline) | 84% | 74% | 58% |
| **LLM + CEGIS (ours)** | **76%** | **82%** | **66%** |

### Detailed Results
Full benchmark CSVs are available in [`results`](results).

Our system outperforms sledgehammer on mid and hard goals (+8% each), demonstrating that LLM guided structured proof search adds value where Sledgehammer struggles. 

Results were obtained using `qwen2.5-coder:7b` running locally via Ollama. Larger models (e.g. `gemini-2.5-flash`, `qwen3-coder:30b`) are expected to produce significantly better results.

---

## Installation

### Prerequisites
- Python 3.10–3.12
- Isabelle/HOL (tested with Isabelle2025) — ensure `isabelle` is on your `$PATH`
- GNU Make, g++

### Python setup
```bash
python3 -m venv .venv
source .venv/bin/activate
pip install -U pip
pip install -r requirements.txt
```

### Ollama (local LLMs)
```bash
# Install from https://ollama.ai then pull a model
ollama serve &
ollama pull qwen2.5-coder:7b
```

### Gemini (hosted)
```bash
# Install Gemini CLI following the instructions here: https://www.geminicli.cc/docs/installation
pipx install gemini-cli
gemini setup #(one time setup)
export GEMINI_API_KEY=your_key_here
```

---

## Usage

### Run the planner on a single goal
```bash
python -m planner.cli --mode auto --timeout 120 --model "qwen2.5-coder:7b" "rev (rev xs) = xs"
```

### Run the prover
```bash
python -m prover.cli --goal "rev (rev xs) = xs" --model "qwen2.5-coder:7b" --sledge
```

### Benchmark
```bash
python -m planner.experiments bench \
  --file datasets/hol_main_easy_goals_test.txt \
  --mode auto --k 1 --timeout 120 \
  --model "qwen2.5-coder:7b"
```

### Sledgehammer-only baseline
```bash
python baselines/sledge_only.py \
  --file datasets/hol_main_easy_goals_test.txt \
  --imports Main \
  --provers "e z3 vampire cvc5" \
  --sledge-timeout 30 \
  --goal-timeout 30
  --print-logs
```

---

## Project Structure

```
datasets/          # Datasets and benchmark results
planner/           # Proof outline planner (driver.py, repair.py — main contributions)
prover/            # Stepwise prover
baselines/         # Sledgehammer-only baseline
isabelle_ui/       # Isabelle/jEdit GUI integration
logs/              # Training logs
```

---


## Contributors

- [Abhishek Nambiar](https://github.com/Silverizz)
- [Cody Noll](https://github.com/CodyNoll)
- [Farah Hannah Abdurahman](https://github.com/hannahabdrhmn)
- [Kartik Lamba](https://github.com/kartiklamba69)

## Citation

This work builds on:

```bibtex
@misc{hou2026arxiv,
      title={Vibe Coding an LLM-powered Theorem Prover}, 
      author={Zhe Hou},
      year={2026},
      eprint={2601.04653},
      archivePrefix={arXiv},
      primaryClass={cs.AI},
      url={https://arxiv.org/abs/2601.04653}, 
}
```
