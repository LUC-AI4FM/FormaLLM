# Benchmarks

Frontier-model evaluation results on the FormaLLM val set (`outputs/val.json`, 30 targets).

## Layout

```
benchmarks/
├── data_matrix.csv          ← one row per LLM, summary metrics
├── per_target_matrix.csv    ← one row per val target, one column per LLM
└── <llm-id>/
    ├── EVAL_REPORT.md       ← human-readable writeup
    ├── results_matrix.csv   ← per-target SANY + TLC + state counts + error reason
    ├── evaluation_results.csv  ← the canonical PASS/FAIL/ERROR per spec (matches the format compare_models.py expects)
    ├── sany_summary.txt
    ├── tlc_summary.txt
    ├── generated/           ← LLM-produced .tla + .cfg (30 each, 4 stubs)
    ├── sany_logs/           ← per-spec SANY output
    └── evaluations/         ← per-spec TLC output
```

## Currently included

| LLM | Variant | Date | Pass Rate (flat) | Pass Rate (non-vacuous) |
|---|---|---|---|---|
| `claude-opus-4-7[1m]` | shot0 | 2026-05-11 | 26.67% (8/30) | **23.33%** (7/30) |
| `claude-opus-4-7[1m]` | shot1 | 2026-05-11 | 30.00% (9/30) | 16.67% (5/30) |
| `claude-opus-4-7[1m]` | shot3 (default) | 2026-05-11 | 26.67% (8/30) | 16.67% (5/30) |
| `claude-opus-4-7[1m]` | shot5 | 2026-05-11 | 16.67% (5/30) | 13.33% (4/30) |

See [ABLATION_REPORT.md](ABLATION_REPORT.md) for the per-shot analysis. Headline: **0-shot beats few-shot for this model** with the pipeline's default fixed-prefix exemplar selector.

## Adding a new model

1. Run the pipeline (or evaluate directly) under `outputs/<backend>_<model>/`.
2. Build the per-spec `results_matrix.csv` (see `outputs/anthropic_claude-opus-4-7-1m/build_matrix.py` for the script).
3. Copy the directory subtree into `benchmarks/<llm-id>/` (mirror the structure above).
4. Append one row to `benchmarks/data_matrix.csv` and one column to `benchmarks/per_target_matrix.csv`.
5. Update the table above.

## Metric definitions

- **`SANY_PASS`** — `tla2sany.SANY` returns 0 errors and reports `Linting of module X`.
- **`TLC PASS`** — TLC log contains `Model checking completed. No error has been found.`.
- **`TLC PASS (vacuous)`** — TLC reports PASS but the log shows `0 distinct states found` (i.e. the spec admits no initial states — the LLM produced valid syntax but a model-empty cfg).
- **`TLC FAIL`** — an invariant or property was violated (a real semantic disagreement between the generated spec and the ground-truth intent).
- **`TLC ERROR`** — TLC could not start: bad cfg syntax, missing constants, undefined operators, missing module deps, or stub specs from `comments_clean: null` rows in val.json.

The flat success rate is `PASS / Total`. The non-vacuous rate excludes both vacuous PASSes and stub-skipped rows from the numerator (vacuous → not really a PASS; stub → not the model's fault).
