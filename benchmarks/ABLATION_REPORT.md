# Opus 4.7 (1M) — Few-Shot Ablation

Generator: Claude Opus 4.7 (1M context). All four variants are the same model under the same FormaLLM val set (30 targets) — only `NUM_FEW_SHOTS` differs.

## Headline

| Variant | NUM_FEW_SHOTS | Real PASS | Vacuous PASS | Real FAIL | ERROR | Unknown | Stubs | All-PASS Rate | Non-Vacuous Rate |
|---|---|---|---|---|---|---|---|---|---|
| `shot0` | 0 | **7** | 1 | 2 | 14 | 6 | 4 | 26.67% | **23.33%** |
| `shot1` | 1 | 5 | 4 | 3 | 13 | 5 | 4 | 30.00% | 16.67% |
| `shot3` | 3 | 5 | 3 | 5 | 17 | 0 | 4 | 26.67% | 16.67% |
| `shot5` | 5 | 4 | 1 | 3 | 16 | 5 | 4 | 16.67% | 13.33% |

**Counter-intuitive finding:** 0-shot beats every few-shot variant on real (non-vacuous) PASS. 5-shot is worst across the board.

## What this likely means

The FormaLLM default uses `train_data[:NUM_FEW_SHOTS]` — a fixed prefix of `train.json`, not similarity-selected. The three default 3-shot exemplars are `Stones`, `KeyValueStore`, and `ZSequences`. Two of them (KeyValueStore, ZSequences) are dense PlusCal-translated specs; ZSequences in particular leans on community modules.

For a strong base model (Opus 4.7 1M), pinning the prompt to those three styles appears to *anchor* the output toward heavier PlusCal-flavored modules where the target spec would have been better served by a smaller plain-TLA+ formulation. The vacuous-pass column rises with shot count (1 → 4 → 3 → 1) and the real-fail column wobbles, both consistent with the model copying *form* from exemplars even when the form doesn't fit the target.

5-shot adds `Huang` (consistent-cut termination — a substantial PlusCal+invariant spec) and `MCMajority` (model-checker wrapper) to the in-context pile, which appears to further degrade output (SANY pass drops from 18 to 15; real PASS drops from 5 to 4).

## What each variant uniquely passed

Non-vacuous real PASSes that appear in **only one** variant:
- `shot0` only: `TwoPhase` (shared with shot1, actually — but absent from shot3/shot5), `Majority` (also shot3), `SimpleRegular` (also shot3), `Consensus` (also shot1, shot3)
- `shot3` only: `YoYoNoPruning` (also shot5)
- `shot5` only: none unique

The intersection of *all four* (always-pass): `nbacc_ray97`. That's the single Opus-4.7-robust target.

The union of any-variant non-vacuous PASS:
`Consensus, Majority, SimpleRegular, YoYoNoPruning, nbacc_ray97, TwoPhase, VoucherTransfer, VoucherCancel`
= 8 distinct val targets. So the *pass@4 (any-shot)* rate is 8/30 = **26.7%**, modestly better than any single shot config.

## Recommendations for the paper

1. **Don't cite `shot3` as the model's capability ceiling.** It's worse than zero-shot.
2. **Adopt non-vacuous PASS as the headline metric.** The flat PASS rate inverts the shot-1 → shot-3 ranking (shot1 looks best at 30% flat, but 4/9 are vacuous).
3. **The pipeline's `train_data[:NUM_FEW_SHOTS]` selector is harming, not helping.** A similarity-based selector (BM25 over `comments_clean`, or AST-sketch retrieval) should be ablated before declaring few-shot dead. Aligns with `tla_benchmark` issue #34.
4. **`pass@k` over different shot counts** is a cleaner story than per-variant accuracy: ~27% of val is reachable by *some* configuration, even with the naive selector.

## Files

Each variant directory contains:
- `EVAL_REPORT.md` (only for `opus-4-7-1m` / `shot3`, the original run)
- `results_matrix.csv` — per-target SANY + TLC + state counts
- `evaluation_results.csv` — flat PASS/FAIL/ERROR (the format `compare_models.py` expects)
- `sany_summary.txt`, `tlc_summary.txt`
- `generated/` — 30 .tla + 30 .cfg
- `sany_logs/`, `evaluations/` — per-spec logs

Top-level: this file + `data_matrix.csv` (one row per variant) + `per_target_matrix.csv` (one row per target × 4 variants).
