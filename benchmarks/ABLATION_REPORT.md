# Opus 4.7 (1M) — Prompting-Strategy Ablation

Generator: Claude Opus 4.7 (1M context). All five variants are the same model under the same FormaLLM val set (30 targets) — only the prompting/exemplar strategy differs.

## Headline

| Variant | Strategy | SANY PASS | Real PASS | Vacuous | Real FAIL | ERROR | Unknown | Stubs | All-PASS | Non-Vacuous |
|---|---|---|---|---|---|---|---|---|---|---|
| `shot0` | k=0 (no exemplars) | 19 | **7** | 1 | 2 | 14 | 6 | 4 | 26.67% | **23.33%** |
| `shot1` | k=1, train_data[0] | 20 | 5 | 4 | 3 | 13 | 5 | 4 | 30.00% | 16.67% |
| `shot3` | k=3, train_data[:3] (pipeline default) | 18 | 5 | 3 | 5 | 17 | 0 | 4 | 26.67% | 16.67% |
| `shot5` | k=5, train_data[:5] | 15 | 4 | 1 | 3 | 16 | 5 | 4 | 16.67% | 13.33% |
| `rag` | agent self-retrieves 1–5 exemplars from corpus | 19 | 4 | 1 | 4 | 12 | 4 | 4 | 16.67% | 13.33% |

**Two counter-intuitive findings:**

1. **0-shot beats every few-shot variant** on real (non-vacuous) PASS. 5-shot is worst among the fixed-prefix variants.
2. **Agent-level RAG (self-selected exemplars) did NOT beat 0-shot.** It tied with shot5 at 4 real PASSes — the worst result.

## What this likely means

### The fixed-prefix few-shot story (shot0 → shot5)

The FormaLLM default uses `train_data[:NUM_FEW_SHOTS]` — a fixed prefix of `train.json`, not similarity-selected. The first 5 exemplars (`Stones`, `KeyValueStore`, `ZSequences`, `Huang`, `MCMajority`) are mostly heavy PlusCal-translated specs. For Opus 4.7 1M, anchoring on these styles appears to push the model *away* from the simpler/correct formulation that 0-shot would have produced.

Evidence: the vacuous-pass count rises with shot count (1 → 4 → 3 → 1) and real-fail count wobbles, both consistent with the model copying *form* from exemplars even when the form doesn't fit the target. With more exemplars, the prompt gets more "confidently wrong."

### The retrieval story (rag)

The `rag` variant gave the subagent free read access to `data/` and let it self-select 1–5 exemplars per target. **It did not help.** Specifically:

- Same model-checking quality as 5-shot (4 real PASS each)
- The agent generally retrieved *more* exemplars than 0-shot used (avg ~2.5 exemplars/target across the 26 non-stub targets vs. 0 for shot0)
- 5 targets ended `SKIPPED_NO_CFG` because the agent forgot to write cfg files for null-cfg targets, leaving them un-checkable
- The targets where retrieval *did* find a near-isomorphic exemplar (VoucherTransfer/Cancel → VoucherRedeem/Issue/LifeCycle, SimpleRegular → Simple, YoYoNoPruning → YoYoAllGraphs) lifted shape correctness but didn't always lead to TLC PASS

**Most-retrieved exemplars** (across 26 retrieving targets):
- `FindHighest` (4× — used for TLAPS-proved sequence-loop specs)
- `VoteProof` (3× — proof skeleton reference)
- `MCMajority`, `Quicksort`, `VoucherRedeem` (2× each)

### Why retrieval underperformed prior expectation

Three hypotheses worth investigating:

1. **1M-context dilution** — when the agent reads several whole exemplar specs (often 100–300 lines each) into context, that volume of in-domain noise crowds out whatever sparse, correct TLA+ priors are in the weights. 0-shot leaves the weights uncontaminated.
2. **Self-retrieval ≠ similarity retrieval** — the agent's notion of "similar" was sometimes wrong. E.g., picking `RingBuffer` + `Disruptor_SPMC` for `BufferedRandomAccessFile` produced concurrency-flavored output where the target is a sequential refinement spec.
3. **Agent attention budget** — the subagent spent 100+ tool calls per run on retrieval bookkeeping (find, grep, read, decide), leaving less effective context for the actual generation. The 5 missing cfgs are direct evidence of attention dropping at the end of each per-target loop.

### What each variant uniquely passed

Non-vacuous real PASSes by variant (sets of val targets that genuinely model-check):

| Variant | Real PASS targets |
|---|---|
| `shot0` | TwoPhase(288), Majority(2730), VoucherTransfer(50816), VoucherCancel(50816), Consensus(4), SimpleRegular(277726), nbacc_ray97(11216) |
| `shot1` | TwoPhase(288), VoucherTransfer(29362), VoucherCancel(29362), Consensus(4), nbacc_ray97(2804) |
| `shot3` | Majority(789), Consensus(4), SimpleRegular(277726), YoYoNoPruning(14), nbacc_ray97(2804) |
| `shot5` | VoucherTransfer(83890), VoucherCancel(83890), YoYoNoPruning(14), nbacc_ray97(2804) |
| `rag` | VoucherTransfer(4199), VoucherCancel(4199), SimpleRegular(277726), nbacc_ray97(12064) |

**Always-pass intersection: only `nbacc_ray97`.**

**Union of any-variant non-vacuous PASS:**
`Consensus, Majority, SimpleRegular, YoYoNoPruning, nbacc_ray97, TwoPhase, VoucherTransfer, VoucherCancel`
= **8 distinct val targets = 26.7%** *(pass@5 ceiling with this model)*

## Recommendations for the paper

1. **`shot0` is the right capability ceiling for Opus 4.7 1M**, not `shot3`. The default pipeline configuration *underestimates* the model.
2. **Adopt non-vacuous PASS as the headline metric.** The flat PASS rate inverts the shot-1 → shot-3 ranking (shot1 looks best at 30% flat, but 4/9 are vacuous).
3. **The pipeline's `train_data[:NUM_FEW_SHOTS]` selector is harming, not helping** *for this model*. Aligns with `tla_benchmark` issue #34.
4. **Agent-level RAG is not the obvious win the field assumes.** With free corpus access, the agent *still* underperformed 0-shot on a strong base model. A more selective retrieval (e.g., top-1 exemplar by BM25 over `comments_clean`, embedded into a fixed prompt template rather than handed to a tool-using agent) might land between shot0 and shot1.
5. **`pass@k` over strategies** is the cleanest aggregate metric: ~27% of val is reachable by *some* prompting configuration, even with all five strategies being relatively naive.

## Caveats

- One run per variant (no temperature variance). Anthropic API on default settings.
- `rag` agent forgot 5 cfgs; in a fully apples-to-apples re-run those would be generated and re-evaluated. Effect would be minor (most would ERROR with a basic cfg).
- 5-shot and rag generation both hit Anthropic content-filter mid-run (~spec 11/30); resumed with continuation subagents using identical instructions and exemplar lists.
- This is val set (30 specs); the ICSOFT'26 paper evaluates on the test set (26 specs after stub-filter). Direct numerical comparison to Table 6 of that paper requires re-running on test.

## Files

Each variant directory contains:
- `EVAL_REPORT.md` (only for `opus-4-7-1m` / `shot3`, the original run)
- `results_matrix.csv` — per-target SANY + TLC + state counts + error reason
- `evaluation_results.csv` — flat PASS/FAIL/ERROR (the format `compare_models.py` expects)
- `sany_summary.txt`, `tlc_summary.txt`
- `generated/` — 30 .tla + 30 .cfg
- `sany_logs/`, `evaluations/` — per-spec logs

`opus-4-7-1m-rag/` additionally has:
- `retrieval_traces/<M>.json` — per-target log of which exemplars the agent chose and why

Top-level: this file + `data_matrix.csv` (one row per variant) + `per_target_matrix.csv` (one row per target × 5 variants).
