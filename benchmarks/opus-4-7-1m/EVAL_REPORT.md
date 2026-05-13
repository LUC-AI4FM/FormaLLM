# Opus 4.7 (1M context) — FormaLLM TLA+ Spec Generation Eval

**Date:** 2026-05-11
**Model:** `claude-opus-4-7[1m]`
**Validation set:** `outputs/val.json` (30 specs)
**Few-shot pool:** first 3 entries of `outputs/train.json` (Stones, KeyValueStore, ZSequences)
**Generation method:** the model produced each .tla directly (no API roundtrip — the subagent IS the model under evaluation)
**Tools:** SANY 2.2 + TLC2 Version 2026.04.22.172729, `tla2tools.jar` at `/Users/eric/GitHub/tla_benchmark/tla2tools.jar`

## Headline numbers

| Metric | Count | % |
|---|---|---|
| Total val targets | 30 | 100% |
| SANY parsed cleanly | 18 | 60.0% |
| TLC PASS (real) | 5 | 16.7% |
| TLC PASS (vacuous — 0 initial states) | 3 | 10.0% |
| TLC FAIL (real invariant violation) | 5 | 16.7% |
| TLC ERROR | 17 | 56.7% |
| of which: stub (null comments — skipped per spec) | 4 | 13.3% |

**Combined success rate (PASS / Total) = 26.67%** (matches `outputs/model_comparison.csv`)
**Non-vacuous success rate = 16.67%** (5/30)

## What passed honestly

| Spec | Distinct states checked | Note |
|---|---|---|
| Consensus | 4 | small spec, full state space |
| Majority | 789 | non-trivial |
| SimpleRegular | 277,726 | substantial |
| YoYoNoPruning | 14 | small but real |
| nbacc_ray97 | 2,804 | non-trivial Byzantine-NB-AC spec |

## What passed vacuously (model generated valid TLA+ but cfg/spec admitted no initial states)

- ClientCentric, Relation, TLAPS

## What failed model-checking (spec parsed; invariant violated)

- MCDieHarder — `NotSolved` (i.e., the spec encoded the puzzle but didn't reach the goal state)
- Hanoi — `NotSolved`
- VoucherTransfer / VoucherCancel — `VTPConsistent` (consistency invariant violated)
- EnvironmentController — `TypeOK` (type invariant violated — implementation bug in the action operators)

## What errored

Breakdown by reason:
- **stub_skipped (4):** MCChangRoberts, MCLeastCircularSubstring, MCQuicksort, Prob — `val.json` records `comments_clean: null`, so per the task spec the subagent wrote `\* SKIPPED` stubs.
- **community_module_missing (3):** BufferedRandomAccessFile (RandomAccessFile), EWD687a_anim (SVG, IOUtils), EWD998ChanID_export (IOUtils, Json) — not in the FormaLLM dataset.
- **bad_cfg_syntax (4):** HDiskSynod, Alternate, MultiPaxos, BinarySearch — Opus generated cfg files with invalid grammar.
- **cfg_missing_constant / cfg_substitution_error (2):** TwoPhase, MCConsensus — cfg referenced names not declared in the spec.
- **semantic_error / undefined_operator (4):** MCEWD687a, MultiPaxos_MC, KVsnap, MajorityProof — Opus used operators it didn't define (e.g., `Transpose`).

## Per-spec table

See `results_matrix.csv` for the full per-target breakdown (SANY, TLC, state counts, error reason).

## Observations

1. **Configuration files are a clear weak spot.** When ground-truth `.cfg` exists in `val.json` (17 of 26 non-stub targets), Opus correctly copies it. For the 9 it had to invent, 4 had grammar errors and 2 used undeclared names. The cfg generator is more brittle than the .tla generator.
2. **The 5 non-vacuous PASS rate matches small-to-medium spec complexity.** Largest real pass is SimpleRegular (~278K states). MultiPaxos / fastpaxos-class specs are too long-tail for one-shot generation here.
3. **Type-invariant violations on `EnvironmentController`** suggest the model's action operators were written without keeping the variable-type domain in sync — a classic mistake also seen in human-written TLA+ first drafts.
4. **The 3 community-module dependencies (RandomAccessFile, SVG/IOUtils, Json)** point at a dataset gap, not a model failure — the dataset doesn't ship these so the generated specs can't possibly resolve them.
