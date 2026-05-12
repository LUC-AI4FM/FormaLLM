#!/usr/bin/env python3
"""Build per_target_matrix.csv from all benchmarks/<variant>/results_matrix.csv files."""
import csv, sys
from pathlib import Path

ROOT = Path("/Users/eric/GitHub/FormaLLM/benchmarks")
val_models = ["MCDieHarder","ClientCentric","HDiskSynod","Alternate","Hanoi","Relation",
    "MCEWD687a","EWD998ChanID_export","EWD687a_anim","MCChangRoberts","TwoPhase","MCConsensus",
    "MCLeastCircularSubstring","Majority","MCQuicksort","VoucherTransfer","EnvironmentController",
    "MultiPaxos_MC","VoucherCancel","Consensus","MultiPaxos","BinarySearch","SimpleRegular",
    "BufferedRandomAccessFile","KVsnap","Prob","MajorityProof","YoYoNoPruning","nbacc_ray97","TLAPS"]

variants = ["opus-4-7-1m-shot0", "opus-4-7-1m-shot1", "opus-4-7-1m", "opus-4-7-1m-shot5"]
variant_labels = {"opus-4-7-1m-shot0":"shot0", "opus-4-7-1m-shot1":"shot1",
                  "opus-4-7-1m":"shot3", "opus-4-7-1m-shot5":"shot5"}

all_rows = {}
for variant in variants:
    csv_path = ROOT / variant / "results_matrix.csv"
    if not csv_path.exists():
        continue
    with csv_path.open() as f:
        reader = csv.DictReader(f)
        for row in reader:
            m = row["Model"]
            label = variant_labels[variant]
            all_rows.setdefault(m, {})[f"{label}_SANY"] = row["SANY"].replace("SANY_","") if row["SANY"] else ""
            tlc = row["TLC"]
            distinct = row["Distinct_States"]
            if tlc == "PASS" and distinct in ("","0"):
                tlc = "PASS_VACUOUS"
            all_rows.setdefault(m, {})[f"{label}_TLC"] = tlc

# Write
out = ROOT / "per_target_matrix.csv"
fields = ["Target"]
for label in ["shot0","shot1","shot3","shot5"]:
    fields.append(f"{label}_SANY")
    fields.append(f"{label}_TLC")

with out.open("w", newline="") as f:
    w = csv.writer(f)
    w.writerow(fields)
    for m in val_models:
        row = [m]
        for label in ["shot0","shot1","shot3","shot5"]:
            row.append(all_rows.get(m, {}).get(f"{label}_SANY", ""))
            row.append(all_rows.get(m, {}).get(f"{label}_TLC", ""))
        w.writerow(row)

print(f"Wrote: {out}")
