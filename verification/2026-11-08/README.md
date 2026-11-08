# Verification record, November 8, 2026: first release

Commit `e6e95f6c295649bccf0ca476c9a5b008320e9443`. Lean `v4.35.0-rc3`, Mathlib
`c55e6e786f49471c72fbddbec5415808896aec1e`, Lean module system.

This commit follows the manuscript identified in
[docs/MANUSCRIPT.md](../../docs/MANUSCRIPT.md). The checks below ran on a fresh build
of this commit's Lean files.

## Local checks

| Check | Result |
| --- | --- |
| Lean source check | `scripts/check-lean-sources.py` passes |
| Statement sync | `scripts/generate_challenge.py --check` passes |
| Build | `lake build PretorsionImageClosed Challenge Solution`: 2,477 jobs, 48 seconds wall time with Mathlib's cache, peak memory 1.4 GB; the only `sorry`s are the six Challenge placeholders |
| Axiom audit | `scripts/audit_axioms.py`: 23 declarations, only `propext`, `Classical.choice`, `Quot.sound` |
| Declaration scan | `scripts/scan_axioms.py`: all 1,811 declarations of the library and Solution; no other axiom |
| `lake comparator` | `scripts/verify-comparator.sh` in a `bwrap` sandbox: con-ron (23,534 declarations), NanoDa and the Lean kernel accept; [`comparator-tail.log`](comparator-tail.log) |

## Hosted Palomar preflight

Run [42473438479](https://github.com/haruhisa-enomoto/pretorsion-image-closed/actions/runs/42473438479)
on commit `4690a5ee81e5dfa28fb2360c03893977cdcc7b41`, pipeline
`PalomarRegistry/PalomarSubmission@14aa8d6`, profile `palomar-standard-v1`:
`status: pass`, checked at 2026-11-08 11:01:29 UTC, 6 min 41 s for the whole
run. The Lean files, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`
and `comparator.json` are identical to commit `e6e95f6` above; the later
commits change only documentation, `formalization.yaml`, the website and the
preflight workflow.

| Phase | Time | Peak memory |
| --- | ---: | ---: |
| Mathlib cache | 51 s | 8.2 GiB |
| Solution build | 53 s | 1.3 GiB |
| Solution export | 7 s | 0.7 GiB |
| `lake comparator` (Lean kernel, NanoDa) | 32 s | 0.5 GiB |
| con-ron replay | 20 s | 0.5 GiB |

Kernels that accepted: NanoDa and con-ron (`--verified`, 23,534 declarations,
the con-ron of Lean `v4.36.0-rc1` pinned by Palomar), besides the Lean kernel.
One warning, not blocking: the Challenge (372 lines, 16,584 bytes) exceeds
Palomar's preferred review surface of 300 lines and 32 KiB. The report is
[`mechanical-report.json`](mechanical-report.json).

Earlier attempts: run 42469587697 (commit `32cf57f`) failed twice in runner
setup on HTTP 504 from GitHub release downloads; run 42473229434 (commit
`8465587`) stopped at intake because the workflow's `request_id` was not 12
characters, fixed in `4690a5e`. Palomar's metadata check also required
`classification.arxiv`, added in `608d7db`.

| File | SHA-256 |
| --- | --- |
| `Challenge.lean` | `45f28013c496a21a9422978abb6521a6897cd81a3ed08791968c2659d657c404` |
| `Solution.lean` | `f3e7deeb3fbebb984bec7ebeb3772b3ee700677ce015aeefd1825d5130917e4b` |
| `comparator.json` | `d0b326a788767b7c4f9b2c4c6c9ce0bcd0dae9484f73777d99d3a8ff5c74942d` |
| `comparator-tail.log` | `e38149eec3564a1c15a5dd37c8342725135f783d8d672a525c7e797713b92f59` |
| `mechanical-report.json` | `98126219a19ed01010aee63709a9cc984b47744ff98c0082e6937de402fa41b2` |
