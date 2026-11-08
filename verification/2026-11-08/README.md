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

Not run yet: the workflow needs the repository on GitHub.

| File | SHA-256 |
| --- | --- |
| `Challenge.lean` | `45f28013c496a21a9422978abb6521a6897cd81a3ed08791968c2659d657c404` |
| `Solution.lean` | `f3e7deeb3fbebb984bec7ebeb3772b3ee700677ce015aeefd1825d5130917e4b` |
| `comparator.json` | `d0b326a788767b7c4f9b2c4c6c9ce0bcd0dae9484f73777d99d3a8ff5c74942d` |
| `comparator-tail.log` | `e38149eec3564a1c15a5dd37c8342725135f783d8d672a525c7e797713b92f59` |
