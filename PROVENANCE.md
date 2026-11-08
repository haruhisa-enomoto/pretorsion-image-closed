# Provenance

The Lean development is maintained by Haruhisa Enomoto. It formalizes
*Pretorsion theories and image-closed subcategories* by Haruhisa Enomoto,
following the version identified in [docs/MANUSCRIPT.md](docs/MANUSCRIPT.md). The
[correspondence](docs/PAPER-CORRESPONDENCE.md) describes formal coverage.

## Contributions

According to the paper's statement on AI use, the research was done under the
author's direction using GPT-5.6-Sol, which found and developed most of the results
and proofs; GPT-6-Astra contributed further results and checked the mathematics; and
the manuscript was drafted and revised with GPT-6-Astra, Claude Opus 5.5 and
Gemini 4 Argon.

The formalization was developed by AI coding agents (Claude Code with Claude Fable 5.1
and Claude Opus 5.5) under Haruhisa Enomoto's direction, in November 2026. This
includes the proofs that differ from the paper, described in
[docs/proofs](docs/proofs/README.md). Section 4.3 reuses an earlier formalization; see
[VENDORED.md](VENDORED.md).

## Dependencies and licences

The package pins Lean 4.35.0-rc3 and Mathlib commit
`c55e6e786f49471c72fbddbec5415808896aec1e` (tag `v4.35.0-rc3`). Mathlib is the only
external Lake dependency. This repository is released under the
[Apache License 2.0](LICENSE).
