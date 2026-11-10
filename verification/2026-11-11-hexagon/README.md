# Verification record, November 11, 2026: the posted paper

Commit `da7ea8e902a2bba856c78f8af53b9c24e0dc3a06`. Lean `v4.35.0-rc3`, Mathlib
`c55e6e786f49471c72fbddbec5415808896aec1e`, Lean module system.

The paper was posted as [hexagon:2611.00207v1](https://hexagonmath.org/2611.00207v1)
on November 10, 2026. Its TeX source is byte-identical to the formalized version
(`main.tex` SHA-256 `798e9fe07db9d0c1527fb714b5947ac970fc7937b9eb791352ab6db6fad5d864`,
checked on November 11, 2026), so statement numbers and the
[correspondence](../../docs/PAPER-CORRESPONDENCE.md) are unchanged. This commit cites
it in [MANUSCRIPT.md](../../docs/MANUSCRIPT.md), `formalization.yaml`, the README and
the website.

The Lean files, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` and
`comparator.json` are identical to those of the
[first release](../2026-11-08/README.md), whose local checks therefore apply.

## Hosted Palomar preflight

Run [42842279381](https://github.com/haruhisa-enomoto/pretorsion-image-closed/actions/runs/42842279381)
on this commit, pipeline `PalomarRegistry/PalomarSubmission@14aa8d6`, profile
`palomar-standard-v1`: `status: pass`, checked at 2026-11-10 15:22:33 UTC, about
8 minutes for the whole run. NanoDa and con-ron (`--verified`, 23,534 declarations)
accept, besides the Lean kernel. One warning, not blocking: the Challenge (372
lines, 16,584 bytes) exceeds Palomar's preferred review surface of 300 lines and
32 KiB. The report is [`mechanical-report.json`](mechanical-report.json).

| File | SHA-256 |
| --- | --- |
| `Challenge.lean` | `45f28013c496a21a9422978abb6521a6897cd81a3ed08791968c2659d657c404` |
| `Solution.lean` | `f3e7deeb3fbebb984bec7ebeb3772b3ee700677ce015aeefd1825d5130917e4b` |
| `comparator.json` | `d0b326a788767b7c4f9b2c4c6c9ce0bcd0dae9484f73777d99d3a8ff5c74942d` |
| `mechanical-report.json` | `92937c95773189e0c1de6a9bcf271a692f3c2776a6ccfa391b84e7b39b5b43e8` |
