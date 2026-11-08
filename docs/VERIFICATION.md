# Verification

The library proves Theorem A, Theorem 3.6, Theorem B and its refinements
Theorems 7.5 and 8.5 of [the paper](MANUSCRIPT.md), and every other numbered
statement that they use; Section 4.3 is proved as well. The
[correspondence](PAPER-CORRESPONDENCE.md) lists the declarations. Records are in
[`verification/`](../verification/README.md).

## Independent statement

`PretorsionImageClosed/Statement.lean` states the results with Mathlib alone:
pretorsion theories with `Z`-trivial morphisms, prekernels and precokernels
(Definition 2.2); subcategories closed under isomorphisms, finite direct sums and
direct summands; `Gen`, `Cogen` and image-closed subcategories; `mod Λ` as finitely
generated modules over `Λᵐᵒᵖ`; representations of `1 → 2 → ⋯ → n` as functors from
`Fin n`; the number of isomorphism classes of indecomposable objects; and the
`q`-Gandhi polynomials through the relation defining `Δ_q`. `Challenge.lean` is
generated from it with six deliberate `sorry` placeholders. `Solution.lean` proves
them and does not import the Challenge.

## Results

The [record of November 8, 2026](../verification/2026-11-08/README.md) gives the
local results and the hashes. A hosted Palomar preflight needs the repository on
GitHub and has not been run yet.

No human expert has reviewed the Lean statements or the proofs. Lean checks the
proofs; whether `Challenge.lean` says what the paper says is a human judgement.

## Reproduce the checks

```sh
python3 scripts/check-lean-sources.py
lake exe cache get
lake build
python3 scripts/audit_axioms.py
python3 scripts/scan_axioms.py
python3 scripts/generate_challenge.py --check
lake build Challenge Solution
./scripts/verify-comparator.sh
```

With Mathlib's cache in place, the library builds in about one minute on 20 hardware
threads; each Lean process stays below 1.5 GB.

`audit_axioms.py` and `scan_axioms.py` generate non-module Lean files, because a
`module` file sees theorems without their proofs. `verify-comparator.sh` follows the
Palomar template: it runs the `lake comparator` bundled with the toolchain, with the
Lean kernel and the bundled NanoDa and con-ron checkers, inside a `bwrap`
(bubblewrap) sandbox. `bwrap` must be on the path, and `.lake/packages` must be a real
directory, not a symlink.

The workflow [Palomar preflight](../.github/workflows/palomar-preflight.yml) runs
Palomar's mechanical verification for a chosen commit.
