# Pretorsion theories and image-closed subcategories

[Website](https://haruhisa-enomoto.github.io/pretorsion-image-closed/) ·
[Main theorems in Lean](PretorsionImageClosed/MainTheorems.lean) ·
[Independent statement](PretorsionImageClosed/Statement.lean) ·
[Paper correspondence](docs/PAPER-CORRESPONDENCE.md)

This repository contains a Lean 4 formalization of the paper *Pretorsion theories
and image-closed subcategories* by Haruhisa Enomoto, including the cited inputs that
it uses. The formalized version is identified in [MANUSCRIPT.md](docs/MANUSCRIPT.md).

Let `Λ` be a finite-dimensional algebra over a field `k`, and `mod Λ` its category of
finite-dimensional right modules. A *pretorsion theory* `(T, F)` generalizes a torsion
pair: morphisms from `T` to `F` factor through `Z = T ∩ F`, and every module `X` sits
in a sequence `T' → X → F'` that is exact up to morphisms factoring through `Z`. A
subcategory is *image-closed* if it contains the image of every morphism between its
objects.

**Theorem A.** For a subcategory `Z` of `mod Λ`, the following are equivalent: `Z` is
image-closed; `Z = Gen Z ∩ Cogen Z`; `Z = T ∩ F` for a pretorsion theory `(T, F)`.

**Theorem 3.6.** The pretorsion theories of `mod Λ`, ordered by `(T, F) ≤ (T', F')`
iff `T ⊆ T'` and `F ⊇ F'`, form a complete lattice, with explicit meets and joins.

**Theorem B.** For the linearly oriented quiver `1 → 2 → ⋯ → n`,

    ∑_{(T,F) ∈ PT(Λ_n)} q^{|ind(T ∩ F)|} = B_{n+1}(1, q),
    ∑_{Z ∈ L_im(Λ_n)} q^{|ind Z|} = C_{n+1}(1, q),

where `B_m` and `C_m` are the `q`-Gandhi polynomials of Han and Zeng. Theorems 7.5
and 8.5 refine these identities by a second variable `x`.

## Start reading

- [Main theorems](PretorsionImageClosed/MainTheorems.lean): `theoremA`,
  `completeLattice`, `gandhiPretorsion`, `gandhiImageClosed`, `theoremBPretorsion`
  and `theoremBImageClosed`.
- [Independent statement](PretorsionImageClosed/Statement.lean): the results stated
  with Mathlib alone. The [Challenge](Challenge.lean) is generated from it, and
  [Solution](Solution.lean) proves it.
- [Paper correspondence](docs/PAPER-CORRESPONDENCE.md): every numbered statement of
  the paper with its Lean declarations.
- [Proof notes](docs/proofs/README.md): the arguments that differ from the paper.

All definitions and proofs are complete. The main statements depend only on the
axioms `propext`, `Classical.choice` and `Quot.sound`. Every numbered statement of
the paper is covered, including the convex geometry of image closure (Section 4.3),
which is proved but not part of the compared statement. The cited inputs are proved:
the closure properties of pretorsion theories, the reconstruction formulas, the
properties of traces and rejects, the image closure of Auslander and Smalø, the
anti-exchange property of quotient and submodule closure, and the needed facts on
convex geometries. The specializations of the Gandhi polynomials to Genocchi and
median Genocchi numbers are classical and not formalized.

No human expert has reviewed the Lean statements or these proofs. Lean checks the
proofs; whether [Challenge.lean](Challenge.lean) says what the paper says is a human
judgement.

## Layout

The library is organized by subject under `PretorsionImageClosed/`.

| Directory | Content |
| --- | --- |
| `Statement`, `MainTheorems` | the statements, and the proofs of the main theorems |
| `Length` | length functions on abelian categories; `mod Λ` and quiver representations |
| `Subobjects`, `Biproducts`, `Modules` | preimages and quotients of subobjects; splittings of biproducts; finitely generated and indecomposable modules |
| `Subcategories` | subcategories, closure conditions, trace and reject |
| `Pretorsion` | pretorsion theories: the trace–reject criterion, the realization criterion, partners of a fixed component, duality, the complete lattice, fixed intersections, torsion pairs |
| `Realizations` | Theorem A, the greatest and least realizations, image closure |
| `ConvexGeometry`, `IndecomposableClosures` | closure operators and convex geometries; quotient, submodule and image closure on indecomposable modules (Section 4.3) |
| `LinearQuiver` | representations of `1 → ⋯ → n`: intervals, decompositions, image-closed subcategories, cutoff coordinates, restriction and extension |
| `Gandhi` | the operator `Δ_q`, the Gandhi polynomials, and the column sums of the enumeration |

Conventions follow the paper. Modules are finite-dimensional right modules,
formalized as finitely generated modules over `Λᵐᵒᵖ`. A subcategory is closed under
isomorphisms, finite direct sums and direct summands. `mod Λ_n` is the category of
functors from the linear order `Fin n` to finite-dimensional vector spaces. All types
live in one universe.

## Build and verify

Lean is pinned to `v4.35.0-rc3` and Mathlib to its `v4.35.0-rc3` tag, commit
`c55e6e786f49471c72fbddbec5415808896aec1e`, the only external dependency. Every Lean
file uses the Lean module system.

```sh
lake exe cache get
lake build
python3 scripts/audit_axioms.py
python3 scripts/scan_axioms.py
```

The statement check uses the `lake comparator` shipped with the toolchain, with the
Lean kernel and the bundled NanoDa and con-ron checkers. It needs `bwrap`
(bubblewrap) on the path, and `.lake/packages` must be a real directory:

```sh
python3 scripts/check-lean-sources.py
./scripts/verify-comparator.sh
```

[docs/VERIFICATION.md](docs/VERIFICATION.md) describes the checks, and the records
are in [verification](verification/README.md).

## Palomar

The repository follows the layout of the
[Palomar registry](https://palomar-registry.org): the statement of record is
[Challenge.lean](Challenge.lean), proved in [Solution.lean](Solution.lean), with
[comparator.json](comparator.json) and the metadata in
[formalization.yaml](formalization.yaml). The workflow
[Palomar preflight](.github/workflows/palomar-preflight.yml) runs Palomar's
mechanical verification for a chosen commit.

## Website

The website presents the theorems, the independent statement, a proof guide, a
library overview and the searchable Lean API. See
[website/README.md](website/README.md) for building and publishing it.

## Provenance

See [PROVENANCE.md](PROVENANCE.md) for the sources of the paper and the Lean files,
and [VENDORED.md](VENDORED.md) for reused code. Licensed under the
[Apache License 2.0](LICENSE).
