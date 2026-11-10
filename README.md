# Pretorsion theories and image-closed subcategories

[Website](https://haruhisa-enomoto.github.io/pretorsion-image-closed/) ·
[Paper](https://hexagonmath.org/2611.00207v1) ·
[Main theorems in Lean](PretorsionImageClosed/MainTheorems.lean) ·
[Independent statement](PretorsionImageClosed/Statement.lean) ·
[Paper correspondence](docs/PAPER-CORRESPONDENCE.md)

This repository contains a Lean 4 formalization of the paper *Pretorsion theories
and image-closed subcategories* by Haruhisa Enomoto
([hexagon:2611.00207v1](https://hexagonmath.org/2611.00207v1)), including the cited inputs that it uses. The
formalized version is identified in [MANUSCRIPT.md](docs/MANUSCRIPT.md).

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

The paper has two parts: a structural part for any finite-dimensional algebra
(Theorem A, the lattice, realizations, and the convex geometry of image closure), and
an enumerative part for the linearly oriented quiver of type A (Theorem B). Both are
formalized.

## Counting in type A

Let `Λ_n` be the path algebra of `1 → 2 → ⋯ → n`. Theorem B counts the pretorsion
theories `PT(Λ_n)` and the image-closed subcategories `L_im(Λ_n)` of `mod Λ_n`, each
weighted by `q` to the number of indecomposables (in `T ∩ F`, and in the subcategory).
The `q`-Gandhi polynomials are defined by `B_1 = C_1 = 1` and

    B_m(x, q) = Δ_q(x² B_{m-1}(x, q)),   C_m(x, q) = (1 + qx) Δ_q(x C_{m-1}(x, q)),
    Δ_q f(x) = (f(1 + qx) − f(x)) / (1 + (q − 1)x).

At `q = 1`, the counts are the positive Genocchi numbers `g_{2n+4}` and the median
Genocchi numbers `H_{2n+3}` ([OEIS A110501](https://oeis.org/A110501) and
[A005439](https://oeis.org/A005439)):

| `n` | 0 | 1 | 2 | 3 | 4 | 5 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `\|PT(Λ_n)\|` | 1 | 3 | 17 | 155 | 2073 | 38227 |
| `\|L_im(Λ_n)\|` | 1 | 2 | 8 | 56 | 608 | 9440 |

For example, `B_3(1, q) = q³ + 4q² + 7q + 5` and `C_3(1, q) = q³ + 3q² + 3q + 1` for
`n = 2`. The proof is combinatorial. Image-closed subcategories of `mod Λ_n`
correspond to families of intervals in `{1, …, n}` closed under nonempty
intersections (Theorem 5.5). Quotient-closed and submodule-closed subcategories
are recorded by cutoff vectors, and Theorem 6.5 decides, vertex by vertex, which
pairs of them form a pretorsion theory. Adjoining one vertex at a
time gives the recurrences of `B` and `C` (Theorems 7.5 and 8.5).

What Lean checks: the identities in `ℤ[q]` and their two-variable refinements, for
every `n`. The table, the evaluation at `q = 1` and the identification with Genocchi
numbers (`B_m(1,1) = g_{2m+2}`, `C_m(1,1) = H_{2m+1}`, classical results of Han and
Zeng) are not formalized; the table was recomputed from the recurrences.

## Context

Pretorsion theories were introduced by Facchini and Finocchiaro for categories
without a zero object, and developed for general categories by Facchini, Finocchiaro
and Gran. In `mod Λ`, Campanini, Fedele and Yıldırım showed that the first and second
components of pretorsion theories are exactly the quotient-closed and
submodule-closed subcategories, and Campanini and Fedele constructed pretorsion
theories whose intersection is a prescribed Serre subcategory. Theorem A determines
all possible intersections. It parallels a result of Enomoto and Sakai: the
subcategories closed under images and extensions are the intersections of a torsion
class and a torsion-free class.

The `q`-refinement follows the quotient–submodule equidistribution conjecture of
Enomoto, which counts subcategories by their number of indecomposables. The counts
link module categories of type A with Genocchi and median Genocchi numbers and the
`q`-Gandhi polynomials of Han and Zeng. Pilaud also obtained the count `H_{2n+3}` for
intersection-closed interval families. The proofs use recurrences; the paper knows
no bijection with the Genocchi permutation models of Han and Zeng that preserves the
statistics. The counts depend on the orientation of the quiver, and only the linear
orientation is treated.

The results concern two groups of readers: those working on the representation
theory of finite-dimensional algebras, in particular torsion theory and lattices of
subcategories, and those working in enumerative combinatorics on Genocchi numbers
and Gandhi polynomials. The references are listed in
[formalization.yaml](formalization.yaml).

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
