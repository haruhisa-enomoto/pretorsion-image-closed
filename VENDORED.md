# Reused Lean source

Mathlib is the only external Lake dependency. Section 4.3 of the paper (the
convex geometry of image closure) reuses code from an earlier formalization,
reorganized here by mathematical topic and connected to this library's notion of
subcategory. [`verification/module-origins.json`](verification/module-origins.json)
records the origin of every reused module. All other modules were written for this
repository.

| Origin | Modules | Licence |
| --- | --- | --- |
| [`quotient-submodule-equidistribution`](https://github.com/haruhisa-enomoto/quotient-submodule-equidistribution), commit `20ee4b9` | 14, and the `InAdd` lemmas of `IndecomposableClosures/Subcategories.lean` | Apache 2.0 |
| [Tau Ceti](https://github.com/TauCetiProject/TauCeti), development state of commit `eeb5b4b` (not a published revision), through `quotient-submodule-equidistribution` | 2 (`Modules/IndecomposableModule.lean`, `Modules/LocalRingIdempotents.lean`) | Apache 2.0, The Tau Ceti contributors |

The reused files are:

- `ConvexGeometry/`: closure operators, anti-exchange, extreme points, closed sets,
  compact closed sets, minimal generators.
- `IndecomposableClosures/`: `Skeleton`, `Presentations`, `ModuleTraces`,
  `EndomorphismRadical`, `QuotientAntiExchange`, `SubmoduleAntiExchange`,
  `SplitProjective`, `SplitInjective`, `Decomposition`: indecomposable skeletons of
  finitely generated modules, the quotient and submodule closures on sets of
  indecomposables, their anti-exchange property, and extreme points as relative
  split projectives and injectives.

Each reused file starts with a notice naming its source module; the two files from
Tau Ceti keep their copyright headers. The files were changed for the pinned Mathlib
and moved to new paths, and their declarations were placed in the
`PretorsionImageClosed` namespace. Helper lemmas that duplicated this library's own
(finite sums of morphisms, monomorphisms and epimorphisms of finitely generated
modules) were replaced by the library versions in `Modules/FiniteModules.lean`.
