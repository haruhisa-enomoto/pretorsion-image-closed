# Arguments that differ from the paper

The library proves every numbered statement it needs, but some proofs take a
different route from the paper. None of them changes a statement.

## A general setting for Sections 2–4

Sections 2–4 are proved for an abelian category with a *length function*: a number
attached to each object that vanishes exactly on zero objects and strictly decreases
along monomorphisms and epimorphisms that are not isomorphisms
(`Length/Basic.lean`). Finite-dimensional modules over a finite-dimensional algebra
and representations of the linear quiver are instances. Lemma 2.9 (sums and
intersections of submodules are finite) is replaced by the existence of maximal and
minimal subobjects in any nonempty set of subobjects. The trace `t_T(X)` is the
largest subobject of `X` in `T`, and the reject `r_F(X)` the smallest subobject with
quotient in `F`; their descriptions as sums of images and intersections of kernels
are `trace_le_iff` and `le_reject_iff`.

## Proposition 3.2: one reject at a time

Let `(T, F₁)` and `(T, F₂)` be pretorsion theories. The paper proves that
`(T, F₁ ∩ F₂)` is a pretorsion theory by dividing `X` by the sum `r₁(X) + r₂(X)` of
the two rejects, using Lemma 3.1 and the transport (3.1). The library divides by one
reject at a time. If `r₁(X) ≠ 0`, put `V = X / r₁(X)`; it is shorter than `X`, so
`(T, F₁ ∩ F₂)` has a short preexact sequence at `V` by induction. The trace–reject
condition for `(T, F₁)` at `X` gives `t(V) = t(X)/r₁(X)`, and every morphism from
`t(X)` to an object of `F₁ ∩ F₂` vanishes on `r₁(X) = r₁(t(X))`. Under these
conditions a short preexact sequence of `V` lifts to `t(X) → X → V → F`
(`IsShortPreexact.of_quotient`, `Pretorsion/Lifting.lean`). Lemma 3.1 is not needed.
For an arbitrary family, a finite subfamily with maximal reject at `X` and at `t(X)`
determines both rejects (`exists_reject_finInf_eq`).

## Lemma 3.3 and Proposition 3.5 through Lemma 3.7

Lemma 3.3 and Proposition 3.5 are deduced from the realization criterion
(Lemma 3.7), as in the paper's proof of Proposition 3.8, instead of through the
diagram arguments of the paper.

## Duality

The join formula (3.3), Corollary 4.7 and the join half of Proposition 3.8 use the
opposite category instead of the duality `Hom_k(-, k)`: `(T, F)` is a pretorsion
theory in `C` exactly when `(Fᵒᵖ, Tᵒᵖ)` is one in `Cᵒᵖ`, and the length function
passes to `Cᵒᵖ` (`Pretorsion/Duality.lean`).

## Representations of the linear quiver

`mod Λ_n` is the category of functors from the linear order `Fin n` to
finite-dimensional vector spaces. Every representation is shown directly to be an
iterated direct sum of interval representations, by splitting off the interval
through a vector at the first nonzero vertex (`LinearQuiver/Decomposition.lean`).
Uniqueness of the decomposition is not needed: a subcategory is determined by the
intervals it contains, because an interval that is a retract of a direct sum is a
retract of one summand (`LinearQuiver/IntervalSets.lean`).

## The enumeration

The column sums of Lemma 7.3 and equation (8.5) are computed by induction on the set
of candidate rows, adding the largest row at each step (`Gandhi/ColumnSum.lean`),
instead of through the binomial double sums (7.10)–(7.11) and (8.6). The Gandhi
polynomials are characterized by the relation `g · (1 + (q - 1)x) = f(1 + qx) - f(x)`
for `g = Δ_q f`, which determines `g` because `ℤ[q][x]` is a domain.

## Section 4.3

Section 4.3 is proved for an indecomposable skeleton of `mod Λ`, with code adapted
from the author's equidistribution formalization ([VENDORED.md](../../VENDORED.md)).
The anti-exchange property of quotient and submodule closure, which the paper cites,
is proved there with traces, rejects and the nilpotent Jacobson radical of the
endomorphism ring of an indecomposable module.
