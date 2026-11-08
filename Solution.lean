module

public import PretorsionImageClosed

@[expose] public section

universe u

/-- **Theorem A** (Theorem 4.4). For a subcategory `Z` of `mod Λ`, `Λ` a
finite-dimensional algebra over a field, the following are equivalent: `Z` is
image-closed; `Z = Gen Z ∩ Cogen Z`; `Z = T ∩ F` for a pretorsion theory
`(T, F)`. -/
theorem PretorsionImageClosed.Challenge.theoremA : PretorsionImageClosed.Statement.TheoremA.{u} :=
  PretorsionImageClosed.theoremA

/-- **Theorem 3.6.** The pretorsion theories of `mod Λ` form a complete lattice,
with meets (3.2), joins (3.3), least element `(0, mod Λ)` and greatest element
`(mod Λ, 0)`. -/
theorem PretorsionImageClosed.Challenge.completeLattice :
    PretorsionImageClosed.Statement.CompleteLattice.{u} :=
  PretorsionImageClosed.completeLattice

/-- **Theorem 7.5.** For the linearly oriented quiver `1 → ⋯ → n`, `PT(Λ_n)` is
finite and `∑ x^{ρ_n(T)} q^{|ind(T ∩ F)|} = B_{n+1}(x, q)`. -/
theorem PretorsionImageClosed.Challenge.gandhiPretorsion :
    PretorsionImageClosed.Statement.GandhiPretorsion.{u} :=
  PretorsionImageClosed.gandhiPretorsion

/-- **Theorem 8.5.** `L_im(Λ_n)` is finite and
`∑ x^{ρ_n(C)} q^{|ind C|} = C_{n+1}(x, q)`. -/
theorem PretorsionImageClosed.Challenge.gandhiImageClosed :
    PretorsionImageClosed.Statement.GandhiImageClosed.{u} :=
  PretorsionImageClosed.gandhiImageClosed

/-- **Theorem B**, first identity: `∑_{(T,F) ∈ PT(Λ_n)} q^{|ind(T ∩ F)|} = B_{n+1}(1, q)`. -/
theorem PretorsionImageClosed.Challenge.theoremBPretorsion :
    PretorsionImageClosed.Statement.TheoremBPretorsion.{u} :=
  PretorsionImageClosed.theoremBPretorsion

/-- **Theorem B**, second identity: `∑_{C ∈ L_im(Λ_n)} q^{|ind C|} = C_{n+1}(1, q)`. -/
theorem PretorsionImageClosed.Challenge.theoremBImageClosed :
    PretorsionImageClosed.Statement.TheoremBImageClosed.{u} :=
  PretorsionImageClosed.theoremBImageClosed
