module

public import PretorsionImageClosed.Realizations.TheoremA
public import PretorsionImageClosed.Pretorsion.Lattice
public import PretorsionImageClosed.Length.Modules
public import PretorsionImageClosed.LinearQuiver.CutoffRestriction
public import PretorsionImageClosed.LinearQuiver.FamilyRestriction

/-!
# The main theorems for `mod Λ`

Assembly of the statements of `Statement.lean` from the library. The general
results are proved for an abelian category with a length function; here they
are specialized to the finite-dimensional modules over a finite-dimensional
algebra. The enumeration of pretorsion theories of the linear quiver
(Theorem 7.5 and the first half of Theorem B) is assembled from the cutoff
description of `PT(Λ_n)`, and the enumeration of image-closed subcategories
(Theorem 8.5 and the second half of Theorem B) from the description of
`L_im(Λ_n)` by intersection-closed interval families.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PretorsionImageClosed

open CategoryTheory Limits Statement

universe u

/-- The length function on `mod Λ` (composition length). -/
def modHasLength (k : Type u) [Field k] (Λ : Type u) [Ring Λ] [Algebra k Λ]
    [FiniteDimensional k Λ] :
    haveI := isNoetherianRing_mop k Λ
    HasLength (Mod k Λ) :=
  haveI := isNoetherianRing_mop k Λ
  haveI := isArtinianRing_mop k Λ
  inferInstance

/-- **Theorem A** (Theorem 4.4). -/
theorem theoremA : Statement.TheoremA.{u} := by
  intro k _ Λ _ _ _
  haveI := isNoetherianRing_mop k Λ
  haveI := isArtinianRing_mop k Λ
  intro Z
  exact ⟨isImageClosed_iff_eq_gen_inf_cogen Z, isImageClosed_iff_exists_pretorsionTheory Z⟩

/-- **Theorem 3.6**: `PT(Λ)` is a complete lattice, with meets (3.2), joins (3.3), least
element `(0, mod Λ)` and greatest element `(mod Λ, 0)`. -/
theorem completeLattice : Statement.CompleteLattice.{u} := by
  intro k _ Λ _ _ _
  haveI := isNoetherianRing_mop k Λ
  haveI := isArtinianRing_mop k Λ
  refine ⟨inferInstance, fun P Q => Iff.rfl, fun S _ => ⟨PretorsionTheory.sInf_T_prop S,
    PretorsionTheory.sInf_F_prop S⟩, fun S _ => ⟨PretorsionTheory.sSup_T_prop S,
    PretorsionTheory.sSup_F_prop S⟩, ?_, ?_, ?_, ?_⟩
  · rw [PretorsionTheory.bot_eq]
    rfl
  · rw [PretorsionTheory.bot_eq]
    rfl
  · rw [PretorsionTheory.top_eq]
    rfl
  · rw [PretorsionTheory.top_eq]
    rfl

/-- **Theorem 7.5**: `PT(Λ_n)` is finite and
`∑_{(T,F) ∈ PT(Λ_n)} x^{ρ_n(T)} q^{|ind(T ∩ F)|} = B_{n+1}(x, q)`. -/
theorem gandhiPretorsion : Statement.GandhiPretorsion.{u} := by
  refine ⟨⟨gandhiFirst, isGandhiFirst_gandhiFirst⟩, ?_⟩
  intro k _ n
  refine ⟨inferInstance, fun B hB => ?_⟩
  rw [LinearQuiver.finsum_pretorsionWeight]
  exact LinearQuiver.cpSum_eq hB n

/-- **Theorem B**, first half: `∑_{(T,F) ∈ PT(Λ_n)} q^{|ind(T ∩ F)|} = B_{n+1}(1, q)`. -/
theorem theoremBPretorsion : Statement.TheoremBPretorsion.{u} := by
  refine ⟨⟨gandhiFirst, isGandhiFirst_gandhiFirst⟩, ?_⟩
  intro k _ n
  refine ⟨inferInstance, fun B hB => ?_⟩
  have h := (gandhiPretorsion.{u}.2 k n).2 B hB
  rw [← h, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro P _
  simp [pretorsionWeight]

/-- **Theorem 8.5**: `L_im(Λ_n)` is finite and
`∑_{C ∈ L_im(Λ_n)} x^{ρ_n(C)} q^{|ind C|} = C_{n+1}(x, q)`. -/
theorem gandhiImageClosed : Statement.GandhiImageClosed.{u} := by
  refine ⟨⟨LinearQuiver.gandhiSecondOf, LinearQuiver.isGandhiSecond_gandhiSecondOf⟩, ?_⟩
  intro k _ n
  refine ⟨inferInstance, fun Cs hCs => ?_⟩
  rw [LinearQuiver.finsum_imageClosedWeight]
  exact (LinearQuiver.xSum_eq n).trans
    (LinearQuiver.isGandhiSecond_gandhiSecondOf.eq hCs (n + 1) (by omega))

/-- **Theorem B**, second half: `∑_{C ∈ L_im(Λ_n)} q^{|ind C|} = C_{n+1}(1, q)`. -/
theorem theoremBImageClosed : Statement.TheoremBImageClosed.{u} := by
  refine ⟨⟨LinearQuiver.gandhiSecondOf, LinearQuiver.isGandhiSecond_gandhiSecondOf⟩, ?_⟩
  intro k _ n
  refine ⟨inferInstance, fun Cs hCs => ?_⟩
  have h := (gandhiImageClosed.{u}.2 k n).2 Cs hCs
  rw [← h, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro Z _
  simp [imageClosedWeight]

end PretorsionImageClosed
