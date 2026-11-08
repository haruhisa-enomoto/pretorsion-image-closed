module

public import PretorsionImageClosed.Realizations.TheoremA
public import PretorsionImageClosed.Pretorsion.FixedMiddle

/-!
# The least realization and the image closure

* **Corollary 4.7.** An image-closed subcategory `Z` has a least
  realization (`leastRealization`), obtained from the greatest realization of
  `Zᵒᵖ` in the opposite category (Construction 4.6 is the dual of
  Construction 4.3). Every pretorsion theory with intersection `Z` lies
  between the least and the greatest realization (`realization_bounds`); with
  Proposition 3.8 this makes the realizations of `Z` a complete lattice.
* **Corollary 4.9** (Auslander–Smalø, Proposition 4.3). `Gen Z ∩ Cogen Z` is
  the smallest image-closed subcategory containing `Z`
  (`isImageClosed_gen_inf_cogen`, `le_gen_inf_cogen`, `gen_inf_cogen_le`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PretorsionImageClosed.Statement

open CategoryTheory Limits Subcategory

variable {C : Type*} [Category C] [Abelian C] [HasLength C]

/-! ### `Gen` and `Cogen` in the opposite category -/

theorem gen_op (Z : Subcategory C) (X : Cᵒᵖ) : Gen Z.op X ↔ Cogen Z X.unop :=
  ⟨fun ⟨Y, hY, p, _⟩ => ⟨Y.unop, hY, p.unop, inferInstance⟩,
    fun ⟨Y, hY, i, _⟩ => ⟨Opposite.op Y, hY, i.op, inferInstance⟩⟩

theorem cogen_op (Z : Subcategory C) (X : Cᵒᵖ) : Cogen Z.op X ↔ Gen Z X.unop :=
  ⟨fun ⟨Y, hY, i, _⟩ => ⟨Y.unop, hY, i.unop, inferInstance⟩,
    fun ⟨Y, hY, p, _⟩ => ⟨Opposite.op Y, hY, p.op, inferInstance⟩⟩

/-- The opposite of an image-closed subcategory is image-closed. -/
theorem Subcategory.IsImageClosed.op {Z : Subcategory C} (hZ : Z.IsImageClosed) :
    Z.op.IsImageClosed := by
  rw [isImageClosed_iff_eq_gen_inf_cogen]
  have h := (isImageClosed_iff_eq_gen_inf_cogen Z).1 hZ
  funext X
  apply propext
  show Z.prop X.unop ↔ Gen Z.op X ∧ Cogen Z.op X
  rw [gen_op, cogen_op, h, and_comm]
  rfl

/-! ### Corollary 4.7 -/

variable (Z : Subcategory C) (hZ : Z.IsImageClosed)

/-- The least realization `(T⁻(Z), F⁺(Z))` of an image-closed subcategory (Corollary 4.7). -/
def leastRealization : PretorsionTheory C := (greatestRealization Z.op hZ.op).unop

theorem leastRealization_middle : (leastRealization Z hZ).middle = Z.prop := by
  show (greatestRealization Z.op hZ.op).unop.middle = Z.prop
  rw [PretorsionTheory.unop_middle, greatestRealization_middle]
  rfl

variable {Z}

/-- **Corollary 4.7.** Every pretorsion theory with intersection `Z` lies between the least
and the greatest realization of `Z`. -/
theorem realization_bounds (P : PretorsionTheory C) (hP : P.middle = Z.prop) :
    leastRealization Z hZ ≤ P ∧ P ≤ greatestRealization Z hZ := by
  refine ⟨?_, le_greatestRealization hZ P hP⟩
  have hP' : P.op.middle = Z.op.prop := by
    rw [PretorsionTheory.op_middle, hP]
    rfl
  have h := le_greatestRealization hZ.op P.op hP'
  rw [← PretorsionTheory.op_unop (greatestRealization Z.op hZ.op)] at h
  exact PretorsionTheory.op_LE_op_iff.1 h

/-- **Corollary 4.7**: the least realization is the least element of `PT_Z`. -/
theorem isLeast_leastRealization :
    IsLeast {P : PretorsionTheory C | P.middle = Z.prop} (leastRealization Z hZ) :=
  ⟨leastRealization_middle Z hZ, fun P hP => (realization_bounds hZ P hP).1⟩

/-- Corollary 4.5 in the form used by Corollary 4.7: the greatest realization is the greatest
element of `PT_Z`. -/
theorem isGreatest_greatestRealization :
    IsGreatest {P : PretorsionTheory C | P.middle = Z.prop} (greatestRealization Z hZ) :=
  ⟨greatestRealization_middle Z hZ, fun P hP => (realization_bounds hZ P hP).2⟩

/-! ### Corollary 4.9 -/

variable (Z)

theorem isImageClosed_gen_inf_cogen : IsImageClosed (Gen Z ⊓ Cogen Z) := by
  rintro X Y f ⟨⟨N, hN, p, hp⟩, -⟩ ⟨-, ⟨M, hM, i, hi⟩⟩
  exact ⟨⟨N, hN, p ≫ factorThruImage f, epi_comp _ _⟩, ⟨M, hM, image.ι f ≫ i, mono_comp _ _⟩⟩

theorem le_gen_inf_cogen : Z.prop ≤ Gen Z ⊓ Cogen Z := fun X hX => ⟨le_gen Z X hX, le_cogen Z X hX⟩

/-- **Corollary 4.9.** `Gen Z ∩ Cogen Z` is contained in every image-closed subcategory
containing `Z`. -/
theorem gen_inf_cogen_le {D : Subcategory C} (hD : D.IsImageClosed) (hZD : Z ≤ D) :
    Gen Z ⊓ Cogen Z ≤ D.prop := by
  rw [(isImageClosed_iff_eq_gen_inf_cogen D).1 hD]
  rintro X ⟨⟨N, hN, p, hp⟩, ⟨M, hM, i, hi⟩⟩
  exact ⟨⟨N, hZD N hN, p, hp⟩, ⟨M, hZD M hM, i, hi⟩⟩

end PretorsionImageClosed.Statement
