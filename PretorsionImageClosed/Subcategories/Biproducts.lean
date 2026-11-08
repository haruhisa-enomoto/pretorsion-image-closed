module

public import PretorsionImageClosed.Subcategories.Basic
public import PretorsionImageClosed.Biproducts.Basic

/-!
# Finite biproducts in subcategories

A subcategory (closed under binary biproducts, direct summands and zero
objects) is closed under all finite biproducts (`Subcategory.prop_biproduct`),
by induction with `biproductFinSuccIso`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PretorsionImageClosed

open CategoryTheory Limits

variable {C : Type*} [Category C] [Preadditive C] [HasFiniteBiproducts C] [HasBinaryBiproducts C]

namespace Statement.Subcategory

variable (Z : Subcategory C)

theorem prop_biproduct_fin : ∀ {n : ℕ} (f : Fin n → C), (∀ j, Z.prop (f j)) → Z.prop (⨁ f)
  | 0, f, _ => Z.prop_of_isZero (by
      rw [IsZero.iff_id_eq_zero]
      apply biproduct.hom_ext'
      intro j
      exact j.elim0)
  | n + 1, f, h => Z.prop_of_iso (biproductFinSuccIso f).symm
      (Z.prop_biprod (h 0) (prop_biproduct_fin _ fun j => h j.succ))

/-- A subcategory is closed under finite biproducts. -/
theorem prop_biproduct {J : Type*} [Fintype J] (f : J → C) (h : ∀ j, Z.prop (f j)) :
    Z.prop (⨁ f) := by
  classical
  let e : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  refine Z.prop_of_iso (biproduct.whiskerEquiv e.symm (fun j => Iso.refl _)) ?_
  exact Z.prop_biproduct_fin _ fun j => h _

end Statement.Subcategory

end PretorsionImageClosed
