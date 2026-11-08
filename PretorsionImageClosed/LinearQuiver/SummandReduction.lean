module

public import PretorsionImageClosed.LinearQuiver.Subobjects

/-!
# Reduction to a single summand (Lemma 5.3)

If an interval representation is a quotient of a direct sum `Y₁ ⊞ Y₂`, it is a
quotient of `Y₁` or of `Y₂`; dually for subobjects. The proof uses that the
subobjects of an interval are totally ordered: the image of
`biprod.desc f g` is the sum of the images of `f` and `g`, hence the larger of
the two, and the kernel of `biprod.lift f g` is the intersection of the
kernels, hence the smaller of the two.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PretorsionImageClosed

open CategoryTheory Limits Statement

/-! ### Images of `desc` and kernels of `lift` in an abelian category -/

section Abelian

variable {C : Type*} [Category C] [Abelian C]

theorem sumSubobject_eq_right_of_le {X : C} {S S' : Subobject X} (h : S ≤ S') :
    sumSubobject S S' = S' := by
  apply le_antisymm
  · exact imageSubobject_le _ (biprod.desc (Subobject.ofLE S S' h) (𝟙 _)) (by
      apply biprod.hom_ext'
      · rw [biprod.inl_desc_assoc, Subobject.ofLE_arrow, biprod.inl_desc]
      · rw [biprod.inr_desc_assoc, Category.id_comp, biprod.inr_desc])
  · exact le_sumSubobject_right S S'

theorem sumSubobject_eq_left_of_le {X : C} {S S' : Subobject X} (h : S' ≤ S) :
    sumSubobject S S' = S := by
  apply le_antisymm
  · exact imageSubobject_le _ (biprod.desc (𝟙 _) (Subobject.ofLE S' S h)) (by
      apply biprod.hom_ext'
      · rw [biprod.inl_desc_assoc, Category.id_comp, biprod.inl_desc]
      · rw [biprod.inr_desc_assoc, Subobject.ofLE_arrow, biprod.inr_desc])
  · exact le_sumSubobject_left S S'

/-- The image of `biprod.desc f g` is the sum of the images of `f` and `g`. -/
theorem imageSubobject_biprod_desc {Y₁ Y₂ X : C} (f : Y₁ ⟶ X) (g : Y₂ ⟶ X) :
    imageSubobject (biprod.desc f g) = sumSubobject (imageSubobject f) (imageSubobject g) := by
  have hfac : biprod.desc f g = biprod.map (factorThruImageSubobject f) (factorThruImageSubobject g) ≫
      biprod.desc (imageSubobject f).arrow (imageSubobject g).arrow := by
    apply biprod.hom_ext'
    · simp only [biprod.inl_map_assoc, biprod.inl_desc, imageSubobject_arrow_comp]
    · simp only [biprod.inr_map_assoc, biprod.inr_desc, imageSubobject_arrow_comp]
  rw [hfac, imageSubobject_epi_comp]
  rfl

/-- The kernel of `biprod.lift f g` is the intersection of the kernels. -/
theorem kernelSubobject_biprod_lift {X Y₁ Y₂ : C} (f : X ⟶ Y₁) (g : X ⟶ Y₂) :
    kernelSubobject (biprod.lift f g) = kernelSubobject f ⊓ kernelSubobject g := by
  apply le_antisymm
  · apply le_inf
    · refine le_kernelSubobject _ _ ?_
      have h : (kernelSubobject (biprod.lift f g)).arrow ≫ f =
          ((kernelSubobject (biprod.lift f g)).arrow ≫ biprod.lift f g) ≫ biprod.fst := by
        rw [Category.assoc, biprod.lift_fst]
      rw [h, kernelSubobject_arrow_comp, zero_comp]
    · refine le_kernelSubobject _ _ ?_
      have h : (kernelSubobject (biprod.lift f g)).arrow ≫ g =
          ((kernelSubobject (biprod.lift f g)).arrow ≫ biprod.lift f g) ≫ biprod.snd := by
        rw [Category.assoc, biprod.lift_snd]
      rw [h, kernelSubobject_arrow_comp, zero_comp]
  · exact le_kernelSubobject _ _ (by
      apply biprod.hom_ext
      · rw [Category.assoc, biprod.lift_fst, zero_comp,
          ← Subobject.factorThru_arrow _ _ (Subobject.inf_arrow_factors_left _ _), Category.assoc,
          kernelSubobject_arrow_comp, comp_zero]
      · rw [Category.assoc, biprod.lift_snd, zero_comp,
          ← Subobject.factorThru_arrow _ _ (Subobject.inf_arrow_factors_right _ _), Category.assoc,
          kernelSubobject_arrow_comp, comp_zero])

theorem mono_of_kernelSubobject_eq_bot {X Y : C} (f : X ⟶ Y) (h : kernelSubobject f = ⊥) : Mono f :=
  Abelian.mono_of_kernel_ι_eq_zero _ (Subobject.mk_eq_bot_iff_zero.1 h)

theorem kernelSubobject_eq_bot_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] : kernelSubobject f = ⊥ :=
  Subobject.mk_eq_bot_iff_zero.2 (kernel.ι_of_mono f)

end Abelian

namespace LinearQuiver

universe u

variable {k : Type u} [Field k] {n : ℕ}

/-- Subobjects of an interval are totally ordered. -/
theorem subobject_le_or_le {a d : Fin n} (K K' : Subobject (interval k a d)) : K ≤ K' ∨ K' ≤ K := by
  rcases eq_bot_or_eq_suffix K with rfl | ⟨ℓ, hal, -, rfl⟩
  · exact Or.inl bot_le
  rcases eq_bot_or_eq_suffix K' with rfl | ⟨ℓ', hal', -, rfl⟩
  · exact Or.inr bot_le
  exact suffix_le_or_le hal hal'

/-- Lemma 5.3(1): if `M_{a,d}` is a quotient of `Y₁ ⊞ Y₂`, it is a quotient of `Y₁` or
of `Y₂`. -/
theorem epi_or_epi_of_epi_biprod_desc {a d : Fin n} {Y₁ Y₂ : Statement.LinRep k n}
    (f : Y₁ ⟶ interval k a d) (g : Y₂ ⟶ interval k a d) [Epi (biprod.desc f g)] : Epi f ∨ Epi g := by
  have himg := imageSubobject_eq_top_of_epi (biprod.desc f g)
  rw [imageSubobject_biprod_desc] at himg
  rcases subobject_le_or_le (imageSubobject f) (imageSubobject g) with h | h
  · rw [sumSubobject_eq_right_of_le h] at himg
    exact Or.inr (epi_of_imageSubobject_eq_top g himg)
  · rw [sumSubobject_eq_left_of_le h] at himg
    exact Or.inl (epi_of_imageSubobject_eq_top f himg)

/-- Lemma 5.3(2): if `M_{a,d}` is a subobject of `Y₁ ⊞ Y₂`, it is a subobject of `Y₁`
or of `Y₂`. -/
theorem mono_or_mono_of_mono_biprod_lift {a d : Fin n} {Y₁ Y₂ : Statement.LinRep k n}
    (f : interval k a d ⟶ Y₁) (g : interval k a d ⟶ Y₂) [Mono (biprod.lift f g)] :
    Mono f ∨ Mono g := by
  have hker := kernelSubobject_eq_bot_of_mono (biprod.lift f g)
  rw [kernelSubobject_biprod_lift] at hker
  rcases subobject_le_or_le (kernelSubobject f) (kernelSubobject g) with h | h
  · rw [inf_eq_left.2 h] at hker
    exact Or.inl (mono_of_kernelSubobject_eq_bot f hker)
  · rw [inf_eq_right.2 h] at hker
    exact Or.inr (mono_of_kernelSubobject_eq_bot g hker)

end LinearQuiver

end PretorsionImageClosed
