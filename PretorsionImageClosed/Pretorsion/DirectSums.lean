module

public import PretorsionImageClosed.Pretorsion.Basic

/-!
# Short preexact sequences and direct sums

Triviality of morphisms and short preexact sequences are compatible with
binary direct sums and transport along isomorphisms. Together with the
decomposition of an object into indecomposables, this reduces the verification
of the pretorsion-theory axioms to indecomposable objects.
-/

@[expose] public section

set_option autoImplicit false

namespace PretorsionImageClosed.Statement

open CategoryTheory Limits

variable {C : Type*} [Category C] [Abelian C] {Zs : Subcategory C}

theorem biprod_map_comp_map {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁)
    (g₂ : Y₂ ⟶ Z₂) : biprod.map f₁ f₂ ≫ biprod.map g₁ g₂ = biprod.map (f₁ ≫ g₁) (f₂ ≫ g₂) := by
  apply biprod.hom_ext <;> simp

/-! ### Trivial morphisms -/

theorem IsTrivial.biprod_map {X₁ X₂ Y₁ Y₂ : C} {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂}
    (h₁ : IsTrivial Zs.prop f₁) (h₂ : IsTrivial Zs.prop f₂) :
    IsTrivial Zs.prop (biprod.map f₁ f₂) := by
  obtain ⟨W₁, hW₁, g₁, k₁, rfl⟩ := h₁
  obtain ⟨W₂, hW₂, g₂, k₂, rfl⟩ := h₂
  exact ⟨W₁ ⊞ W₂, Zs.prop_biprod hW₁ hW₂, biprod.map g₁ g₂, biprod.map k₁ k₂,
    biprod_map_comp_map _ _ _ _⟩

theorem IsTrivial.biprod_lift {W Y₁ Y₂ : C} {f₁ : W ⟶ Y₁} {f₂ : W ⟶ Y₂}
    (h₁ : IsTrivial Zs.prop f₁) (h₂ : IsTrivial Zs.prop f₂) :
    IsTrivial Zs.prop (biprod.lift f₁ f₂) := by
  obtain ⟨W₁, hW₁, g₁, k₁, rfl⟩ := h₁
  obtain ⟨W₂, hW₂, g₂, k₂, rfl⟩ := h₂
  refine ⟨W₁ ⊞ W₂, Zs.prop_biprod hW₁ hW₂, biprod.lift g₁ g₂, biprod.map k₁ k₂, ?_⟩
  apply biprod.hom_ext <;> simp

theorem IsTrivial.biprod_desc {X₁ X₂ Y : C} {f₁ : X₁ ⟶ Y} {f₂ : X₂ ⟶ Y}
    (h₁ : IsTrivial Zs.prop f₁) (h₂ : IsTrivial Zs.prop f₂) :
    IsTrivial Zs.prop (biprod.desc f₁ f₂) := by
  obtain ⟨W₁, hW₁, g₁, k₁, rfl⟩ := h₁
  obtain ⟨W₂, hW₂, g₂, k₂, rfl⟩ := h₂
  refine ⟨W₁ ⊞ W₂, Zs.prop_biprod hW₁ hW₂, biprod.map g₁ g₂, biprod.desc k₁ k₂, ?_⟩
  apply biprod.hom_ext' <;> simp

/-! ### Short preexact sequences -/

theorem IsPrekernel.biprod {T₁ X₁ F₁ T₂ X₂ F₂ : C} {u₁ : T₁ ⟶ X₁} {v₁ : X₁ ⟶ F₁} {u₂ : T₂ ⟶ X₂}
    {v₂ : X₂ ⟶ F₂} (h₁ : IsPrekernel Zs.prop u₁ v₁) (h₂ : IsPrekernel Zs.prop u₂ v₂) :
    IsPrekernel Zs.prop (biprod.map u₁ u₂) (biprod.map v₁ v₂) := by
  refine ⟨?_, ?_⟩
  · rw [biprod_map_comp_map]
    exact h₁.1.biprod_map h₂.1
  · intro Y u' hu'
    have t₁ : IsTrivial Zs.prop ((u' ≫ biprod.fst) ≫ v₁) := by
      rw [Category.assoc, ← biprod.map_fst, ← Category.assoc]
      exact hu'.comp_right _
    have t₂ : IsTrivial Zs.prop ((u' ≫ biprod.snd) ≫ v₂) := by
      rw [Category.assoc, ← biprod.map_snd, ← Category.assoc]
      exact hu'.comp_right _
    obtain ⟨w₁, hw₁, hu₁⟩ := h₁.2 _ t₁
    obtain ⟨w₂, hw₂, hu₂⟩ := h₂.2 _ t₂
    refine ⟨biprod.lift w₁ w₂, ?_, ?_⟩
    · apply biprod.hom_ext <;> simp [hw₁, hw₂]
    · intro w hw
      apply biprod.hom_ext
      · rw [biprod.lift_fst]
        apply hu₁
        rw [Category.assoc, ← biprod.map_fst, ← Category.assoc, hw]
      · rw [biprod.lift_snd]
        apply hu₂
        rw [Category.assoc, ← biprod.map_snd, ← Category.assoc, hw]

theorem IsPrecokernel.biprod {T₁ X₁ F₁ T₂ X₂ F₂ : C} {u₁ : T₁ ⟶ X₁} {v₁ : X₁ ⟶ F₁} {u₂ : T₂ ⟶ X₂}
    {v₂ : X₂ ⟶ F₂} (h₁ : IsPrecokernel Zs.prop u₁ v₁) (h₂ : IsPrecokernel Zs.prop u₂ v₂) :
    IsPrecokernel Zs.prop (biprod.map u₁ u₂) (biprod.map v₁ v₂) := by
  refine ⟨?_, ?_⟩
  · rw [biprod_map_comp_map]
    exact h₁.1.biprod_map h₂.1
  · intro Y v' hv'
    have t₁ : IsTrivial Zs.prop (u₁ ≫ biprod.inl ≫ v') := by
      rw [← Category.assoc, ← biprod.inl_map, Category.assoc]
      exact hv'.comp_left _
    have t₂ : IsTrivial Zs.prop (u₂ ≫ biprod.inr ≫ v') := by
      rw [← Category.assoc, ← biprod.inr_map, Category.assoc]
      exact hv'.comp_left _
    obtain ⟨w₁, hw₁, hv₁⟩ := h₁.2 _ t₁
    obtain ⟨w₂, hw₂, hv₂⟩ := h₂.2 _ t₂
    refine ⟨biprod.desc w₁ w₂, ?_, ?_⟩
    · apply biprod.hom_ext' <;> simp [hw₁, hw₂]
    · intro w hw
      apply biprod.hom_ext'
      · rw [biprod.inl_desc]
        apply hv₁
        rw [← Category.assoc, ← biprod.inl_map, Category.assoc, hw]
      · rw [biprod.inr_desc]
        apply hv₂
        rw [← Category.assoc, ← biprod.inr_map, Category.assoc, hw]

theorem IsShortPreexact.biprod {T₁ X₁ F₁ T₂ X₂ F₂ : C} {u₁ : T₁ ⟶ X₁} {v₁ : X₁ ⟶ F₁}
    {u₂ : T₂ ⟶ X₂} {v₂ : X₂ ⟶ F₂} (h₁ : IsShortPreexact Zs.prop u₁ v₁)
    (h₂ : IsShortPreexact Zs.prop u₂ v₂) :
    IsShortPreexact Zs.prop (biprod.map u₁ u₂) (biprod.map v₁ v₂) :=
  ⟨h₁.1.biprod h₂.1, h₁.2.biprod h₂.2⟩

/-- Transport of a short preexact sequence along an isomorphism of the middle term. -/
theorem IsShortPreexact.of_iso {T X X' F : C} {u : T ⟶ X} {v : X ⟶ F}
    (h : IsShortPreexact Zs.prop u v) (e : X ≅ X') :
    IsShortPreexact Zs.prop (u ≫ e.hom) (e.inv ≫ v) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact h.1.1
  · intro Y u' hu'
    rw [← Category.assoc] at hu'
    obtain ⟨w, hw, huniq⟩ := h.1.2 _ hu'
    refine ⟨w, ?_, ?_⟩
    · show w ≫ u ≫ e.hom = u'
      rw [← Category.assoc, hw, Category.assoc, e.inv_hom_id, Category.comp_id]
    · intro w' hw'
      have hw'' : w' ≫ u ≫ e.hom = u' := hw'
      apply huniq
      show w' ≫ u = u' ≫ e.inv
      rw [← hw'', Category.assoc, Category.assoc, e.hom_inv_id, Category.comp_id]
  · simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact h.2.1
  · intro Y v' hv'
    rw [Category.assoc] at hv'
    obtain ⟨w, hw, huniq⟩ := h.2.2 _ hv'
    refine ⟨w, ?_, ?_⟩
    · show (e.inv ≫ v) ≫ w = v'
      rw [Category.assoc, hw, e.inv_hom_id_assoc]
    · intro w' hw'
      have hw'' : (e.inv ≫ v) ≫ w' = v' := hw'
      apply huniq
      show v ≫ w' = e.hom ≫ v'
      rw [← hw'']
      simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- The identity sequence of an object of `Zs` is short preexact. -/
theorem isShortPreexact_id {X : C} (hX : Zs.prop X) :
    IsShortPreexact Zs.prop (𝟙 X) (𝟙 X) := by
  refine ⟨⟨IsTrivial.of_prop_src _ hX, ?_⟩, ⟨IsTrivial.of_prop_src _ hX, ?_⟩⟩
  · intro Y u' _
    exact ⟨u', Category.comp_id _, fun w hw => by rw [← hw, Category.comp_id]⟩
  · intro Y v' _
    exact ⟨v', Category.id_comp _, fun w hw => by rw [← hw, Category.id_comp]⟩

end PretorsionImageClosed.Statement
