module

public import PretorsionImageClosed.Subcategories.Basic

/-!
# Pretorsion theories: first properties

Lemma 2.11: `Z`-prekernels are monomorphisms and `Z`-precokernels are
epimorphisms. Proposition 2.3 (Campanini–Fedele–Yıldırım): the first
component of a pretorsion theory is quotient-closed and the second is
subobject-closed; closure under finite direct sums and summands is part of
the subcategory convention here. Invariance of prekernels and precokernels
under isomorphisms is recorded as well.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PretorsionImageClosed

open CategoryTheory Limits ZeroObject

namespace Statement

variable {C : Type*} [Category C] {Z : ObjectProperty C}

/-! ### Lemma 2.11 -/

/-- Lemma 2.11: a `Z`-prekernel is a monomorphism. -/
theorem IsPrekernel.mono {T X F : C} {u : T ⟶ X} {v : X ⟶ F} (h : IsPrekernel Z u v) : Mono u := by
  refine ⟨fun {Y} a b hab => ?_⟩
  have htriv : IsTrivial Z ((a ≫ u) ≫ v) := by
    rw [Category.assoc]
    exact h.1.comp_left a
  obtain ⟨_, -, huniq⟩ := h.2 (a ≫ u) htriv
  exact (huniq a rfl).trans (huniq b hab.symm).symm

/-- Lemma 2.11: a `Z`-precokernel is an epimorphism. -/
theorem IsPrecokernel.epi {T X F : C} {u : T ⟶ X} {v : X ⟶ F} (h : IsPrecokernel Z u v) :
    Epi v := by
  refine ⟨fun {Y} a b hab => ?_⟩
  have htriv : IsTrivial Z (u ≫ v ≫ a) := by
    rw [← Category.assoc]
    exact h.1.comp_right a
  obtain ⟨_, -, huniq⟩ := h.2 (v ≫ a) htriv
  exact (huniq a rfl).trans (huniq b hab.symm).symm

/-! ### Invariance under isomorphisms -/

theorem IsPrekernel.of_iso_left {T T' X F : C} {u : T ⟶ X} {v : X ⟶ F} (h : IsPrekernel Z u v)
    (e : T' ≅ T) : IsPrekernel Z (e.hom ≫ u) v := by
  refine ⟨by rw [Category.assoc]; exact h.1.comp_left e.hom, fun {Y} u' hu' => ?_⟩
  obtain ⟨w, hw, huniq⟩ := h.2 u' hu'
  refine ⟨w ≫ e.inv, by simp [hw], fun w' hw' => ?_⟩
  rw [← huniq (w' ≫ e.hom) (by simpa using hw')]
  simp

theorem IsPrekernel.comp_iso_right {T X F F' : C} {u : T ⟶ X} {v : X ⟶ F} (h : IsPrekernel Z u v)
    (e : F ≅ F') : IsPrekernel Z u (v ≫ e.hom) := by
  refine ⟨by rw [← Category.assoc]; exact h.1.comp_right e.hom, fun {Y} u' hu' => ?_⟩
  apply h.2 u'
  have := hu'.comp_right e.inv
  simpa using this

theorem IsPrecokernel.of_iso_left {T T' X F : C} {u : T ⟶ X} {v : X ⟶ F}
    (h : IsPrecokernel Z u v) (e : T' ≅ T) : IsPrecokernel Z (e.hom ≫ u) v := by
  refine ⟨by rw [Category.assoc]; exact h.1.comp_left e.hom, fun {Y} v' hv' => ?_⟩
  apply h.2 v'
  have := hv'.comp_left e.inv
  simpa using this

theorem IsPrecokernel.comp_iso_right {T X F F' : C} {u : T ⟶ X} {v : X ⟶ F}
    (h : IsPrecokernel Z u v) (e : F ≅ F') : IsPrecokernel Z u (v ≫ e.hom) := by
  refine ⟨by rw [← Category.assoc]; exact h.1.comp_right e.hom, fun {Y} v' hv' => ?_⟩
  obtain ⟨w, hw, huniq⟩ := h.2 v' hv'
  refine ⟨e.inv ≫ w, by simp [hw], fun w' hw' => ?_⟩
  rw [← huniq (e.hom ≫ w') (by simpa using hw')]
  simp

theorem IsPrekernel.of_eq {T X F : C} {u u' : T ⟶ X} {v : X ⟶ F} (h : IsPrekernel Z u v)
    (e : u = u') : IsPrekernel Z u' v := e ▸ h

theorem IsPrecokernel.of_eq {T X F : C} {u : T ⟶ X} {v v' : X ⟶ F} (h : IsPrecokernel Z u v)
    (e : v = v') : IsPrecokernel Z u v' := e ▸ h

/-! ### Proposition 2.3 -/

section Components

variable [HasZeroMorphisms C] [HasBinaryBiproducts C] [Balanced C]

/-- Proposition 2.3 (Campanini–Fedele–Yıldırım), first half: the first
component of a pretorsion theory is quotient-closed. -/
theorem IsPretorsionTheory.isQuotientClosed {T F : Subcategory C}
    (h : IsPretorsionTheory T.prop F.prop) : T.IsQuotientClosed := by
  intro X Y q hq hX
  obtain ⟨T', F', u, v, hT', hF', hu, hv⟩ := h.2 Y
  -- `q ≫ v` is trivial, so `q` factors through the prekernel `u`
  obtain ⟨w, hw, -⟩ := hu.2 q (h.1 (q ≫ v) hX hF')
  have : Mono u := hu.mono
  have : Epi u := by
    refine ⟨fun {W} a b hab => ?_⟩
    rw [← cancel_epi q, ← hw, Category.assoc, Category.assoc, hab]
  have : IsIso u := isIso_of_mono_of_epi u
  exact T.prop_of_isIso u hT'

/-- Proposition 2.3 (Campanini–Fedele–Yıldırım), second half: the second
component of a pretorsion theory is subobject-closed. -/
theorem IsPretorsionTheory.isSubobjectClosed {T F : Subcategory C}
    (h : IsPretorsionTheory T.prop F.prop) : F.IsSubobjectClosed := by
  intro X Y i hi hY
  obtain ⟨T', F', u, v, hT', hF', hu, hv⟩ := h.2 X
  -- `u ≫ i` is trivial, so `i` factors through the precokernel `v`
  obtain ⟨w, hw, -⟩ := hv.2 i (h.1 (u ≫ i) hT' hY)
  have : Epi v := hv.epi
  have : Mono v := by
    refine ⟨fun {W} a b hab => ?_⟩
    rw [← cancel_mono i, ← hw, ← Category.assoc, ← Category.assoc, hab]
  have : IsIso v := isIso_of_mono_of_epi v
  exact F.prop_of_iso (asIso v).symm hF'

end Components


/-- Pretorsion theories with the same components are equal. -/
theorem PretorsionTheory.ext {D : Type*} [Category D] [HasZeroMorphisms D] [HasBinaryBiproducts D]
    {P Q : PretorsionTheory D} (hT : P.T = Q.T) (hF : P.F = Q.F) : P = Q := by
  cases P
  cases Q
  cases hT
  cases hF
  rfl

end Statement

end PretorsionImageClosed
