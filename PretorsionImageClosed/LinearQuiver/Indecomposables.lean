module

public import PretorsionImageClosed.LinearQuiver.Decomposition

/-!
# The indecomposable representations of the linear quiver

Consequences of the structure theorem and of the morphism computations:

* intervals are indecomposable (`indecomposable_interval`) and isomorphic
  intervals have the same endpoints (`interval_iso_iff`);
* every indecomposable representation is isomorphic to an interval
  (`exists_iso_interval_of_indecomposable`), so the intervals `M_{a,d}`,
  `a ≤ d`, form a complete set of representatives of the indecomposables, as
  stated after Definition 5.1;
* (5.1): a monomorphism `M_{a',d'} ⟶ M_{a,d}` forces `d' = d` and `a ≤ a'`, an
  epimorphism `M_{a,d} ⟶ M_{a',d'}` forces `a' = a` and `d' ≤ d`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PretorsionImageClosed

open CategoryTheory Limits

namespace LinearQuiver

universe u

variable {k : Type u} [Field k] {n : ℕ}

/-! ### Coordinates of compositions, identities and zero -/

theorem coord_comp {c d a b a' b' : Fin n} (η : interval k c d ⟶ interval k a b)
    (θ : interval k a b ⟶ interval k a' b') (i : Fin n) :
    coord (η ≫ θ) i = coord η i * coord θ i := by
  unfold coord
  rw [NatTrans.comp_app]
  change ((θ.app i).hom.hom ((η.app i).hom.hom (unit k c d i))).1 = _
  rw [app_val]
  rfl

theorem coord_id (a d i : Fin n) : coord (𝟙 (interval k a d)) i = if a ≤ i ∧ i ≤ d then 1 else 0 := by
  unfold coord
  rw [NatTrans.id_app]
  change (unit k a d i : k) = _
  rw [unit_val]

theorem coord_zero (c d a b i : Fin n) : coord (0 : interval k c d ⟶ interval k a b) i = 0 := by
  unfold coord
  change ((0 : (interval k c d).obj i ⟶ (interval k a b).obj i).hom.hom (unit k c d i)).1 = 0
  rfl

/-! ### Intervals are indecomposable -/

theorem not_isZero_interval_of_le {a d : Fin n} (h : a ≤ d) : ¬ IsZero (interval k a d) :=
  not_isZero_interval h

/-- An endomorphism of an interval is determined by one coordinate on the
interval. -/
theorem coord_end_eq {a d : Fin n} (had : a ≤ d) (p : interval k a d ⟶ interval k a d) (i : Fin n) :
    coord p i = coord p a * coord (𝟙 (interval k a d)) i := by
  rw [coord_id]
  by_cases hi : a ≤ i ∧ i ≤ d
  · rw [if_pos hi, mul_one]
    exact coord_eq_coord p le_rfl hi.1 le_rfl hi.2
  · rw [if_neg hi, mul_zero]
    exact coord_eq_zero_of_not_mem_src p hi

theorem indecomposable_interval {a d : Fin n} (had : a ≤ d) : Indecomposable (interval k a d) := by
  refine ⟨not_isZero_interval had, fun Y Z e => ?_⟩
  -- the idempotent cutting out `Y`
  set p : interval k a d ⟶ interval k a d := e.hom ≫ biprod.fst ≫ biprod.inl ≫ e.inv with hp
  have hpp : p ≫ p = p := by
    rw [hp]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, biprod.inl_fst_assoc]
  have hl : coord p a * coord p a = coord p a := by
    have := congrArg (fun q => coord q a) hpp
    rwa [coord_comp] at this
  have hl' : coord p a = 0 ∨ coord p a = 1 := by
    rcases eq_or_ne (coord p a) 0 with h | h
    · exact Or.inl h
    · exact Or.inr (mul_left_cancel₀ h (by rw [hl, mul_one]))
  rcases hl' with h0 | h1
  · -- `p = 0`, so `Y` is zero
    have hp0 : p = 0 := hom_ext_coord fun i => by
      rw [coord_end_eq had p i, h0, zero_mul, coord_zero]
    left
    rw [IsZero.iff_id_eq_zero]
    have : (biprod.fst ≫ biprod.inl : Y ⊞ Z ⟶ Y ⊞ Z) = 0 := by
      have h2 : e.inv ≫ p ≫ e.hom = biprod.fst ≫ biprod.inl := by
        rw [hp]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]
      rw [← h2, hp0, zero_comp, comp_zero]
    have h3 : (biprod.inl : Y ⟶ Y ⊞ Z) = 0 := by
      have := congrArg (fun q => (biprod.inl : Y ⟶ Y ⊞ Z) ≫ q) this
      simpa using this
    rw [← biprod.inl_fst (X := Y) (Y := Z), h3, zero_comp]
  · -- `p = 𝟙`, so `Z` is zero
    have hp1 : p = 𝟙 _ := hom_ext_coord fun i => by
      rw [coord_end_eq had p i, h1, one_mul]
    right
    rw [IsZero.iff_id_eq_zero]
    have : (biprod.fst ≫ biprod.inl : Y ⊞ Z ⟶ Y ⊞ Z) = 𝟙 _ := by
      have h2 : e.inv ≫ p ≫ e.hom = biprod.fst ≫ biprod.inl := by
        rw [hp]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]
      rw [← h2, hp1, Category.id_comp, Iso.inv_hom_id]
    have := congrArg (fun q => (biprod.inr : Z ⟶ Y ⊞ Z) ≫ q ≫ biprod.snd) this
    simpa using this.symm

/-! ### Isomorphic intervals have the same endpoints -/

theorem finrank_obj_eq_of_iso {X Y : Statement.LinRep k n} (e : X ≅ Y) (i : Fin n) :
    Module.finrank k (X.obj i) = Module.finrank k (Y.obj i) :=
  LinearEquiv.finrank_eq (FGModuleCat.isoToLinearEquiv (e.app i))

theorem interval_iso_iff {a d a' d' : Fin n} (had : a ≤ d) (had' : a' ≤ d') :
    Nonempty (interval k a d ≅ interval k a' d') ↔ a = a' ∧ d = d' := by
  constructor
  · rintro ⟨e⟩
    have h : ∀ i, (if a ≤ i ∧ i ≤ d then (1 : ℕ) else 0) = if a' ≤ i ∧ i ≤ d' then 1 else 0 := by
      intro i
      have := finrank_obj_eq_of_iso e i
      change Module.finrank k (intervalSpace k a d i) = Module.finrank k (intervalSpace k a' d' i)
        at this
      rwa [finrank_intervalSpace, finrank_intervalSpace] at this
    have hmem : ∀ i, (a ≤ i ∧ i ≤ d) ↔ (a' ≤ i ∧ i ≤ d') := by
      intro i
      have hi := h i
      constructor
      · intro hi1
        by_contra hi2
        rw [if_pos hi1, if_neg hi2] at hi
        exact one_ne_zero hi
      · intro hi2
        by_contra hi1
        rw [if_neg hi1, if_pos hi2] at hi
        exact zero_ne_one hi
    have ha := (hmem a).1 ⟨le_rfl, had⟩
    have ha' := (hmem a').2 ⟨le_rfl, had'⟩
    have hd := (hmem d).1 ⟨had, le_rfl⟩
    have hd' := (hmem d').2 ⟨had', le_rfl⟩
    exact ⟨le_antisymm ha'.1 ha.1, le_antisymm hd.2 hd'.2⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨Iso.refl _⟩

/-! ### Indecomposables are intervals -/

theorem exists_iso_interval_of_indecomposable {X : Statement.LinRep k n} (hX : Indecomposable X) :
    ∃ a d : Fin n, a ≤ d ∧ Nonempty (X ≅ interval k a d) := by
  obtain ⟨a, d, had, X', ⟨e⟩⟩ := exists_iso_biprod_interval X hX.1
  rcases hX.2 _ _ e with h | h
  · exact absurd h (not_isZero_interval had)
  · exact ⟨a, d, had, ⟨e ≪≫ (isoBiprodZero h).symm⟩⟩

/-! ### Monomorphisms and epimorphisms between intervals (5.1) -/

/-- A morphism between intervals with a nonzero coordinate forces the
inequalities `a ≤ c` and `b ≤ d`. -/
theorem le_of_coord_ne_zero {c d a b : Fin n} (η : interval k c d ⟶ interval k a b) {i : Fin n}
    (h : coord η i ≠ 0) : a ≤ c ∧ b ≤ d := by
  constructor
  · by_contra hca
    exact h (coord_eq_zero_of_lt' η (not_le.1 hca) i)
  · by_contra hbd
    exact h (coord_eq_zero_of_lt η (not_le.1 hbd) i)

/-- A monomorphism `M_{a',d'} ⟶ M_{a,d}` between nonzero intervals has `d' = d` and
`a ≤ a'`. -/
theorem eq_and_le_of_mono {a' d' a d : Fin n} (had' : a' ≤ d') (η : interval k a' d' ⟶ interval k a d)
    [Mono η] : d' = d ∧ a ≤ a' := by
  -- `η` is injective at the vertex `d'`, where the source is nonzero
  have hinj := (FGModuleCat.mono_iff_injective (η.app d')).1 ((NatTrans.mono_iff_mono_app η).1 inferInstance d')
  have hne : coord η d' ≠ 0 := by
    intro h0
    have h1 : (η.app d').hom.hom (unit k a' d' d') = (η.app d').hom.hom 0 := by
      apply Subtype.ext
      rw [app_val, map_zero]
      change _ = (0 : k)
      rw [h0, mul_zero]
    have := hinj h1
    rw [Subtype.ext_iff, unit_val_of_mem k ⟨had', le_rfl⟩] at this
    exact one_ne_zero this
  obtain ⟨haa', hdd'⟩ := le_of_coord_ne_zero η hne
  have hmem : a ≤ d' ∧ d' ≤ d := by
    by_contra h
    exact hne (coord_eq_zero_of_not_mem_tgt η h)
  exact ⟨le_antisymm hmem.2 hdd', haa'⟩

/-- An epimorphism `M_{a,d} ⟶ M_{a',d'}` between nonzero intervals has `a' = a` and
`d' ≤ d`. -/
theorem eq_and_le_of_epi {a d a' d' : Fin n} (had' : a' ≤ d') (η : interval k a d ⟶ interval k a' d')
    [Epi η] : a' = a ∧ d' ≤ d := by
  -- `η` is surjective at the vertex `a'`, where the target is nonzero
  have hsurj := (FGModuleCat.epi_iff_surjective (η.app a')).1 ((NatTrans.epi_iff_epi_app η).1 inferInstance a')
  have hne : coord η a' ≠ 0 := by
    intro h0
    obtain ⟨x, hx⟩ := hsurj (unit k a' d' a')
    have := congrArg Subtype.val hx
    rw [app_val, h0, mul_zero, unit_val_of_mem k ⟨le_rfl, had'⟩] at this
    exact zero_ne_one this
  obtain ⟨haa', hdd'⟩ := le_of_coord_ne_zero η hne
  have hmem : a ≤ a' ∧ a' ≤ d := by
    by_contra h
    exact hne (coord_eq_zero_of_not_mem_src η h)
  exact ⟨le_antisymm haa' hmem.1, hdd'⟩

end LinearQuiver

end PretorsionImageClosed
