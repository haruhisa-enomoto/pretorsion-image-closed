module

public import PretorsionImageClosed.LinearQuiver.Interval
public import PretorsionImageClosed.Subobjects.Preimage
public import PretorsionImageClosed.Length.Representations
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Morphisms between interval representations

Proposition 5.2 of the manuscript (Thomas): for interval representations
`M_{c,d}` and `M_{a,b}` of the linearly oriented quiver,
`Hom(M_{c,d}, M_{a,b})` is one-dimensional if `a ≤ c ≤ b ≤ d` and zero
otherwise, and a nonzero morphism has image `M_{c,b}`.

A morphism `η : M_{c,d} ⟶ M_{a,b}` is determined by its *coordinates*
`coord η i ∈ k`, the values at the unit vectors of the vertex spaces. The
naturality squares give the equation `coord_naturality`, from which the
vanishing conditions follow; when `a ≤ c` and `b ≤ d` every morphism is a
scalar multiple of the canonical morphism `canonicalHom`, which factors as the
projection `M_{c,d} ⟶ M_{c,b}` followed by the inclusion `M_{c,b} ⟶ M_{a,b}`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PretorsionImageClosed

open CategoryTheory Limits

namespace LinearQuiver

universe u

variable (k : Type u) [Field k] {n : ℕ}

/-! ### Unit vectors and coordinates -/

/-- The unit vector of the vertex space `M_{c,d}(i)`: `1` if `i ∈ [c, d]`, `0` otherwise. -/
def unit (c d i : Fin n) : intervalSpace k c d i :=
  ⟨if c ≤ i ∧ i ≤ d then 1 else 0, by
    unfold intervalSpace
    split_ifs
    · exact Submodule.mem_top
    · exact Submodule.zero_mem _⟩

theorem unit_val (c d i : Fin n) : (unit k c d i : k) = if c ≤ i ∧ i ≤ d then 1 else 0 := rfl

theorem unit_val_of_mem {c d i : Fin n} (h : c ≤ i ∧ i ≤ d) : (unit k c d i : k) = 1 := by
  rw [unit_val, if_pos h]

theorem unit_eq_zero_of_not_mem {c d i : Fin n} (h : ¬ (c ≤ i ∧ i ≤ d)) : unit k c d i = 0 := by
  apply Subtype.ext
  rw [unit_val, if_neg h]
  rfl

/-- Every element of a vertex space is a multiple of the unit vector. -/
theorem eq_smul_unit {c d i : Fin n} (x : intervalSpace k c d i) : x = (x : k) • unit k c d i := by
  apply Subtype.ext
  rw [Submodule.coe_smul, unit_val, smul_eq_mul]
  by_cases h : c ≤ i ∧ i ≤ d
  · rw [if_pos h, mul_one]
  · rw [if_neg h, mul_zero, coe_eq_zero_of_not_mem k h]

variable {k}

/-- The coordinate of a morphism `η : M_{c,d} ⟶ M_{a,b}` at the vertex `i`: the
value in `k` of `η` on the unit vector. -/
def coord {c d a b : Fin n} (η : interval k c d ⟶ interval k a b) (i : Fin n) : k :=
  ((η.app i).hom.hom (unit k c d i)).1

/-- The value of `η` on an arbitrary vector. -/
theorem app_val {c d a b : Fin n} (η : interval k c d ⟶ interval k a b) (i : Fin n)
    (x : intervalSpace k c d i) :
    ((η.app i).hom.hom x).1 = (x : k) * coord η i := by
  have h := congrArg (fun y => ((η.app i).hom.hom y).1) (eq_smul_unit k x)
  rw [h]
  erw [map_smul]
  rfl

theorem coord_eq_zero_of_not_mem_src {c d a b : Fin n} (η : interval k c d ⟶ interval k a b)
    {i : Fin n} (h : ¬ (c ≤ i ∧ i ≤ d)) : coord η i = 0 := by
  unfold coord
  rw [unit_eq_zero_of_not_mem k h]
  erw [map_zero]
  rfl

theorem coord_eq_zero_of_not_mem_tgt {c d a b : Fin n} (η : interval k c d ⟶ interval k a b)
    {i : Fin n} (h : ¬ (a ≤ i ∧ i ≤ b)) : coord η i = 0 :=
  coe_eq_zero_of_not_mem k h _

/-- Two morphisms between interval representations with the same coordinates
are equal. -/
theorem hom_ext_coord {c d a b : Fin n} {η η' : interval k c d ⟶ interval k a b}
    (h : ∀ i, coord η i = coord η' i) : η = η' := by
  ext i : 2
  apply FGModuleCat.hom_ext
  refine LinearMap.ext fun (x : intervalSpace k c d i) => ?_
  apply Subtype.ext
  change ((η.app i).hom.hom x).1 = ((η'.app i).hom.hom x).1
  rw [app_val, app_val, h]

/-- The naturality equation in coordinates: for `i ≤ j` and `i ∈ [c, d]`,
`(if j ≤ d then coord η j else 0) = if j ≤ b then coord η i else 0`. -/
theorem coord_naturality {c d a b : Fin n} (η : interval k c d ⟶ interval k a b) {i j : Fin n}
    (hij : i ≤ j) (hi : c ≤ i ∧ i ≤ d) :
    (if j ≤ d then coord η j else 0) = if j ≤ b then coord η i else 0 := by
  have hnat := congrArg (fun g => (g.hom.hom (unit k c d i)).1) (η.naturality (homOfLE hij))
  change ((η.app j).hom.hom (((interval k c d).map (homOfLE hij)).hom.hom (unit k c d i))).1 =
    (((interval k a b).map (homOfLE hij)).hom.hom ((η.app i).hom.hom (unit k c d i))).1 at hnat
  -- left side: `η_j` of the structure map applied to the unit
  have hl : ((η.app j).hom.hom (((interval k c d).map (homOfLE hij)).hom.hom (unit k c d i))).1 =
      (if j ≤ d then (1 : k) else 0) * coord η j := by
    rw [app_val]
    congr 1
    change ((inclusionOrZero k _ _ (unit k c d i) : intervalSpace k c d j) : k) = _
    rw [coe_intervalMap k hij, unit_val_of_mem k hi]
  -- right side: the structure map of `η_i` of the unit
  have hr : (((interval k a b).map (homOfLE hij)).hom.hom ((η.app i).hom.hom (unit k c d i))).1 =
      if j ≤ b then coord η i else 0 := by
    change ((inclusionOrZero k _ _ _ : intervalSpace k a b j) : k) = _
    rw [coe_intervalMap k hij]
    rfl
  rw [hl, hr] at hnat
  rw [← hnat]
  by_cases hjd : j ≤ d
  · rw [if_pos hjd, if_pos hjd, one_mul]
  · rw [if_neg hjd, if_neg hjd, zero_mul]

/-! ### Vanishing -/

/-- If `d < b`, every morphism `M_{c,d} ⟶ M_{a,b}` is zero. -/
theorem coord_eq_zero_of_lt {c d a b : Fin n} (η : interval k c d ⟶ interval k a b) (hdb : d < b)
    (i : Fin n) : coord η i = 0 := by
  by_cases hi : c ≤ i ∧ i ≤ d
  · have := coord_naturality η (hi.2.trans hdb.le) hi
    rw [if_neg (not_le.2 hdb), if_pos le_rfl] at this
    exact this.symm
  · exact coord_eq_zero_of_not_mem_src η hi

/-- If `c < a`, every morphism `M_{c,d} ⟶ M_{a,b}` is zero. -/
theorem coord_eq_zero_of_lt' {c d a b : Fin n} (η : interval k c d ⟶ interval k a b) (hca : c < a)
    (i : Fin n) : coord η i = 0 := by
  by_cases hi : a ≤ i ∧ i ≤ b
  · by_cases hi' : c ≤ i ∧ i ≤ d
    · have := coord_naturality η (hca.le.trans hi.1) ⟨le_rfl, hi'.1.trans hi'.2⟩
      rw [if_pos hi'.2, if_pos hi.2, coord_eq_zero_of_not_mem_tgt η (fun h => hca.not_ge h.1)] at this
      exact this
    · exact coord_eq_zero_of_not_mem_src η hi'
  · exact coord_eq_zero_of_not_mem_tgt η hi

/-- On the overlap `[c, b]`, the coordinates of a morphism agree. -/
theorem coord_eq_coord {c d a b : Fin n} (η : interval k c d ⟶ interval k a b) (hbd : b ≤ d)
    {i j : Fin n} (hij : i ≤ j) (hi : c ≤ i) (hj : j ≤ b) : coord η j = coord η i := by
  have := coord_naturality η hij ⟨hi, (hij.trans hj).trans hbd⟩
  rwa [if_pos (hj.trans hbd), if_pos hj] at this

/-! ### The canonical morphism -/

theorem coe_inclusionOrZero_intervalSpace {c d a b : Fin n} (hac : a ≤ c) (hbd : b ≤ d) (i : Fin n)
    (x : intervalSpace k c d i) :
    ((inclusionOrZero k (intervalSpace k c d i) (intervalSpace k a b i) x : intervalSpace k a b i) : k) =
      if i ≤ b then (x : k) else 0 := by
  rw [coe_inclusionOrZero]
  by_cases hi : c ≤ i ∧ i ≤ d
  · by_cases hib : i ≤ b
    · rw [if_pos hib, if_pos]
      unfold intervalSpace
      rw [if_pos hi, if_pos ⟨hac.trans hi.1, hib⟩]
    · rw [if_neg hib, if_neg]
      unfold intervalSpace
      rw [if_pos hi, if_neg (fun h => hib h.2)]
      intro hle
      have := hle (Submodule.mem_top (x := (1 : k)))
      rw [Submodule.mem_bot] at this
      exact one_ne_zero this
  · rw [coe_eq_zero_of_not_mem k hi x]
    split_ifs <;> rfl

/-- The canonical morphism `M_{c,d} ⟶ M_{a,b}` for `a ≤ c` and `b ≤ d`: the
identity on the overlap `[c, b]`, zero elsewhere. -/
def canonicalHom {c d a b : Fin n} (hac : a ≤ c) (hbd : b ≤ d) : interval k c d ⟶ interval k a b where
  app i := FGModuleCat.ofHom (inclusionOrZero k (intervalSpace k c d i) (intervalSpace k a b i))
  naturality {i j} f := by
    apply FGModuleCat.hom_ext
    refine LinearMap.ext fun (x : intervalSpace k c d i) => ?_
    apply Subtype.ext
    change ((inclusionOrZero k _ _ (inclusionOrZero k _ _ x) : intervalSpace k a b j) : k) =
      ((inclusionOrZero k _ _ (inclusionOrZero k _ _ x) : intervalSpace k a b j) : k)
    rw [coe_inclusionOrZero_intervalSpace hac hbd, coe_intervalMap k (leOfHom f),
      coe_intervalMap k (leOfHom f), coe_inclusionOrZero_intervalSpace hac hbd]
    by_cases hjb : j ≤ b
    · rw [if_pos hjb, if_pos hjb, if_pos (hjb.trans hbd), if_pos ((leOfHom f).trans hjb)]
    · rw [if_neg hjb, if_neg hjb]

theorem coord_canonicalHom {c d a b : Fin n} (hac : a ≤ c) (hbd : b ≤ d) (i : Fin n) :
    coord (canonicalHom (k := k) hac hbd) i = if c ≤ i ∧ i ≤ b then 1 else 0 := by
  unfold coord
  change ((inclusionOrZero k _ _ (unit k c d i) : intervalSpace k a b i) : k) = _
  rw [coe_inclusionOrZero_intervalSpace hac hbd, unit_val]
  by_cases hi : c ≤ i ∧ i ≤ d
  · by_cases hib : i ≤ b
    · rw [if_pos hib, if_pos hi, if_pos ⟨hi.1, hib⟩]
    · rw [if_neg hib, if_neg (show ¬ (c ≤ i ∧ i ≤ b) from fun h => hib h.2)]
  · rw [if_neg (show ¬ (c ≤ i ∧ i ≤ b) from fun h => hi ⟨h.1, h.2.trans hbd⟩)]
    split_ifs <;> rfl

/-- Proposition 5.2: for `a ≤ c` and `b ≤ d`, every morphism `M_{c,d} ⟶ M_{a,b}`
is the scalar `coord η c` times the canonical morphism, in coordinates. -/
theorem coord_eq_coord_mul_canonical {c d a b : Fin n} (η : interval k c d ⟶ interval k a b)
    (hac : a ≤ c) (hbd : b ≤ d) (i : Fin n) :
    coord η i = coord η c * coord (canonicalHom (k := k) hac hbd) i := by
  rw [coord_canonicalHom]
  by_cases hi : c ≤ i ∧ i ≤ b
  · rw [if_pos hi, mul_one]
    exact coord_eq_coord η hbd hi.1 le_rfl hi.2
  · rw [if_neg hi, mul_zero]
    by_cases hi' : c ≤ i ∧ i ≤ d
    · exact coord_eq_zero_of_not_mem_tgt η (fun h => hi ⟨hi'.1, h.2⟩)
    · exact coord_eq_zero_of_not_mem_src η hi'

/-- `canonicalHom = intervalProj ≫ intervalIncl`. -/
theorem canonicalHom_eq {c d a b : Fin n} (hac : a ≤ c) (hbd : b ≤ d) :
    canonicalHom (k := k) hac hbd = intervalProj k c hbd ≫ intervalIncl k b hac := by
  apply hom_ext_coord
  intro i
  rw [coord_canonicalHom]
  unfold coord
  rw [NatTrans.comp_app]
  symm
  change ((inclusionOrZero k (intervalSpace k c b i) (intervalSpace k a b i)
    (inclusionOrZero k (intervalSpace k c d i) (intervalSpace k c b i) (unit k c d i)) :
      intervalSpace k a b i) : k) = _
  rw [coe_inclusionOrZero_left k hac, coe_inclusionOrZero_right k hbd, unit_val]
  by_cases hi : c ≤ i ∧ i ≤ d
  · by_cases hib : i ≤ b
    · rw [if_pos hib, if_pos hi, if_pos ⟨hi.1, hib⟩]
    · rw [if_neg hib, if_neg (show ¬ (c ≤ i ∧ i ≤ b) from fun h => hib h.2)]
  · rw [if_neg (show ¬ (c ≤ i ∧ i ≤ b) from fun h => hi ⟨h.1, h.2.trans hbd⟩)]
    split_ifs <;> rfl

/-! ### The inclusions are monomorphisms, the projections epimorphisms -/

instance mono_intervalIncl {a ℓ d : Fin n} (h : a ≤ ℓ) : Mono (intervalIncl k d h) := by
  rw [NatTrans.mono_iff_mono_app]
  intro i
  rw [FGModuleCat.mono_iff_injective]
  intro (x : intervalSpace k ℓ d i) (y : intervalSpace k ℓ d i) hxy
  apply Subtype.ext
  have := congrArg Subtype.val hxy
  change ((inclusionOrZero k _ _ x : intervalSpace k a d i) : k) =
    ((inclusionOrZero k _ _ y : intervalSpace k a d i) : k) at this
  rwa [coe_inclusionOrZero_left k h, coe_inclusionOrZero_left k h] at this

instance epi_intervalProj (a : Fin n) {ℓ d : Fin n} (h : ℓ ≤ d) : Epi (intervalProj k a h) := by
  rw [NatTrans.epi_iff_epi_app]
  intro i
  rw [FGModuleCat.epi_iff_surjective]
  intro (y : intervalSpace k a ℓ i)
  by_cases hi : a ≤ i ∧ i ≤ ℓ
  · refine ⟨⟨y.1, ?_⟩, ?_⟩
    · rw [intervalSpace_of_mem k ⟨hi.1, hi.2.trans h⟩]
      exact Submodule.mem_top
    · apply Subtype.ext
      change ((inclusionOrZero k _ _ (⟨y.1, _⟩ : intervalSpace k a d i) : intervalSpace k a ℓ i) : k) = _
      rw [coe_inclusionOrZero_right k h, if_pos hi.2]
  · refine ⟨0, ?_⟩
    apply Subtype.ext
    erw [map_zero]
    rw [coe_eq_zero_of_not_mem k hi y]
    rfl

/-- Proposition 5.2: the image of the canonical morphism `M_{c,d} ⟶ M_{a,b}` is
the subrepresentation `M_{c,b}`. -/
theorem imageSubobject_canonicalHom {c d a b : Fin n} (hac : a ≤ c) (hbd : b ≤ d) :
    imageSubobject (canonicalHom (k := k) hac hbd) = Subobject.mk (intervalIncl k b hac) := by
  rw [canonicalHom_eq, imageSubobject_epi_comp, imageSubobject_mono]

end LinearQuiver

end PretorsionImageClosed
