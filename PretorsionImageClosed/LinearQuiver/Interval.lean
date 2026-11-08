module

public import PretorsionImageClosed.Statement
public import PretorsionImageClosed.Modules.FiniteModules
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Interval representations of the linearly oriented quiver

The representations of `1 → 2 → ⋯ → n` are the functors `Fin n ⥤ FGModuleCat k`
(`Statement.LinRep`). For `a ≤ d` in `Fin n`, the interval representation
`interval k a d` (Definition 5.1, `M_{a,d}` in the manuscript) is `k` at the
vertices of `[a, d]`, zero elsewhere, with identity maps inside the interval.
It is realized with the submodule of `k` that is `⊤` on `[a, d]` and `⊥`
outside, so that all vertex spaces have one uniform type; every structure map
is "the inclusion if it exists, zero otherwise" (`inclusionOrZero`), whose
value in `k` is given by `coe_inclusionOrZero`.

This file gives the construction and its basic API: values and maps at the
vertices, the canonical inclusions `interval k ℓ d ⟶ interval k a d` and
projections `interval k a d ⟶ interval k a ℓ`, and the dimension of the vertex
spaces.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PretorsionImageClosed

open CategoryTheory Limits

namespace LinearQuiver

universe u

variable (k : Type u) [Field k]

/-! ### Inclusion-or-zero maps between submodules of `k` -/

/-- The inclusion `p → q` if `p ≤ q`, and zero otherwise. -/
def inclusionOrZero (p q : Submodule k k) : p →ₗ[k] q :=
  by classical exact if h : p ≤ q then Submodule.inclusion h else 0

theorem inclusionOrZero_of_le {p q : Submodule k k} (h : p ≤ q) :
    inclusionOrZero k p q = Submodule.inclusion h := by
  unfold inclusionOrZero
  rw [dif_pos h]

theorem inclusionOrZero_of_not_le {p q : Submodule k k} (h : ¬ p ≤ q) :
    inclusionOrZero k p q = 0 := by
  unfold inclusionOrZero
  rw [dif_neg h]

open Classical in
theorem coe_inclusionOrZero (p q : Submodule k k) (x : p) :
    ((inclusionOrZero k p q x : q) : k) = if p ≤ q then (x : k) else 0 := by
  by_cases h : p ≤ q
  · rw [inclusionOrZero_of_le k h, if_pos h, Submodule.coe_inclusion]
  · rw [inclusionOrZero_of_not_le k h, if_neg h]
    rfl

theorem inclusionOrZero_self (p : Submodule k k) : inclusionOrZero k p p = LinearMap.id := by
  rw [inclusionOrZero_of_le k le_rfl]
  rfl

/-! ### Vertex spaces -/

variable {n : ℕ}

/-- The vertex space of the interval `[a, d]` at `i`: `k` (as `⊤`) if `i ∈ [a, d]`,
zero (as `⊥`) otherwise. -/
def intervalSpace (a d i : Fin n) : Submodule k k :=
  if a ≤ i ∧ i ≤ d then ⊤ else ⊥

theorem intervalSpace_of_mem {a d i : Fin n} (h : a ≤ i ∧ i ≤ d) :
    intervalSpace k a d i = ⊤ := if_pos h

theorem intervalSpace_of_not_mem {a d i : Fin n} (h : ¬ (a ≤ i ∧ i ≤ d)) :
    intervalSpace k a d i = ⊥ := if_neg h

theorem coe_eq_zero_of_not_mem {a d i : Fin n} (h : ¬ (a ≤ i ∧ i ≤ d)) (x : intervalSpace k a d i) :
    (x : k) = 0 := by
  have hle : intervalSpace k a d i ≤ ⊥ := (intervalSpace_of_not_mem k h).le
  exact (Submodule.mem_bot k).1 (hle x.2)

theorem intervalSpace_le_iff {a d i j : Fin n} (hij : i ≤ j) :
    intervalSpace k a d i ≤ intervalSpace k a d j ↔ ((a ≤ i ∧ i ≤ d) → j ≤ d) := by
  unfold intervalSpace
  constructor
  · intro h hi
    by_contra hjd
    rw [if_pos hi, if_neg (fun hj => hjd hj.2)] at h
    have := h (Submodule.mem_top (x := (1 : k)))
    rw [Submodule.mem_bot] at this
    exact one_ne_zero this
  · intro h
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd ⟨h1.1.trans hij, h h1⟩ h2
    · exact bot_le
    · exact le_rfl

/-- The value in `k` of the structure map from vertex `i` to vertex `j ≥ i`. -/
theorem coe_intervalMap {a d i j : Fin n} (hij : i ≤ j) (x : intervalSpace k a d i) :
    ((inclusionOrZero k (intervalSpace k a d i) (intervalSpace k a d j) x : intervalSpace k a d j) : k) =
      if j ≤ d then (x : k) else 0 := by
  rw [coe_inclusionOrZero, intervalSpace_le_iff k hij]
  by_cases hi : a ≤ i ∧ i ≤ d
  · by_cases hjd : j ≤ d
    · rw [if_pos (fun _ => hjd), if_pos hjd]
    · rw [if_neg (fun h => hjd (h hi)), if_neg hjd]
  · rw [coe_eq_zero_of_not_mem k hi x]
    split_ifs <;> rfl

/-! ### The interval representation -/

/-- The interval representation `M_{a,d}` (Definition 5.1). -/
abbrev interval (a d : Fin n) : Statement.LinRep k n where
  obj i := FGModuleCat.of k (intervalSpace k a d i)
  map {i j} f :=
    FGModuleCat.ofHom (inclusionOrZero k (intervalSpace k a d i) (intervalSpace k a d j))
  map_id i := by
    apply FGModuleCat.hom_ext
    exact inclusionOrZero_self k _
  map_comp {i j l} f g := by
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change ((inclusionOrZero k _ _ x : intervalSpace k a d l) : k) =
      ((inclusionOrZero k _ _ (inclusionOrZero k _ _ x) : intervalSpace k a d l) : k)
    rw [coe_intervalMap k (leOfHom (f ≫ g)), coe_intervalMap k (leOfHom g),
      coe_intervalMap k (leOfHom f)]
    by_cases hl : l ≤ d
    · rw [if_pos hl, if_pos hl, if_pos ((leOfHom g).trans hl)]
    · rw [if_neg hl, if_neg hl]

theorem interval_obj (a d i : Fin n) :
    (interval k a d).obj i = FGModuleCat.of k (intervalSpace k a d i) := rfl

theorem interval_map (a d : Fin n) {i j : Fin n} (f : i ⟶ j) :
    (interval k a d).map f =
      FGModuleCat.ofHom (inclusionOrZero k (intervalSpace k a d i) (intervalSpace k a d j)) := rfl

theorem finrank_intervalSpace (a d i : Fin n) :
    Module.finrank k (intervalSpace k a d i) = if a ≤ i ∧ i ≤ d then 1 else 0 := by
  by_cases h : a ≤ i ∧ i ≤ d
  · rw [intervalSpace_of_mem k h, if_pos h, finrank_top, Module.finrank_self]
  · rw [intervalSpace_of_not_mem k h, if_neg h, finrank_bot]

theorem isZero_interval_obj_of_not_mem {a d i : Fin n} (h : ¬ (a ≤ i ∧ i ≤ d)) :
    IsZero ((interval k a d).obj i) := by
  rw [FGModuleCat.isZero_iff_subsingleton, interval_obj]
  change Subsingleton (intervalSpace k a d i)
  rw [Submodule.subsingleton_iff_eq_bot]
  exact intervalSpace_of_not_mem k h

/-! ### Canonical inclusions and projections -/

theorem intervalSpace_le_of_le_left {a ℓ d : Fin n} (h : a ≤ ℓ) (i : Fin n) :
    intervalSpace k ℓ d i ≤ intervalSpace k a d i := by
  unfold intervalSpace
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd ⟨h.trans h1.1, h1.2⟩ h2
  · exact bot_le
  · exact le_rfl

theorem coe_inclusionOrZero_left {a ℓ d : Fin n} (h : a ≤ ℓ) (i : Fin n)
    (x : intervalSpace k ℓ d i) :
    ((inclusionOrZero k (intervalSpace k ℓ d i) (intervalSpace k a d i) x : intervalSpace k a d i) : k)
      = (x : k) := by
  rw [coe_inclusionOrZero, if_pos (intervalSpace_le_of_le_left k h i)]

/-- The canonical inclusion `M_{ℓ,d} ⟶ M_{a,d}` for `a ≤ ℓ`: a suffix is a
subrepresentation. -/
def intervalIncl {a ℓ : Fin n} (d : Fin n) (h : a ≤ ℓ) : interval k ℓ d ⟶ interval k a d where
  app i := FGModuleCat.ofHom (inclusionOrZero k (intervalSpace k ℓ d i) (intervalSpace k a d i))
  naturality {i j} f := by
    apply FGModuleCat.hom_ext
    refine LinearMap.ext fun (x : intervalSpace k ℓ d i) => ?_
    apply Subtype.ext
    change ((inclusionOrZero k _ _ (inclusionOrZero k _ _ x) : intervalSpace k a d j) : k) =
      ((inclusionOrZero k _ _ (inclusionOrZero k _ _ x) : intervalSpace k a d j) : k)
    rw [coe_inclusionOrZero_left k h, coe_intervalMap k (leOfHom f), coe_intervalMap k (leOfHom f),
      coe_inclusionOrZero_left k h]

/-- The value in `k` of the projection `M_{a,d} → M_{a,ℓ}` at a vertex `i`. -/
theorem coe_inclusionOrZero_right {a ℓ d : Fin n} (h : ℓ ≤ d) (i : Fin n)
    (x : intervalSpace k a d i) :
    ((inclusionOrZero k (intervalSpace k a d i) (intervalSpace k a ℓ i) x : intervalSpace k a ℓ i) : k)
      = if i ≤ ℓ then (x : k) else 0 := by
  rw [coe_inclusionOrZero]
  by_cases hi : a ≤ i ∧ i ≤ d
  · by_cases hil : i ≤ ℓ
    · rw [if_pos hil, if_pos]
      unfold intervalSpace
      rw [if_pos hi, if_pos ⟨hi.1, hil⟩]
    · rw [if_neg hil, if_neg]
      unfold intervalSpace
      rw [if_pos hi, if_neg (fun h' => hil h'.2)]
      intro hle
      have := hle (Submodule.mem_top (x := (1 : k)))
      rw [Submodule.mem_bot] at this
      exact one_ne_zero this
  · rw [coe_eq_zero_of_not_mem k hi x]
    split_ifs <;> rfl

/-- The canonical projection `M_{a,d} ⟶ M_{a,ℓ}` for `ℓ ≤ d`: a prefix is a
quotient representation. -/
def intervalProj (a : Fin n) {ℓ d : Fin n} (h : ℓ ≤ d) : interval k a d ⟶ interval k a ℓ where
  app i := FGModuleCat.ofHom (inclusionOrZero k (intervalSpace k a d i) (intervalSpace k a ℓ i))
  naturality {i j} f := by
    apply FGModuleCat.hom_ext
    refine LinearMap.ext fun (x : intervalSpace k a d i) => ?_
    apply Subtype.ext
    change ((inclusionOrZero k _ _ (inclusionOrZero k _ _ x) : intervalSpace k a ℓ j) : k) =
      ((inclusionOrZero k _ _ (inclusionOrZero k _ _ x) : intervalSpace k a ℓ j) : k)
    rw [coe_inclusionOrZero_right k h, coe_intervalMap k (leOfHom f), coe_intervalMap k (leOfHom f),
      coe_inclusionOrZero_right k h]
    by_cases hjl : j ≤ ℓ
    · rw [if_pos hjl, if_pos hjl, if_pos (hjl.trans h), if_pos ((leOfHom f).trans hjl)]
    · rw [if_neg hjl, if_neg hjl]

end LinearQuiver

end PretorsionImageClosed
