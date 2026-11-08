module

public import PretorsionImageClosed.Biproducts.Basic
public import PretorsionImageClosed.LinearQuiver.Hom
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Every representation of the linear quiver is a direct sum of intervals

The structure theorem for representations of `1 → 2 → ⋯ → n` (the classical
fact stated after Definition 5.1 that the interval representations are the
indecomposables). The proof is elementary: for a nonzero representation `X`,
let `i₀` be the first vertex with `X(i₀) ≠ 0`, pick a nonzero vector `v` there
and let `d` be the last vertex to which `v` survives. The span of the images
of `v` is a copy of `M_{i₀,d}`, and a linear functional on `X(d)` with value
`1` on the image of `v` gives a retraction `X ⟶ M_{i₀,d}` (natural because
`X` vanishes before `i₀`). Hence `M_{i₀,d}` splits off, and induction on the
total dimension finishes the proof (`intervalSum`).

The predicate `IntervalSum X` records such a decomposition into iterated binary
direct sums of intervals.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PretorsionImageClosed

open CategoryTheory Limits

namespace LinearQuiver

universe u

variable {k : Type u} [Field k] {n : ℕ}

theorem interval_map_apply (c d : Fin n) {i j : Fin n} (f : i ⟶ j) (x : intervalSpace k c d i) :
    ((interval k c d).map f).hom.hom x =
      inclusionOrZero k (intervalSpace k c d i) (intervalSpace k c d j) x := rfl

/-! ### The images of a vector -/

section Split

variable (X : Statement.LinRep k n) (i₀ : Fin n) (v : X.obj i₀)

/-- The images of `v` along the quiver: `X(i₀ → j)(v)` for `j ≥ i₀`, zero for `j < i₀`. -/
def vmap (j : Fin n) : X.obj j :=
  if h : i₀ ≤ j then (X.map (homOfLE h)).hom.hom v else 0

theorem vmap_of_le {j : Fin n} (h : i₀ ≤ j) : vmap X i₀ v j = (X.map (homOfLE h)).hom.hom v := by
  unfold vmap
  rw [dif_pos h]

theorem vmap_of_not_le {j : Fin n} (h : ¬ i₀ ≤ j) : vmap X i₀ v j = 0 := by
  unfold vmap
  rw [dif_neg h]

theorem vmap_self : vmap X i₀ v i₀ = v := by
  rw [vmap_of_le X i₀ v le_rfl]
  change (X.map (𝟙 i₀)).hom.hom v = v
  rw [X.map_id]
  rfl

theorem map_vmap {i j : Fin n} (f : i ⟶ j) (hi : i₀ ≤ i) :
    (X.map f).hom.hom (vmap X i₀ v i) = vmap X i₀ v j := by
  rw [vmap_of_le X i₀ v hi, vmap_of_le X i₀ v (hi.trans (leOfHom f))]
  change ((X.map (homOfLE hi)) ≫ (X.map f)).hom.hom v = _
  rw [← X.map_comp, Subsingleton.elim (homOfLE hi ≫ f) (homOfLE (hi.trans (leOfHom f)))]

/-! ### The morphism from an interval determined by a vector -/

variable {X i₀ v} (d : Fin n)

/-- The linear map `M_{i₀,d}(j) → X(j)`, `x ↦ x • X(i₀ → j)(v)`. -/
def fromVectorLin (j : Fin n) : intervalSpace k i₀ d j →ₗ[k] X.obj j :=
  (LinearMap.toSpanSingleton k (X.obj j) (vmap X i₀ v j)).comp (intervalSpace k i₀ d j).subtype

theorem fromVectorLin_apply (j : Fin n) (x : intervalSpace k i₀ d j) :
    fromVectorLin (v := v) d j x = (x : k) • vmap X i₀ v j := rfl

/-- The morphism `M_{i₀,d} ⟶ X` sending the unit vector at `j` to `X(i₀ → j)(v)`,
for `d` beyond which `v` dies. -/
def fromVector (hd : ∀ j, d < j → vmap X i₀ v j = 0) : interval k i₀ d ⟶ X where
  app j := ConcreteCategory.ofHom (fromVectorLin (v := v) d j)
  naturality {i j} f := by
    apply FGModuleCat.hom_ext
    refine LinearMap.ext fun (x : intervalSpace k i₀ d i) => ?_
    change fromVectorLin (v := v) d j (((interval k i₀ d).map f).hom.hom x) =
      (X.map f).hom.hom (fromVectorLin (v := v) d i x)
    rw [fromVectorLin_apply, fromVectorLin_apply, interval_map_apply, map_smul]
    have hc := coe_intervalMap k (a := i₀) (d := d) (leOfHom f) x
    rw [hc]
    by_cases hi : i₀ ≤ i
    · rw [map_vmap X i₀ v f hi]
      by_cases hjd : j ≤ d
      · rw [if_pos hjd]
      · rw [if_neg hjd, hd j (not_le.1 hjd)]
        simp
    · have hx : (x : k) = 0 := coe_eq_zero_of_not_mem k (fun h => hi h.1) x
      rw [hx]
      simp

theorem fromVector_app_apply (hd : ∀ j, d < j → vmap X i₀ v j = 0) (j : Fin n)
    (x : intervalSpace k i₀ d j) :
    ((fromVector d hd).app j).hom.hom x = (x : k) • vmap X i₀ v j := rfl

/-! ### The retraction determined by a functional -/

variable (ℓ : Module.Dual k (X.obj d))

/-- The linear map `X(j) → M_{i₀,d}(j)`, `x ↦ ℓ(X(j → d)(x))` for `j ∈ [i₀, d]`,
zero elsewhere. -/
def toIntervalLin (j : Fin n) : X.obj j →ₗ[k] intervalSpace k i₀ d j := by
  classical
  exact if h : i₀ ≤ j ∧ j ≤ d then
    (ℓ.comp (X.map (homOfLE h.2)).hom.hom).codRestrict (intervalSpace k i₀ d j)
      (fun x => by rw [intervalSpace_of_mem k h]; exact Submodule.mem_top)
  else 0

theorem toIntervalLin_apply_of_mem {j : Fin n} (h : i₀ ≤ j ∧ j ≤ d) (x : X.obj j) :
    (toIntervalLin (i₀ := i₀) d ℓ j x : k) = ℓ ((X.map (homOfLE h.2)).hom.hom x) := by
  unfold toIntervalLin
  rw [dif_pos h]
  rfl

theorem toIntervalLin_apply_of_not_mem {j : Fin n} (h : ¬ (i₀ ≤ j ∧ j ≤ d)) (x : X.obj j) :
    (toIntervalLin (i₀ := i₀) d ℓ j x : k) = 0 := by
  unfold toIntervalLin
  rw [dif_neg h]
  rfl

theorem eq_zero_of_lt_first (hfirst : ∀ i, i < i₀ → IsZero (X.obj i)) {i : Fin n} (hi : i < i₀)
    (x : X.obj i) : x = 0 := by
  have := (FGModuleCat.isZero_iff_subsingleton _).1 (hfirst i hi)
  exact Subsingleton.elim _ _

/-- The retraction `X ⟶ M_{i₀,d}` induced by a functional `ℓ` on `X(d)`, natural
because `X` vanishes at the vertices before `i₀`. -/
def toInterval (hfirst : ∀ i, i < i₀ → IsZero (X.obj i)) : X ⟶ interval k i₀ d where
  app j := ConcreteCategory.ofHom (toIntervalLin (i₀ := i₀) d ℓ j)
  naturality {i j} f := by
    apply FGModuleCat.hom_ext
    refine LinearMap.ext fun x => ?_
    apply Subtype.ext
    change (toIntervalLin (i₀ := i₀) d ℓ j ((X.map f).hom.hom x) : k) =
      (((interval k i₀ d).map f).hom.hom (toIntervalLin (i₀ := i₀) d ℓ i x) : k)
    rw [interval_map_apply, coe_intervalMap k (leOfHom f)]
    by_cases hjd : j ≤ d
    · rw [if_pos hjd]
      by_cases hj : i₀ ≤ j
      · rw [toIntervalLin_apply_of_mem d ℓ ⟨hj, hjd⟩]
        by_cases hi : i₀ ≤ i
        · rw [toIntervalLin_apply_of_mem d ℓ ⟨hi, (leOfHom f).trans hjd⟩]
          change ℓ ((X.map f ≫ X.map (homOfLE hjd)).hom.hom x) = _
          rw [← X.map_comp, Subsingleton.elim (f ≫ homOfLE hjd) (homOfLE ((leOfHom f).trans hjd))]
        · rw [toIntervalLin_apply_of_not_mem d ℓ (fun h => hi h.1),
            eq_zero_of_lt_first hfirst (not_le.1 hi) x, map_zero, map_zero, map_zero]
      · rw [toIntervalLin_apply_of_not_mem d ℓ (fun h => hj h.1),
          toIntervalLin_apply_of_not_mem d ℓ (fun h => hj (h.1.trans (leOfHom f)))]
    · rw [if_neg hjd, toIntervalLin_apply_of_not_mem d ℓ (fun h => hjd h.2)]

theorem toInterval_app_apply (hfirst : ∀ i, i < i₀ → IsZero (X.obj i)) (j : Fin n) (x : X.obj j) :
    ((toInterval d ℓ hfirst).app j).hom.hom x = toIntervalLin (i₀ := i₀) d ℓ j x := rfl

/-- `ℓ` with `ℓ(X(i₀ → d)(v)) = 1` makes `toInterval` a retraction of `fromVector`. -/
theorem fromVector_comp_toInterval (hd : ∀ j, d < j → vmap X i₀ v j = 0)
    (hfirst : ∀ i, i < i₀ → IsZero (X.obj i)) (hℓ : ℓ (vmap X i₀ v d) = 1) :
    fromVector d hd ≫ toInterval d ℓ hfirst = 𝟙 _ := by
  ext j : 2
  apply FGModuleCat.hom_ext
  refine LinearMap.ext fun (x : intervalSpace k i₀ d j) => ?_
  apply Subtype.ext
  change (toIntervalLin (i₀ := i₀) d ℓ j (fromVectorLin (v := v) d j x) : k) = (x : k)
  rw [fromVectorLin_apply]
  by_cases hj : i₀ ≤ j ∧ j ≤ d
  · rw [toIntervalLin_apply_of_mem d ℓ hj, map_smul, map_vmap X i₀ v _ hj.1, map_smul, hℓ,
      smul_eq_mul, mul_one]
  · rw [toIntervalLin_apply_of_not_mem d ℓ hj, coe_eq_zero_of_not_mem k hj x]

end Split

/-! ### Nonzero intervals -/

theorem not_isZero_interval {a d : Fin n} (h : a ≤ d) : ¬ IsZero (interval k a d) := by
  intro hz
  have := hz.obj a
  rw [FGModuleCat.isZero_iff_subsingleton] at this
  change Subsingleton (intervalSpace k a d a) at this
  rw [Submodule.subsingleton_iff_eq_bot, intervalSpace_of_mem k ⟨le_rfl, h⟩] at this
  exact top_ne_bot this

/-- A functional taking the value `1` on a given nonzero vector. -/
theorem exists_dual_eq_one {V : Type*} [AddCommGroup V] [Module k V] {w : V} (hw : w ≠ 0) :
    ∃ ℓ : Module.Dual k V, ℓ w = 1 := by
  obtain ⟨f, hf, -⟩ := Submodule.exists_dual_map_eq_bot_of_notMem (p := (⊥ : Submodule k V))
    (x := w) (by rw [Submodule.mem_bot]; exact hw) inferInstance
  exact ⟨(f w)⁻¹ • f, by rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf]⟩

/-! ### Iterated decompositions into intervals -/

/-- `X` is an iterated binary direct sum of interval representations. -/
inductive IntervalSum : Statement.LinRep k n → Prop
  | zero {X : Statement.LinRep k n} (h : IsZero X) : IntervalSum X
  | step {X X' : Statement.LinRep k n} (a d : Fin n) (had : a ≤ d) (h' : IntervalSum X')
      (e : X ≅ interval k a d ⊞ X') : IntervalSum X

/-- Splitting off the interval through a vector at the first nonzero vertex. -/
theorem exists_iso_biprod_interval (X : Statement.LinRep k n) (hX : ¬ IsZero X) :
    ∃ (a d : Fin n) (_ : a ≤ d) (X' : Statement.LinRep k n),
      Nonempty (X ≅ interval k a d ⊞ X') := by
  classical
  -- the first nonzero vertex
  have hne : (Finset.univ.filter fun i : Fin n => ¬ IsZero (X.obj i)).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at h
    exact hX (Functor.isZero _ fun i => not_not.1 (h (Finset.mem_univ i)))
  set i₀ := (Finset.univ.filter fun i : Fin n => ¬ IsZero (X.obj i)).min' hne with hi₀
  have hi₀_mem := Finset.min'_mem _ hne
  rw [← hi₀, Finset.mem_filter] at hi₀_mem
  have hfirst : ∀ i, i < i₀ → IsZero (X.obj i) := by
    intro i hi
    by_contra h
    have := Finset.min'_le (Finset.univ.filter fun i : Fin n => ¬ IsZero (X.obj i)) i
      (Finset.mem_filter.2 ⟨Finset.mem_univ i, h⟩)
    rw [← hi₀] at this
    exact absurd hi (not_lt.2 this)
  -- a nonzero vector there
  have hnt : Nontrivial (X.obj i₀) := by
    rw [FGModuleCat.isZero_iff_subsingleton] at hi₀_mem
    exact not_subsingleton_iff_nontrivial.1 hi₀_mem.2
  obtain ⟨v, hv⟩ := exists_ne (0 : X.obj i₀)
  -- the last vertex to which `v` survives
  have hvi₀ : vmap X i₀ v i₀ ≠ 0 := by rw [vmap_self]; exact hv
  have hDne : (Finset.univ.filter fun j : Fin n => vmap X i₀ v j ≠ 0).Nonempty :=
    ⟨i₀, Finset.mem_filter.2 ⟨Finset.mem_univ _, hvi₀⟩⟩
  set d := (Finset.univ.filter fun j : Fin n => vmap X i₀ v j ≠ 0).max' hDne with hd_def
  have hd_mem := Finset.max'_mem _ hDne
  rw [← hd_def, Finset.mem_filter] at hd_mem
  have hi₀d : i₀ ≤ d := by
    have := Finset.le_max' (Finset.univ.filter fun j : Fin n => vmap X i₀ v j ≠ 0) i₀
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, hvi₀⟩)
    rwa [← hd_def] at this
  have hd : ∀ j, d < j → vmap X i₀ v j = 0 := by
    intro j hj
    by_contra h
    have := Finset.le_max' (Finset.univ.filter fun j : Fin n => vmap X i₀ v j ≠ 0) j
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
    rw [← hd_def] at this
    exact absurd hj (not_lt.2 this)
  -- a functional with value `1` on `X(i₀ → d)(v)`
  obtain ⟨ℓ, hℓ⟩ := exists_dual_eq_one (k := k) hd_mem.2
  -- the splitting
  haveI : IsSplitMono (fromVector d hd) :=
    ⟨⟨⟨toInterval d ℓ hfirst, fromVector_comp_toInterval d ℓ hd hfirst hℓ⟩⟩⟩
  exact ⟨i₀, d, hi₀d, cokernel (fromVector d hd), ⟨isoBiprodCokernelOfIsSplitMono (fromVector d hd)⟩⟩

/-- **Structure theorem.** Every representation of the linearly oriented quiver
is an iterated direct sum of interval representations. -/
theorem intervalSum (X : Statement.LinRep k n) : IntervalSum X := by
  suffices h : ∀ m, ∀ Y : Statement.LinRep k n, length Y = m → IntervalSum Y from h _ X rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro Y hY
    by_cases hz : IsZero Y
    · exact IntervalSum.zero hz
    obtain ⟨a, d, had, Y', ⟨e⟩⟩ := exists_iso_biprod_interval Y hz
    have hmono : Mono (biprod.inr ≫ e.inv : Y' ⟶ Y) := mono_comp _ _
    have hnotiso : ¬ IsIso (biprod.inr ≫ e.inv : Y' ⟶ Y) := by
      intro hiso
      have : IsIso (biprod.inr : Y' ⟶ interval k a d ⊞ Y') := by
        have h2 : (biprod.inr : Y' ⟶ interval k a d ⊞ Y') = (biprod.inr ≫ e.inv) ≫ e.hom := by
          simp
        rw [h2]
        infer_instance
      exact not_isZero_interval had (isZero_of_isIso_biprod_inr this)
    have hlt : length Y' < length Y := length_lt_of_mono _ hnotiso
    exact IntervalSum.step a d had (ih _ (hY ▸ hlt) Y' rfl) e

end LinearQuiver

end PretorsionImageClosed
