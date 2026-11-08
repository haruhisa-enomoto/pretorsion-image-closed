module

public import PretorsionImageClosed.LinearQuiver.IntervalSets

/-!
# Counting indecomposables of a subcategory of the linear quiver

The number `|ind C|` of isomorphism classes of indecomposable objects of a
subcategory `C` of `mod Λ_n` (`Statement.indCard`) is the number of intervals
`[a, d]` with `M_{a,d} ∈ C` (`indCard_eq`), and the statistic `ρ_n(C)` of
Definition 7.1 (`Statement.rho`) is the number of intervals `[a, n]` in `C`
(`rho_eq`). Both are proved by an explicit bijection between the isomorphism
classes of indecomposables of `C` and the intervals of `C`, using the
classification of indecomposables.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PretorsionImageClosed

open CategoryTheory Limits Statement

namespace LinearQuiver

universe u

variable {k : Type u} [Field k] {n : ℕ}

/-- The indecomposable objects of `C`, as a full subcategory. -/
abbrev IndObj (C : Subcategory (Statement.LinRep k n)) :=
  ObjectProperty.FullSubcategory (fun X : Statement.LinRep k n => C.prop X ∧ Indecomposable X)

/-- The intervals of `C`. -/
abbrev IntervalPairs (C : Subcategory (Statement.LinRep k n)) :=
  {p : Fin n × Fin n // p.1 ≤ p.2 ∧ C.prop (interval k p.1 p.2)}

variable (C : Subcategory (Statement.LinRep k n))

/-- The interval of an indecomposable object of `C`. -/
def pairOf (X : IndObj C) : IntervalPairs C :=
  ⟨((exists_iso_interval_of_indecomposable X.2.2).choose,
    (exists_iso_interval_of_indecomposable X.2.2).choose_spec.choose),
   (exists_iso_interval_of_indecomposable X.2.2).choose_spec.choose_spec.1,
   C.prop_of_iso (exists_iso_interval_of_indecomposable X.2.2).choose_spec.choose_spec.2.some X.2.1⟩

theorem pairOf_iso (X : IndObj C) :
    Nonempty (X.obj ≅ interval k (pairOf C X).1.1 (pairOf C X).1.2) :=
  (exists_iso_interval_of_indecomposable X.2.2).choose_spec.choose_spec.2

theorem pairOf_eq_of_iso {X Y : IndObj C} (e : X.obj ≅ Y.obj) : pairOf C X = pairOf C Y := by
  obtain ⟨e1⟩ := pairOf_iso C X
  obtain ⟨e2⟩ := pairOf_iso C Y
  have := (interval_iso_iff (pairOf C X).2.1 (pairOf C Y).2.1).1 ⟨e1.symm ≪≫ e ≪≫ e2⟩
  exact Subtype.ext (Prod.ext this.1 this.2)

/-- The indecomposable object of `C` attached to an interval of `C`. -/
def objOf (p : IntervalPairs C) : IndObj C :=
  ⟨interval k p.1.1 p.1.2, p.2.2, indecomposable_interval p.2.1⟩

theorem pairOf_objOf (p : IntervalPairs C) : pairOf C (objOf C p) = p := by
  obtain ⟨e⟩ := pairOf_iso C (objOf C p)
  have := (interval_iso_iff p.2.1 (pairOf C (objOf C p)).2.1).1 ⟨e⟩
  exact Subtype.ext (Prod.ext this.1.symm this.2.symm)

/-- Isomorphism classes of indecomposables of `C` correspond to intervals of `C`. -/
def skeletonEquiv : Quotient (isIsomorphicSetoid (IndObj C)) ≃ IntervalPairs C where
  toFun := Quotient.lift (pairOf C) (fun X Y ⟨e⟩ => pairOf_eq_of_iso C ((ObjectProperty.ι _).mapIso e))
  invFun p := Quotient.mk _ (objOf C p)
  left_inv := by
    rintro ⟨X⟩
    apply Quotient.sound
    exact ⟨ObjectProperty.isoMk _ ((pairOf_iso C X).some.symm)⟩
  right_inv p := pairOf_objOf C p

/-- `|ind C|` is the number of intervals of `C`. -/
theorem indCard_eq : indCard C.prop = Nat.card (IntervalPairs C) :=
  Nat.card_congr (skeletonEquiv C)

/-! ### The statistic `ρ` -/

section Rho

variable {m : ℕ} (D : Subcategory (Statement.LinRep k (m + 1)))

/-- The indecomposables of `D` with nonzero value at the last vertex. -/
abbrev LastObj :=
  ObjectProperty.FullSubcategory (fun X : Statement.LinRep k (m + 1) =>
    D.prop X ∧ Indecomposable X ∧ ∃ i : Fin (m + 1), i.val + 1 = m + 1 ∧ ¬ IsZero (X.obj i))

/-- The intervals of `D` ending at the last vertex. -/
abbrev LastPairs := {a : Fin (m + 1) // D.prop (interval k a (Fin.last m))}

theorem interval_obj_last_not_isZero_iff {a d : Fin (m + 1)} (had : a ≤ d) :
    (∃ i : Fin (m + 1), i.val + 1 = m + 1 ∧ ¬ IsZero ((interval k a d).obj i)) ↔ d = Fin.last m := by
  constructor
  · rintro ⟨i, hi, hz⟩
    have hil : i = Fin.last m := Fin.ext (by simp only [Fin.val_last]; omega)
    subst hil
    by_contra hd
    apply hz
    apply isZero_interval_obj_of_not_mem
    rintro ⟨-, hdl⟩
    exact hd (le_antisymm (Fin.le_last d) hdl)
  · rintro rfl
    refine ⟨Fin.last m, by simp, ?_⟩
    intro hz
    rw [FGModuleCat.isZero_iff_subsingleton] at hz
    change Subsingleton (intervalSpace k a (Fin.last m) (Fin.last m)) at hz
    rw [Submodule.subsingleton_iff_eq_bot, intervalSpace_of_mem k ⟨had, le_rfl⟩] at hz
    exact top_ne_bot hz

/-- The interval of an indecomposable with nonzero last value ends at the last vertex. -/
def lastOf (X : LastObj D) : LastPairs D :=
  ⟨(pairOf D ⟨X.obj, X.2.1, X.2.2.1⟩).1.1, by
    have hp := (pairOf D ⟨X.obj, X.2.1, X.2.2.1⟩).2
    obtain ⟨e⟩ := pairOf_iso D ⟨X.obj, X.2.1, X.2.2.1⟩
    have hd : (pairOf D ⟨X.obj, X.2.1, X.2.2.1⟩).1.2 = Fin.last m := by
      rw [← interval_obj_last_not_isZero_iff (k := k) hp.1]
      obtain ⟨i, hi, hz⟩ := X.2.2.2
      exact ⟨i, hi, fun h => hz (h.of_iso (e.app i))⟩
    rw [← hd]
    exact hp.2⟩

theorem lastOf_iso (X : LastObj D) : Nonempty (X.obj ≅ interval k (lastOf D X).1 (Fin.last m)) := by
  obtain ⟨e⟩ := pairOf_iso D ⟨X.obj, X.2.1, X.2.2.1⟩
  have hp := (pairOf D ⟨X.obj, X.2.1, X.2.2.1⟩).2
  have hd : (pairOf D ⟨X.obj, X.2.1, X.2.2.1⟩).1.2 = Fin.last m := by
    rw [← interval_obj_last_not_isZero_iff (k := k) hp.1]
    obtain ⟨i, hi, hz⟩ := X.2.2.2
    exact ⟨i, hi, fun h => hz (h.of_iso (e.app i))⟩
  rw [hd] at e
  exact ⟨e⟩

theorem lastOf_eq_of_iso {X Y : LastObj D} (e : X.obj ≅ Y.obj) : lastOf D X = lastOf D Y := by
  obtain ⟨e1⟩ := lastOf_iso D X
  obtain ⟨e2⟩ := lastOf_iso D Y
  have := (interval_iso_iff (Fin.le_last _) (Fin.le_last _)).1 ⟨e1.symm ≪≫ e ≪≫ e2⟩
  exact Subtype.ext this.1

/-- The indecomposable with nonzero last value attached to an interval ending at the
last vertex. -/
def lastObjOf (a : LastPairs D) : LastObj D :=
  ⟨interval k a.1 (Fin.last m), a.2, indecomposable_interval (Fin.le_last _),
    (interval_obj_last_not_isZero_iff (Fin.le_last _)).2 rfl⟩

theorem lastOf_lastObjOf (a : LastPairs D) : lastOf D (lastObjOf D a) = a := by
  obtain ⟨e⟩ := lastOf_iso D (lastObjOf D a)
  have := (interval_iso_iff (Fin.le_last _) (Fin.le_last _)).1 ⟨e⟩
  exact Subtype.ext this.1.symm

/-- Isomorphism classes of indecomposables of `D` with nonzero last value correspond
to intervals of `D` ending at the last vertex. -/
def lastSkeletonEquiv : Quotient (isIsomorphicSetoid (LastObj D)) ≃ LastPairs D where
  toFun := Quotient.lift (lastOf D) (fun X Y ⟨e⟩ => lastOf_eq_of_iso D ((ObjectProperty.ι _).mapIso e))
  invFun a := Quotient.mk _ (lastObjOf D a)
  left_inv := by
    rintro ⟨X⟩
    apply Quotient.sound
    exact ⟨ObjectProperty.isoMk _ ((lastOf_iso D X).some.symm)⟩
  right_inv a := lastOf_lastObjOf D a

/-- `ρ(D)` is the number of intervals of `D` ending at the last vertex. -/
theorem rho_eq : rho D.prop = Nat.card (LastPairs D) :=
  Nat.card_congr (lastSkeletonEquiv D)

end Rho

/-- For `n = 0` there are no vertices and `ρ = 0`. -/
theorem rho_zero (D : Subcategory (Statement.LinRep k 0)) : rho D.prop = 0 := by
  unfold rho
  have : IsEmpty (Skeleton (ObjectProperty.FullSubcategory (fun X : Statement.LinRep k 0 =>
      D.prop X ∧ Indecomposable X ∧ ∃ i : Fin 0, i.val + 1 = 0 ∧ ¬ IsZero (X.obj i)))) := by
    constructor
    rintro ⟨X⟩
    obtain ⟨i, -, -⟩ := X.2.2.2
    exact i.elim0
  exact Nat.card_of_isEmpty

end LinearQuiver

end PretorsionImageClosed
