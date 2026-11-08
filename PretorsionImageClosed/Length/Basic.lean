module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts

/-!
# Length functions on abelian categories

The manuscript works in `mod Λ`, where every object has finite length, and uses
this through finiteness arguments: traces are finite sums of images, rejects
finite intersections of kernels (Lemma 2.9), and every module is a finite direct
sum of indecomposables. We package what is needed as a *length function*: a
natural number attached to each object which vanishes exactly on zero objects
and decreases strictly along non-invertible monomorphisms and epimorphisms.
Both target categories, finite-dimensional modules over a finite-dimensional
algebra and representations of the linear quiver, carry one.

From this we derive that every nonempty set of subobjects of an object has
maximal and minimal elements, which replaces Lemma 2.9.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PretorsionImageClosed

open CategoryTheory Limits

/-- A length function on a category with zero morphisms: `length X = 0` exactly
for zero objects, and `length` decreases strictly along monomorphisms and
epimorphisms that are not isomorphisms. -/
class HasLength (C : Type*) [Category C] [HasZeroMorphisms C] where
  /-- The length of an object. -/
  length : C → ℕ
  length_eq_zero_iff : ∀ X : C, length X = 0 ↔ IsZero X
  length_eq_of_iso : ∀ {X Y : C}, (X ≅ Y) → length X = length Y
  length_lt_of_mono : ∀ {X Y : C} (f : X ⟶ Y), Mono f → ¬ IsIso f → length X < length Y
  length_lt_of_epi : ∀ {X Y : C} (f : X ⟶ Y), Epi f → ¬ IsIso f → length Y < length X

export HasLength (length)

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasLength C]

theorem length_eq_zero_iff (X : C) : length X = 0 ↔ IsZero X := HasLength.length_eq_zero_iff X

theorem length_pos_iff (X : C) : 0 < length X ↔ ¬ IsZero X := by
  rw [Nat.pos_iff_ne_zero, Ne, length_eq_zero_iff]

theorem IsZero.length_eq_zero {X : C} (h : IsZero X) : length X = 0 := (length_eq_zero_iff X).2 h

theorem length_pos_of_not_isZero {X : C} (h : ¬ IsZero X) : 0 < length X := (length_pos_iff X).2 h

theorem length_eq_of_iso {X Y : C} (e : X ≅ Y) : length X = length Y :=
  HasLength.length_eq_of_iso e

theorem length_lt_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] (h : ¬ IsIso f) : length X < length Y :=
  HasLength.length_lt_of_mono f inferInstance h

theorem length_lt_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] (h : ¬ IsIso f) : length Y < length X :=
  HasLength.length_lt_of_epi f inferInstance h

theorem length_le_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] : length X ≤ length Y := by
  by_cases h : IsIso f
  · exact (length_eq_of_iso (asIso f)).le
  · exact (length_lt_of_mono f h).le

theorem length_le_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] : length Y ≤ length X := by
  by_cases h : IsIso f
  · exact (length_eq_of_iso (asIso f)).ge
  · exact (length_lt_of_epi f h).le

theorem isIso_of_mono_of_length_le {X Y : C} (f : X ⟶ Y) [Mono f] (h : length Y ≤ length X) :
    IsIso f := by
  by_contra hf
  exact absurd (length_lt_of_mono f hf) (not_lt.2 h)

theorem isIso_of_epi_of_length_le {X Y : C} (f : X ⟶ Y) [Epi f] (h : length X ≤ length Y) :
    IsIso f := by
  by_contra hf
  exact absurd (length_lt_of_epi f hf) (not_lt.2 h)

/-! ### Subobjects -/

section Subobject

variable {X : C} (S : Subobject X)

theorem length_subobject_le : length (S : C) ≤ length X := length_le_of_mono S.arrow

theorem length_le_of_subobject_le {S T : Subobject X} (h : S ≤ T) : length (S : C) ≤ length (T : C) :=
  length_le_of_mono (Subobject.ofLE S T h)

/-- Two nested subobjects of the same length coincide. -/
theorem Subobject.eq_of_le_of_length_le {S T : Subobject X} (h : S ≤ T)
    (hl : length (T : C) ≤ length (S : C)) : S = T := by
  have : IsIso (Subobject.ofLE S T h) := isIso_of_mono_of_length_le _ hl
  refine le_antisymm h (Subobject.le_of_comm (inv (Subobject.ofLE S T h)) ?_)
  rw [IsIso.inv_comp_eq, Subobject.ofLE_arrow]

theorem Subobject.lt_length_of_lt {S T : Subobject X} (h : S < T) :
    length (S : C) < length (T : C) := by
  by_contra hl
  exact h.ne (Subobject.eq_of_le_of_length_le h.le (not_lt.1 hl))

/-- Every nonempty set of subobjects contains a maximal element: one that is
not strictly below any other member. -/
theorem Subobject.exists_maximal_of_nonempty (s : Set (Subobject X)) (hs : s.Nonempty) :
    ∃ S ∈ s, ∀ T ∈ s, S ≤ T → S = T := by
  obtain ⟨S, hS, hmin⟩ :=
    (measure fun S : Subobject X => length X - length (S : C)).wf.has_min s hs
  refine ⟨S, hS, fun T hT hle => Subobject.eq_of_le_of_length_le hle ?_⟩
  have h1 := length_subobject_le S
  have h2 := length_subobject_le T
  have := hmin T hT
  change ¬ (length X - length (T : C) < length X - length (S : C)) at this
  omega

/-- Every nonempty set of subobjects contains a minimal element. -/
theorem Subobject.exists_minimal_of_nonempty (s : Set (Subobject X)) (hs : s.Nonempty) :
    ∃ S ∈ s, ∀ T ∈ s, T ≤ S → T = S := by
  obtain ⟨S, hS, hmin⟩ :=
    (measure fun S : Subobject X => length (S : C)).wf.has_min s hs
  refine ⟨S, hS, fun T hT hle => Subobject.eq_of_le_of_length_le hle ?_⟩
  have := hmin T hT
  change ¬ (length (T : C) < length (S : C)) at this
  exact not_lt.1 this

end Subobject

end PretorsionImageClosed
