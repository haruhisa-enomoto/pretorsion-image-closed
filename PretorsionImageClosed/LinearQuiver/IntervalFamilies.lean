module

public import PretorsionImageClosed.LinearQuiver.ImageClosed
public import PretorsionImageClosed.LinearQuiver.Counting
public import PretorsionImageClosed.Gandhi.Delta

/-!
# Image-closed subcategories as interval families

By Theorem 5.5, the image-closed subcategories of `mod Λ_n` correspond to the
intersection-closed families of intervals `𝕀(C)` (Definition 5.4). This file
sets up the families as finite sets of pairs `(a, d)` with `a ≤ d` in `Fin n`
(`IntervalFamily`, `ClosedFamily`), the bijection with
`ImageClosedSubcategory` (`imageClosedEquiv`), and the weight
`x^{ρ_n(C)} q^{|ind C|}` in these terms (`fWeight`): `ρ_n` counts the intervals
ending at the last vertex and `|ind C|` is the size of the family.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PretorsionImageClosed

open CategoryTheory Limits Statement Polynomial Finset

namespace LinearQuiver

universe u

variable {k : Type u} [Field k] {n : ℕ}

/-- A family of intervals `[a, d]` in `{0, …, n - 1}`, as pairs `a ≤ d`. -/
@[ext]
structure IntervalFamily (n : ℕ) where
  /-- The set of pairs `(a, d)`. -/
  D : Finset (Fin n × Fin n)
  le_of_mem : ∀ p ∈ D, p.1 ≤ p.2

/-- Intersection-closed families (Definition 5.4). -/
def IntervalFamily.IsClosed (D : IntervalFamily n) : Prop :=
  ∀ a b c d : Fin n, (a, b) ∈ D.D → (c, d) ∈ D.D → max a c ≤ min b d → (max a c, min b d) ∈ D.D

/-- Intersection-closed interval families: `𝕀(C)` for `C ∈ L_im(Λ_n)`. -/
def ClosedFamily (n : ℕ) : Type := {D : IntervalFamily n // D.IsClosed}

open Classical in
/-- The interval family `𝕀(Z)` of a subcategory. -/
def familyOf (Z : Subcategory (Statement.LinRep k n)) : IntervalFamily n where
  D := univ.filter (fun p : Fin n × Fin n => p.1 ≤ p.2 ∧ Z.prop (interval k p.1 p.2))
  le_of_mem p hp := (Finset.mem_filter.1 hp).2.1

theorem mem_familyOf {Z : Subcategory (Statement.LinRep k n)} {p : Fin n × Fin n} :
    p ∈ (familyOf Z).D ↔ p.1 ≤ p.2 ∧ Z.prop (interval k p.1 p.2) := by
  simp [familyOf]

/-- The subcategory `add` of the intervals of a family. -/
def IntervalFamily.subcategory (D : IntervalFamily n) : Subcategory (Statement.LinRep k n) :=
  ofIntervals (fun a d => (a, d) ∈ D.D)

theorem IntervalFamily.prop_interval_iff (D : IntervalFamily n) {a d : Fin n} (had : a ≤ d) :
    (D.subcategory (k := k)).prop (interval k a d) ↔ (a, d) ∈ D.D :=
  ofIntervals_prop_interval _ had

theorem familyOf_isClosed {Z : Subcategory (Statement.LinRep k n)} (hZ : Z.IsImageClosed) :
    (familyOf (k := k) Z).IsClosed := by
  intro a b c d hab hcd hmin
  rw [mem_familyOf] at hab hcd ⊢
  exact ⟨hmin, intersectionClosed_of_isImageClosed Z hZ a b c d hab.1 hcd.1 hab.2 hcd.2 hmin⟩

theorem IntervalFamily.IsClosed.isImageClosed {D : IntervalFamily n} (hD : D.IsClosed) :
    (D.subcategory (k := k)).IsImageClosed := by
  apply isImageClosed_of_intersectionClosed
  intro a b c d hab hcd ha hc hmin
  rw [D.prop_interval_iff hab] at ha
  rw [D.prop_interval_iff hcd] at hc
  rw [D.prop_interval_iff hmin]
  exact hD a b c d ha hc hmin

theorem familyOf_subcategory (D : IntervalFamily n) : familyOf (D.subcategory (k := k)) = D := by
  ext p
  rw [mem_familyOf]
  constructor
  · rintro ⟨h1, h2⟩
    exact (D.prop_interval_iff h1).1 h2
  · intro h
    exact ⟨D.le_of_mem p h, (D.prop_interval_iff (D.le_of_mem p h)).2 h⟩

theorem subcategory_familyOf (Z : Subcategory (Statement.LinRep k n)) :
    (familyOf Z).subcategory = Z := by
  apply subcategory_ext_intervals
  intro a d had
  rw [IntervalFamily.prop_interval_iff _ had, mem_familyOf]
  exact ⟨fun h => h.2, fun h => ⟨had, h⟩⟩

/-- Theorem 5.5 as a bijection: image-closed subcategories of `mod Λ_n` correspond to
intersection-closed interval families. -/
def imageClosedEquiv : ImageClosedSubcategory k n ≃ ClosedFamily n where
  toFun Z := ⟨familyOf Z.1, familyOf_isClosed Z.2⟩
  invFun D := ⟨D.1.subcategory, D.2.isImageClosed⟩
  left_inv Z := Subtype.ext (subcategory_familyOf Z.1)
  right_inv D := Subtype.ext (familyOf_subcategory D.1)

/-! ### Weights -/

/-- The number of intervals of the family ending at the last vertex: `ρ_n`. -/
def IntervalFamily.lastCount (D : IntervalFamily n) : ℕ :=
  (D.D.filter (fun p => p.2.val + 1 = n)).card

theorem lastCount_succ {m : ℕ} (D : IntervalFamily (m + 1)) :
    D.lastCount = (univ.filter (fun a : Fin (m + 1) => (a, Fin.last m) ∈ D.D)).card := by
  unfold IntervalFamily.lastCount
  refine Finset.card_bij' (fun p _ => p.1) (fun a _ => (a, Fin.last m)) ?_ ?_ ?_ ?_
  · intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_filter.1 hp
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have : p.2 = Fin.last m := Fin.ext (by rw [Fin.val_last]; omega)
    rw [← this]
    exact hp1
  · intro a ha
    rw [Finset.mem_filter] at ha ⊢
    exact ⟨ha.2, by simp⟩
  · intro p hp
    obtain ⟨-, hp2⟩ := Finset.mem_filter.1 hp
    have : p.2 = Fin.last m := Fin.ext (by rw [Fin.val_last]; omega)
    exact Prod.ext rfl this.symm
  · intro a _
    rfl

theorem rho_subcategory_family (D : IntervalFamily n) :
    rho (D.subcategory (k := k)).prop = D.lastCount := by
  cases n with
  | zero =>
    rw [rho_zero]
    unfold IntervalFamily.lastCount
    symm
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro p _
    exact p.1.elim0
  | succ m =>
    rw [rho_eq, lastCount_succ]
    apply Nat.subtype_card
    intro a
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨-, h⟩
      exact (D.prop_interval_iff (Fin.le_last a)).2 h
    · intro h
      exact ⟨Finset.mem_univ _, (D.prop_interval_iff (Fin.le_last a)).1 h⟩

theorem indCard_subcategory_family (D : IntervalFamily n) :
    indCard (D.subcategory (k := k)).prop = D.D.card := by
  rw [indCard_eq]
  apply Nat.subtype_card
  intro p
  constructor
  · intro h
    exact ⟨D.le_of_mem p h, (D.prop_interval_iff (D.le_of_mem p h)).2 h⟩
  · rintro ⟨h1, h2⟩
    exact (D.prop_interval_iff h1).1 h2

/-- The weight `x^{ρ_n} q^{|ind|}` of an intersection-closed family. -/
def fWeight (D : ClosedFamily n) : Rq[X] := X ^ D.1.lastCount * C (q ^ D.1.D.card)

theorem imageClosedWeight_eq (Z : ImageClosedSubcategory k n) :
    imageClosedWeight k n Z = fWeight (imageClosedEquiv Z) := by
  show X ^ rho Z.1.prop * C (q ^ indCard Z.1.prop) =
    X ^ (familyOf Z.1).lastCount * C (q ^ (familyOf Z.1).D.card)
  conv_lhs => rw [← subcategory_familyOf Z.1]
  rw [rho_subcategory_family, indCard_subcategory_family]

instance : Finite (IntervalFamily n) :=
  Finite.of_injective IntervalFamily.D (fun _ _ h => IntervalFamily.ext h)

instance : Finite (ClosedFamily n) := Subtype.finite

instance : Fintype (ClosedFamily n) := Fintype.ofFinite _

/-- `L_im(Λ_n)` is finite. -/
instance : Finite (ImageClosedSubcategory k n) := Finite.of_equiv _ (imageClosedEquiv (k := k) (n := n)).symm

instance : Fintype (ImageClosedSubcategory k n) := Fintype.ofFinite _

theorem finsum_imageClosedWeight :
    ∑ᶠ Z : ImageClosedSubcategory k n, imageClosedWeight k n Z = ∑ D : ClosedFamily n, fWeight D := by
  rw [finsum_eq_sum_of_fintype, Finset.sum_congr rfl (fun Z _ => imageClosedWeight_eq Z)]
  exact Fintype.sum_equiv imageClosedEquiv _ _ (fun _ => rfl)

end LinearQuiver

end PretorsionImageClosed
