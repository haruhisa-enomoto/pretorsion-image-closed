module

public import PretorsionImageClosed.LinearQuiver.CutoffCriterion
public import PretorsionImageClosed.LinearQuiver.Counting
public import PretorsionImageClosed.Gandhi.Delta

/-!
# Weights of pretorsion theories in cutoff coordinates

The weight `x^{ρ_n(T)} q^{|ind(T ∩ F)|}` of a pretorsion theory `(T_β, F_α)`
of `mod Λ_n` (Definition 7.1) in terms of the cutoffs: `ρ_n(T_β)` is the
number of rows `a` with `β a = n`, and `|ind(T_β ∩ F_α)|` is the number of
pairs `a ≤ d` with `d < β a` and `α d ≤ a`, counted column by column.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PretorsionImageClosed

open CategoryTheory Limits Statement Polynomial Finset

namespace LinearQuiver

universe u

variable {k : Type u} [Field k] {n : ℕ}

/-- The number of rows reaching the last column: `ρ_n(T_β)`. -/
def RowCutoff.rowsReaching (β : RowCutoff n) : ℕ := (univ.filter (fun a : Fin n => β.β a = n)).card

/-- The number of intervals of column `d` in `T_β ∩ F_α` (equation (7.2)). -/
def colCount (β : RowCutoff n) (α : ColCutoff n) (d : Fin n) : ℕ :=
  (univ.filter (fun a : Fin n => a ≤ d ∧ d.val < β.β a ∧ α.α d ≤ a.val)).card

/-- `|ind(T_β ∩ F_α)|`, summed over the columns. -/
def middleCount (β : RowCutoff n) (α : ColCutoff n) : ℕ := ∑ d, colCount β α d

/-- The weight `x^{ρ} q^{|ind|}` of a cutoff pair. -/
def cpWeight (p : CutoffPair n) : Rq[X] :=
  X ^ p.1.1.rowsReaching * C (q ^ middleCount p.1.1 p.1.2)

theorem rho_subcategory (β : RowCutoff n) :
    rho (β.subcategory (k := k)).prop = β.rowsReaching := by
  cases n with
  | zero =>
    rw [rho_zero]
    simp [RowCutoff.rowsReaching]
  | succ m =>
    rw [rho_eq, RowCutoff.rowsReaching]
    apply Nat.subtype_card
    intro a
    rw [Finset.mem_filter, β.prop_interval_iff (Fin.le_last a), Fin.val_last]
    have h1 := β.β_le a
    constructor
    · rintro ⟨-, h⟩
      omega
    · intro h
      exact ⟨Finset.mem_univ _, by omega⟩

theorem indCard_inf (β : RowCutoff n) (α : ColCutoff n) :
    indCard ((β.subcategory (k := k)).prop ⊓ α.subcategory.prop) = middleCount β α := by
  have h := indCard_eq (β.subcategory (k := k) ⊓ α.subcategory)
  rw [Subcategory.inf_prop] at h
  rw [h, Nat.subtype_card (univ.filter (fun p : Fin n × Fin n =>
    p.1 ≤ p.2 ∧ p.2.val < β.β p.1 ∧ α.α p.2 ≤ p.1.val)) ?_]
  · rw [Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]
    unfold middleCount colCount
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.card_filter]
  · intro p
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨-, h1, h2, h3⟩
      exact ⟨h1, (β.prop_interval_iff h1).2 h2, (α.prop_interval_iff h1).2 h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨Finset.mem_univ _, h1, (β.prop_interval_iff h1).1 h2, (α.prop_interval_iff h1).1 h3⟩

/-- The weight of a pretorsion theory is the weight of its cutoff pair. -/
theorem pretorsionWeight_eq (P : PretorsionTheory (Statement.LinRep k n)) :
    pretorsionWeight k n P = cpWeight (pretorsionEquiv P) := by
  have hT := rowCutoff_subcategory P.isPretorsionTheory.isQuotientClosed
  have hF := colCutoff_subcategory P.isPretorsionTheory.isSubobjectClosed
  show X ^ rho P.T.prop * C (q ^ indCard (P.T.prop ⊓ P.F.prop)) =
    X ^ (rowCutoff P.T).rowsReaching * C (q ^ middleCount (rowCutoff P.T) (colCutoff P.F))
  rw [← rho_subcategory (k := k), ← indCard_inf (k := k), hT, hF]

instance : Fintype (CutoffPair n) := Fintype.ofFinite _

instance : Fintype (PretorsionTheory (Statement.LinRep k n)) := Fintype.ofFinite _

theorem finsum_pretorsionWeight :
    ∑ᶠ P : PretorsionTheory (Statement.LinRep k n), pretorsionWeight k n P =
      ∑ p : CutoffPair n, cpWeight p := by
  rw [finsum_eq_sum_of_fintype, Finset.sum_congr rfl (fun P _ => pretorsionWeight_eq P)]
  exact Fintype.sum_equiv pretorsionEquiv _ _ (fun _ => rfl)

end LinearQuiver

end PretorsionImageClosed
