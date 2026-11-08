module

public import PretorsionImageClosed.Gandhi.Delta
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-!
# Column sums

The two sums over the choices in a new column, evaluated by induction on the
set `R` of candidate rows (a finite set in a linear order).

* `psi R` (Lemma 7.3): the sum over subsets `Cont ⊆ R` of continued rows and
  admissible column cutoffs; it equals `Δ_q(x^{|R| + 1})`.
* `theta R` (equation (8.5)): the sum over subsets `J ⊆ R` of admissible
  starts, weighted by the number of admissible starts of the extension; it
  equals `x^{|R| + 1} + q x² Δ_q(x^{|R|})`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PretorsionImageClosed.Statement

open Polynomial Finset

variable {ι : Type*} [LinearOrder ι]

/-! ### The pretorsion column sum -/

/-- The weight of the choice of continued rows `Cont ⊆ R`, summed over the admissible
column cutoffs: `α = 0`, or `α = e + 1` for a continued row `e` all of whose predecessors
in `R` are continued. -/
def psiTerm (R Cont : Finset ι) : Rq[X] :=
  X ^ Cont.card * (C (q ^ Cont.card) +
    ∑ e ∈ Cont.filter (fun e => ∀ a ∈ R, a < e → a ∈ Cont),
      C (q ^ (Cont.filter (fun a => e < a)).card))

/-- The sum over the column extensions above `R` (Lemma 7.3, Step 1). -/
def psi (R : Finset ι) : Rq[X] := ∑ Cont ∈ R.powerset, psiTerm R Cont

theorem psi_empty : psi (∅ : Finset ι) = 1 := by
  simp [psi, psiTerm]

theorem psiTerm_insert_of_subset {r : ι} {R Cont : Finset ι} (hr : ∀ x ∈ R, x < r)
    (hCont : Cont ⊆ R) : psiTerm (insert r R) Cont = psiTerm R Cont := by
  unfold psiTerm
  congr 3
  apply Finset.filter_congr
  intro e he
  constructor
  · intro h a ha hae
    exact h a (Finset.mem_insert_of_mem ha) hae
  · intro h a ha hae
    rcases Finset.mem_insert.1 ha with rfl | ha'
    · exact absurd hae (not_lt.2 (hr e (hCont he)).le)
    · exact h a ha' hae

theorem psiTerm_insert_insert {r : ι} {R Cont : Finset ι} (hr : ∀ x ∈ R, x < r)
    (hCont : Cont ⊆ R) :
    psiTerm (insert r R) (insert r Cont) =
      X * (C q * psiTerm R Cont + if Cont = R then X ^ R.card else 0) := by
  have hrR : r ∉ R := fun h => lt_irrefl r (hr r h)
  have hrC : r ∉ Cont := fun h => hrR (hCont h)
  have hlt : ∀ e ∈ Cont, e < r := fun e he => hr e (hCont he)
  -- the filtered set of admissible pivots
  have hfilter : (insert r Cont).filter (fun e => ∀ a ∈ insert r R, a < e → a ∈ insert r Cont) =
      (if Cont = R then insert r (Cont.filter (fun e => ∀ a ∈ R, a < e → a ∈ Cont))
        else Cont.filter (fun e => ∀ a ∈ R, a < e → a ∈ Cont)) := by
    rw [Finset.filter_insert]
    have hsame : Cont.filter (fun e => ∀ a ∈ insert r R, a < e → a ∈ insert r Cont) =
        Cont.filter (fun e => ∀ a ∈ R, a < e → a ∈ Cont) := by
      apply Finset.filter_congr
      intro e he
      constructor
      · intro h a ha hae
        rcases Finset.mem_insert.1 (h a (Finset.mem_insert_of_mem ha) hae) with rfl | h'
        · exact absurd hae (not_lt.2 (hlt e he).le)
        · exact h'
      · intro h a ha hae
        rcases Finset.mem_insert.1 ha with rfl | ha'
        · exact absurd hae (not_lt.2 (hlt e he).le)
        · exact Finset.mem_insert_of_mem (h a ha' hae)
    rw [hsame]
    by_cases hCR : Cont = R
    · rw [if_pos hCR, if_pos]
      intro a ha _
      rcases Finset.mem_insert.1 ha with rfl | ha'
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (hCR ▸ ha')
    · rw [if_neg hCR, if_neg]
      intro h
      apply hCR
      apply Finset.Subset.antisymm hCont
      intro a ha
      rcases Finset.mem_insert.1 (h a (Finset.mem_insert_of_mem ha) (hr a ha)) with rfl | h'
      · exact absurd ha hrR
      · exact h'
  -- the count of continued rows after a pivot
  have hcount : ∀ e ∈ Cont, ((insert r Cont).filter (fun a => e < a)).card =
      (Cont.filter (fun a => e < a)).card + 1 := by
    intro e he
    rw [Finset.filter_insert, if_pos (hlt e he), Finset.card_insert_of_notMem]
    intro h
    exact hrC (Finset.mem_filter.1 h).1
  have hcount_r : ((insert r Cont).filter (fun a => r < a)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro a ha
    rcases Finset.mem_insert.1 ha with rfl | ha'
    · exact lt_irrefl _
    · exact not_lt.2 (hlt a ha').le
  unfold psiTerm
  rw [hfilter, Finset.card_insert_of_notMem hrC]
  have hnotmem : r ∉ Cont.filter (fun e => ∀ a ∈ R, a < e → a ∈ Cont) :=
    fun h => hrC (Finset.mem_filter.1 h).1
  by_cases hCR : Cont = R
  · rw [if_pos hCR, if_pos hCR, Finset.sum_insert hnotmem, hcount_r,
      Finset.sum_congr rfl (fun e he => by rw [hcount e (Finset.mem_filter.1 he).1])]
    subst hCR
    simp only [pow_zero, map_one, pow_succ, map_mul, Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun e _ => by rw [mul_comm (C (q ^ _)) (C q)])]
    rw [← Finset.mul_sum]
    ring
  · rw [if_neg hCR, if_neg hCR,
      Finset.sum_congr rfl (fun e he => by rw [hcount e (Finset.mem_filter.1 he).1])]
    simp only [pow_succ, map_mul, Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun e _ => by rw [mul_comm (C (q ^ _)) (C q)])]
    rw [← Finset.mul_sum]
    ring

theorem psi_insert_max {r : ι} {R : Finset ι} (hr : ∀ x ∈ R, x < r) :
    psi (insert r R) = U * psi R + X ^ (R.card + 1) := by
  have hrR : r ∉ R := fun h => lt_irrefl r (hr r h)
  unfold psi
  rw [Finset.sum_powerset_insert hrR]
  rw [Finset.sum_congr rfl (fun Cont hCont =>
    psiTerm_insert_of_subset hr (Finset.mem_powerset.1 hCont))]
  rw [Finset.sum_congr rfl (fun Cont hCont =>
    psiTerm_insert_insert hr (Finset.mem_powerset.1 hCont))]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq'
    R.powerset R (fun _ => X ^ R.card), if_pos (Finset.mem_powerset.2 (Finset.Subset.refl _))]
  ring

/-- Lemma 7.3: `psi R = Δ_q(x^{|R| + 1})`. -/
theorem psi_eq_geomSum (R : Finset ι) : psi R = geomSum R.card := by
  induction R using Finset.induction_on_max with
  | empty => rw [psi_empty, Finset.card_empty, geomSum_zero]
  | insert r R hr ih =>
    have hrR : r ∉ R := fun h => lt_irrefl r (hr r h)
    rw [psi_insert_max hr, ih, Finset.card_insert_of_notMem hrR, geomSum_succ]

/-! ### The image-closed column sum -/

/-- The number of admissible starts after adjoining the intervals `[a, d]`, `a ∈ J`, to a
family with admissible starts `R` (Lemma 8.4(2)): `|R| + 1` if `J = ∅`, and otherwise the
number of starts `≤ min J` plus `|J|`. -/
def admCount (R J : Finset ι) : ℕ :=
  (R.filter (fun c => ∀ j ∈ J, c ≤ j)).card + J.card + (if J = ∅ then 1 else 0)

/-- The weight of the choice `J ⊆ R`. -/
def thetaTerm (R J : Finset ι) : Rq[X] := C (q ^ J.card) * X ^ admCount R J

/-- The sum over the extensions of a family with admissible starts `R` (equation (8.5)). -/
def theta (R : Finset ι) : Rq[X] := ∑ J ∈ R.powerset, thetaTerm R J

theorem theta_empty : theta (∅ : Finset ι) = X := by
  simp [theta, thetaTerm, admCount]

theorem thetaTerm_insert_of_subset {r : ι} {R J : Finset ι} (hr : ∀ x ∈ R, x < r) (hJ : J ⊆ R) :
    thetaTerm (insert r R) J = thetaTerm R J * (if J = ∅ then X else 1) := by
  unfold thetaTerm admCount
  rw [Finset.filter_insert]
  by_cases hJe : J = ∅
  · subst hJe
    rw [if_pos (by simp), Finset.card_insert_of_notMem (fun h => lt_irrefl r (hr r (Finset.mem_filter.1 h).1))]
    simp only [if_true]
    ring
  · obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.2 hJe
    rw [if_neg (fun h => not_lt.2 (h j hj) (hr j (hJ hj)))]
    simp only [if_neg hJe]
    ring

theorem thetaTerm_insert_insert {r : ι} {R J : Finset ι} (hr : ∀ x ∈ R, x < r) (hJ : J ⊆ R) :
    thetaTerm (insert r R) (insert r J) = C q * X * thetaTerm R J := by
  have hrR : r ∉ R := fun h => lt_irrefl r (hr r h)
  have hrJ : r ∉ J := fun h => hrR (hJ h)
  unfold thetaTerm admCount
  have hne : insert r J ≠ ∅ := Finset.insert_ne_empty _ _
  rw [if_neg hne, Finset.card_insert_of_notMem hrJ, Finset.filter_insert]
  have hfilter : R.filter (fun c => ∀ j ∈ insert r J, c ≤ j) = R.filter (fun c => ∀ j ∈ J, c ≤ j) := by
    apply Finset.filter_congr
    intro c hc
    constructor
    · intro h j hj
      exact h j (Finset.mem_insert_of_mem hj)
    · intro h j hj
      rcases Finset.mem_insert.1 hj with rfl | hj'
      · exact (hr c hc).le
      · exact h j hj'
  rw [hfilter]
  by_cases hJe : J = ∅
  · subst hJe
    rw [if_pos (by simp), Finset.card_insert_of_notMem (fun h => hrR (Finset.mem_filter.1 h).1)]
    simp only [if_true, Finset.card_empty, pow_zero, map_one, pow_succ, map_mul]
    ring
  · obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.2 hJe
    rw [if_neg (fun h => not_lt.2 (h j (Finset.mem_insert_of_mem hj)) (hr j (hJ hj))), if_neg hJe]
    simp only [pow_succ, map_mul]
    ring

theorem theta_insert_max {r : ι} {R : Finset ι} (hr : ∀ x ∈ R, x < r) :
    theta (insert r R) = U * theta R + (X - 1) * X ^ (R.card + 1) := by
  have hrR : r ∉ R := fun h => lt_irrefl r (hr r h)
  unfold theta
  rw [Finset.sum_powerset_insert hrR]
  rw [Finset.sum_congr rfl (fun J hJ => thetaTerm_insert_of_subset hr (Finset.mem_powerset.1 hJ))]
  rw [Finset.sum_congr rfl (fun J hJ => thetaTerm_insert_insert hr (Finset.mem_powerset.1 hJ))]
  rw [← Finset.mul_sum]
  have hsplit : ∑ J ∈ R.powerset, thetaTerm R J * (if J = ∅ then X else 1) =
      ∑ J ∈ R.powerset, thetaTerm R J + (X - 1) * thetaTerm R ∅ := by
    rw [Finset.sum_congr rfl (fun J _ => show thetaTerm R J * (if J = ∅ then X else 1) =
      thetaTerm R J + (if J = ∅ then (X - 1) * thetaTerm R J else 0) by split_ifs <;> ring)]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' R.powerset ∅,
      if_pos (Finset.mem_powerset.2 (Finset.empty_subset _))]
  rw [hsplit]
  have h0 : thetaTerm R ∅ = X ^ (R.card + 1) := by
    simp [thetaTerm, admCount]
  rw [h0]
  ring

/-- Equation (8.5): `theta R = x^{|R| + 1} + q x² Δ_q(x^{|R|})`. -/
theorem theta_eq (R : Finset ι) : theta R = X ^ (R.card + 1) + C q * X ^ 2 * deltaXPow R.card := by
  induction R using Finset.induction_on_max with
  | empty => rw [theta_empty]; simp [deltaXPow]
  | insert r R hr ih =>
    have hrR : r ∉ R := fun h => lt_irrefl r (hr r h)
    rw [theta_insert_max hr, ih, Finset.card_insert_of_notMem hrR]
    cases hR : R.card with
    | zero => simp [deltaXPow, geomSum_zero]; ring
    | succ m =>
      rw [deltaXPow_succ_succ]
      ring

end PretorsionImageClosed.Statement
