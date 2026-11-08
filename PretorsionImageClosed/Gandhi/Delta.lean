module

public import PretorsionImageClosed.Statement
import Mathlib.Tactic.LinearCombination

/-!
# The `q`-difference operator and the Gandhi polynomials

Elementary properties of the relation `IsDelta f g` (`g = Δ_q f`) in
`ℤ[q][x]`: linearity, uniqueness of `g`, the values on monomials
(`Δ_q(x^{m+1}) = Σ_{i ≤ m} x^i (1 + qx)^{m-i}`, equation (7.5)), and the
existence of `Δ_q f` for every `f`. Consequently the `q`-Gandhi polynomials
of both kinds exist and are unique (`gandhiFirst`, `gandhiSecond`).

The last lemma, `isDelta_X_mul_comp`, is the substitution identity used in
the proof of Theorem 8.5: for `G = Δ_q g`,
`Δ_q(x g(1 + qx)) = g(1 + qx) + q (1 + qx) G(1 + qx)`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PretorsionImageClosed.Statement

open Polynomial

/-- `U = 1 + q x`. -/
abbrev U : Rq[X] := 1 + C q * X

theorem one_add_C_sub_mul_X : (1 + C (q - 1) * X : Rq[X]) = U - X := by
  rw [C_sub, C_1]
  ring

/-! ### Linearity and uniqueness -/

theorem IsDelta.add {f g f' g' : Rq[X]} (h : IsDelta f g) (h' : IsDelta f' g') :
    IsDelta (f + f') (g + g') := by
  unfold IsDelta at *
  rw [add_mul, h, h', add_comp]
  ring

theorem IsDelta.C_mul {f g : Rq[X]} (c : Rq) (h : IsDelta f g) : IsDelta (C c * f) (C c * g) := by
  unfold IsDelta at *
  rw [mul_assoc, h, C_mul_comp]
  ring

theorem isDelta_zero : IsDelta (0 : Rq[X]) 0 := by
  unfold IsDelta
  simp

theorem isDelta_one : IsDelta (1 : Rq[X]) 0 := by
  unfold IsDelta
  simp

theorem IsDelta.sum {ι : Type*} (s : Finset ι) (f g : ι → Rq[X])
    (h : ∀ i ∈ s, IsDelta (f i) (g i)) : IsDelta (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isDelta_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem U_sub_X_ne_zero : (U - X : Rq[X]) ≠ 0 := by
  intro h
  have := congrArg (fun p : Rq[X] => p.coeff 0) h
  simp at this

theorem IsDelta.unique {f g g' : Rq[X]} (h : IsDelta f g) (h' : IsDelta f g') : g = g' := by
  unfold IsDelta at h h'
  rw [one_add_C_sub_mul_X] at h h'
  exact mul_right_cancel₀ U_sub_X_ne_zero (h.trans h'.symm)

/-! ### Monomials -/

/-- `Σ_{i ≤ m} x^i U^{m-i}`, which is `Δ_q(x^{m+1})` (equation (7.5)). -/
def geomSum (m : ℕ) : Rq[X] := ∑ i ∈ Finset.range (m + 1), X ^ i * U ^ (m - i)

theorem geomSum_zero : geomSum 0 = 1 := by
  simp [geomSum]

theorem geomSum_succ (m : ℕ) : geomSum (m + 1) = U * geomSum m + X ^ (m + 1) := by
  unfold geomSum
  rw [Finset.sum_range_succ, Finset.mul_sum, Nat.sub_self, pow_zero, mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have : m + 1 - i = (m - i) + 1 := by omega
  rw [this, pow_succ]
  ring

theorem geomSum_succ' (m : ℕ) : geomSum (m + 1) = X * geomSum m + U ^ (m + 1) := by
  unfold geomSum
  rw [Finset.sum_range_succ', Finset.mul_sum, pow_zero, one_mul, Nat.sub_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have : m + 1 - (i + 1) = m - i := by omega
  rw [this, pow_succ]
  ring

theorem geomSum_mul_sub (m : ℕ) : geomSum m * (U - X) = U ^ (m + 1) - X ^ (m + 1) := by
  induction m with
  | zero => rw [geomSum_zero]; ring
  | succ m ih =>
    rw [geomSum_succ, add_mul, mul_assoc, ih]
    ring

/-- `Δ_q(x^{m+1}) = Σ_{i ≤ m} x^i U^{m-i}` (equation (7.5)). -/
theorem isDelta_X_pow_succ (m : ℕ) : IsDelta (X ^ (m + 1)) (geomSum m) := by
  unfold IsDelta
  rw [one_add_C_sub_mul_X, geomSum_mul_sub, X_pow_comp]

/-- `Δ_q(x^m)`: `0` for `m = 0` and `geomSum (m - 1)` otherwise. -/
def deltaXPow : ℕ → Rq[X]
  | 0 => 0
  | m + 1 => geomSum m

theorem isDelta_X_pow (m : ℕ) : IsDelta (X ^ m) (deltaXPow m) := by
  cases m with
  | zero =>
    show IsDelta (X ^ 0) 0
    rw [pow_zero]
    exact isDelta_one
  | succ m => exact isDelta_X_pow_succ m

theorem deltaXPow_succ_succ (m : ℕ) : deltaXPow (m + 2) = X ^ (m + 1) + U * deltaXPow (m + 1) := by
  show geomSum (m + 1) = X ^ (m + 1) + U * geomSum m
  rw [geomSum_succ, add_comm]

/-- `Δ_q f` exists for every `f`. -/
theorem exists_isDelta (f : Rq[X]) : ∃ g, IsDelta f g := by
  induction f using Polynomial.induction_on' with
  | add p r hp hr =>
    obtain ⟨g, hg⟩ := hp
    obtain ⟨g', hg'⟩ := hr
    exact ⟨g + g', hg.add hg'⟩
  | monomial m c =>
    rw [← C_mul_X_pow_eq_monomial]
    exact ⟨C c * deltaXPow m, (isDelta_X_pow m).C_mul c⟩

/-! ### The Gandhi polynomials -/

/-- The `q`-Gandhi polynomials of the first kind, `B 1 = 1`, `B m = Δ_q(x² B (m-1))`
(with the irrelevant value `B 0 = 0`). -/
def gandhiFirst : ℕ → Rq[X]
  | 0 => 0
  | 1 => 1
  | m + 2 => Classical.choose (exists_isDelta (X ^ 2 * gandhiFirst (m + 1)))

theorem isGandhiFirst_gandhiFirst : IsGandhiFirst gandhiFirst := by
  refine ⟨rfl, fun m hm => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  exact Classical.choose_spec (exists_isDelta (X ^ 2 * gandhiFirst (m + 1)))

theorem IsGandhiFirst.eq {B B' : ℕ → Rq[X]} (hB : IsGandhiFirst B) (hB' : IsGandhiFirst B') :
    ∀ m, 1 ≤ m → B m = B' m := by
  intro m
  induction m with
  | zero => intro h; omega
  | succ m ih =>
    intro _
    cases m with
    | zero => rw [hB.1, hB'.1]
    | succ m =>
      have h1 := hB.2 (m + 2) (by omega)
      have h2 := hB'.2 (m + 2) (by omega)
      have hm : m + 2 - 1 = m + 1 := rfl
      rw [hm] at h1 h2
      rw [ih (by omega)] at h1
      exact h1.unique h2

/-- The `q`-Gandhi polynomials of the second kind, `C 1 = 1`,
`C m = (1 + qx) Δ_q(x C (m-1))` (with the irrelevant value `C 0 = 0`). -/
def gandhiSecond : ℕ → Rq[X]
  | 0 => 0
  | 1 => 1
  | m + 2 => U * Classical.choose (exists_isDelta (X * gandhiSecond (m + 1)))

theorem isGandhiSecond_gandhiSecond : IsGandhiSecond gandhiSecond := by
  refine ⟨rfl, fun m hm => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  exact ⟨_, Classical.choose_spec (exists_isDelta (X * gandhiSecond (m + 1))), rfl⟩

theorem IsGandhiSecond.eq {Cs Cs' : ℕ → Rq[X]} (hC : IsGandhiSecond Cs) (hC' : IsGandhiSecond Cs') :
    ∀ m, 1 ≤ m → Cs m = Cs' m := by
  intro m
  induction m with
  | zero => intro h; omega
  | succ m ih =>
    intro _
    cases m with
    | zero => rw [hC.1, hC'.1]
    | succ m =>
      obtain ⟨g, hg, hCg⟩ := hC.2 (m + 2) (by omega)
      obtain ⟨g', hg', hCg'⟩ := hC'.2 (m + 2) (by omega)
      have hm : m + 2 - 1 = m + 1 := rfl
      rw [hm] at hg hg'
      rw [ih (by omega)] at hg
      rw [hCg, hCg', hg.unique hg']

/-! ### The substitution identity of Theorem 8.5 -/

/-- For `G = Δ_q g`: `Δ_q(x · g(U)) = g(U) + q U · G(U)`, where `U = 1 + qx`. -/
theorem isDelta_X_mul_comp {g G : Rq[X]} (hG : IsDelta g G) :
    IsDelta (X * g.comp U) (g.comp U + C q * U * G.comp U) := by
  unfold IsDelta at *
  have hG' := congrArg (fun p : Rq[X] => p.comp U) hG
  simp only [mul_comp, add_comp, one_comp, C_comp, C_mul_comp, X_comp, sub_comp, comp_assoc] at hG'
  simp only [mul_comp, add_comp, one_comp, C_comp, C_mul_comp, X_comp, sub_comp, comp_assoc]
  rw [C_sub, C_1] at hG' ⊢
  linear_combination (1 + C q * X) * hG'

end PretorsionImageClosed.Statement
