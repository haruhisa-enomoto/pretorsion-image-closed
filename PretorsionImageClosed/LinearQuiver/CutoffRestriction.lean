module

public import PretorsionImageClosed.LinearQuiver.CutoffWeights
public import PretorsionImageClosed.Gandhi.ColumnSum

/-!
# Restriction and extension of cutoff pairs

Lemma 7.2 and Lemma 7.3 of the manuscript, in cutoff coordinates. A cutoff
pair on `n + 1` vertices restricts to a cutoff pair on the first `n`
vertices (`CutoffPair.restrict`). The pairs restricting to a given `p` are
parametrized by the set `Cont` of continued rows among the candidate rows
(the rows reaching column `n - 1`, together with the new row `n`) and an
admissible cutoff for the new column (`glue`, `exists_glue`). Summing the
weights over a fibre gives `q^{|ind|} · Δ_q(x^{ρ + 2})` (`fiber_sum`), so the
total weight `cpSum` satisfies `cpSum (n + 1) = Δ_q(x² · cpSum n)`
(`isDelta_cpSum`), and `cpSum n = B_{n+1}` (Theorem 7.5).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PretorsionImageClosed

open Statement Polynomial Finset

namespace LinearQuiver

variable {n : ℕ}

/-- Equality of cutoff pairs is decided classically. -/
noncomputable instance : DecidableEq (CutoffPair n) := Classical.decEq _

/-! ### Restriction -/

/-- Restriction of row cutoffs to the first `n` vertices. -/
def RowCutoff.restrict (β : RowCutoff (n + 1)) : RowCutoff n where
  β a := min (β.β a.castSucc) n
  le_β a := le_min (by simpa using β.le_β a.castSucc) a.isLt.le
  β_le _ := min_le_right _ _

/-- Restriction of column cutoffs to the first `n` vertices. -/
def ColCutoff.restrict (α : ColCutoff (n + 1)) : ColCutoff n where
  α d := α.α d.castSucc
  α_le d := by simpa using α.α_le d.castSucc

theorem criterion_restrict {β : RowCutoff (n + 1)} {α : ColCutoff (n + 1)} (h : Criterion β α) :
    Criterion β.restrict α.restrict := by
  intro d
  rcases h d.castSucc with h0 | ⟨e, he, hde, hprev⟩
  · exact Or.inl h0
  · right
    have hα := α.α_le d.castSucc
    simp only [Fin.val_castSucc] at hα hde
    have hed : e.val < n := by omega
    refine ⟨⟨e.val, hed⟩, he, ?_, ?_⟩
    · show d.val < min (β.β (Fin.castSucc ⟨e.val, hed⟩)) n
      have hcast : Fin.castSucc (⟨e.val, hed⟩ : Fin n) = e := Fin.ext rfl
      rw [hcast]
      exact lt_min hde d.isLt
    · intro a ha hβ
      have hβ' : min (β.β a.castSucc) n = d.val := hβ
      have hlt : a.castSucc < e := by
        rw [Fin.lt_def] at ha ⊢
        simpa using ha
      have := hprev a.castSucc hlt
      simp only [Fin.val_castSucc] at this
      have hd := d.isLt
      omega

/-- Restriction of cutoff pairs (Lemma 7.2). -/
def CutoffPair.restrict (x : CutoffPair (n + 1)) : CutoffPair n :=
  ⟨(x.1.1.restrict, x.1.2.restrict), criterion_restrict x.2⟩

/-! ### Candidate rows -/

/-- The row cutoffs of `p`, extended by the value `n` on the new row `n`. -/
def βext (p : CutoffPair n) : Fin (n + 1) → ℕ := Fin.snoc (α := fun _ => ℕ) p.1.1.β n

@[simp] theorem βext_castSucc (p : CutoffPair n) (a : Fin n) : βext p a.castSucc = p.1.1.β a :=
  Fin.snoc_castSucc _ _ _

@[simp] theorem βext_last (p : CutoffPair n) : βext p (Fin.last n) = n := Fin.snoc_last _ _

theorem βext_le (p : CutoffPair n) (a : Fin (n + 1)) : βext p a ≤ n := by
  induction a using Fin.lastCases with
  | last => simp
  | cast a => simp [p.1.1.β_le a]

theorem le_βext (p : CutoffPair n) (a : Fin (n + 1)) : a.val ≤ βext p a := by
  induction a using Fin.lastCases with
  | last => simp
  | cast a => simpa using p.1.1.le_β a

/-- The candidate rows: the rows reaching column `n - 1`, and the new row `n`. -/
def candRows (p : CutoffPair n) : Finset (Fin (n + 1)) := univ.filter (fun a => βext p a = n)

theorem mem_candRows {p : CutoffPair n} {a : Fin (n + 1)} : a ∈ candRows p ↔ βext p a = n := by
  simp [candRows]

theorem card_candRows (p : CutoffPair n) : (candRows p).card = p.1.1.rowsReaching + 1 := by
  unfold candRows RowCutoff.rowsReaching
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  simp

/-! ### Extension data -/

/-- The admissible cutoffs for the new column: `0`, or `e + 1` for a continued row `e` all of
whose predecessors among the candidate rows are continued (equation (6.5)). -/
def Allowed (p : CutoffPair n) (Cont : Finset (Fin (n + 1))) : Option (Fin (n + 1)) → Prop
  | none => True
  | some e => e ∈ Cont ∧ ∀ a ∈ candRows p, a < e → a ∈ Cont

/-- The column cutoff encoded by an option. -/
def colValue : Option (Fin (n + 1)) → ℕ
  | none => 0
  | some e => e.val + 1

theorem colValue_le (c : Option (Fin (n + 1))) : colValue c ≤ n + 1 := by
  cases c with
  | none => exact Nat.zero_le _
  | some e => exact e.isLt

/-- The row cutoffs of the extension: continued rows get the cutoff `n + 1`. -/
def glueRow (p : CutoffPair n) (Cont : Finset (Fin (n + 1))) : RowCutoff (n + 1) where
  β a := if a ∈ Cont then n + 1 else βext p a
  le_β a := by
    split_ifs with h
    · exact a.isLt.le
    · exact le_βext p a
  β_le a := by
    split_ifs with h
    · exact le_rfl
    · exact Nat.le_succ_of_le (βext_le p a)

/-- The column cutoffs of the extension. -/
def glueCol (p : CutoffPair n) (c : Option (Fin (n + 1))) : ColCutoff (n + 1) where
  α d := Fin.snoc (α := fun _ => ℕ) p.1.2.α (colValue c) d
  α_le d := by
    induction d using Fin.lastCases with
    | last => simpa using colValue_le c
    | cast d => simpa using p.1.2.α_le d

theorem glueRow_apply_of_mem {p : CutoffPair n} {Cont : Finset (Fin (n + 1))} {a : Fin (n + 1)}
    (h : a ∈ Cont) : (glueRow p Cont).β a = n + 1 := if_pos h

theorem glueRow_apply_of_notMem {p : CutoffPair n} {Cont : Finset (Fin (n + 1))} {a : Fin (n + 1)}
    (h : a ∉ Cont) : (glueRow p Cont).β a = βext p a := if_neg h

theorem glueRow_eq_succ_iff {p : CutoffPair n} {Cont : Finset (Fin (n + 1))} {a : Fin (n + 1)} :
    (glueRow p Cont).β a = n + 1 ↔ a ∈ Cont := by
  by_cases h : a ∈ Cont
  · rw [glueRow_apply_of_mem h]
    exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [glueRow_apply_of_notMem h]
    have := βext_le p a
    exact ⟨fun h' => absurd h' (by omega), fun h' => absurd h' h⟩

theorem lt_glueRow_iff {p : CutoffPair n} {Cont : Finset (Fin (n + 1))} {a : Fin (n + 1)} :
    n < (glueRow p Cont).β a ↔ a ∈ Cont := by
  by_cases h : a ∈ Cont
  · rw [glueRow_apply_of_mem h]
    exact ⟨fun _ => h, fun _ => Nat.lt_succ_self _⟩
  · rw [glueRow_apply_of_notMem h]
    have := βext_le p a
    exact ⟨fun h' => absurd h' (by omega), fun h' => absurd h' h⟩

@[simp] theorem glueCol_castSucc (p : CutoffPair n) (c : Option (Fin (n + 1))) (d : Fin n) :
    (glueCol p c).α d.castSucc = p.1.2.α d := by simp [glueCol]

@[simp] theorem glueCol_last (p : CutoffPair n) (c : Option (Fin (n + 1))) :
    (glueCol p c).α (Fin.last n) = colValue c := by simp [glueCol]

theorem criterion_glue (p : CutoffPair n) (Cont : Finset (Fin (n + 1))) (c : Option (Fin (n + 1)))
    (hc : Allowed p Cont c) : Criterion (glueRow p Cont) (glueCol p c) := by
  intro d
  induction d using Fin.lastCases with
  | last =>
    cases c with
    | none => exact Or.inl (by simp [colValue])
    | some e =>
      right
      obtain ⟨heC, hpre⟩ := hc
      refine ⟨e, by simp [colValue], ?_, ?_⟩
      · rw [Fin.val_last, glueRow_apply_of_mem heC]
        exact Nat.lt_succ_self _
      · intro a hae hβ
        rw [Fin.val_last] at hβ
        by_cases haC : a ∈ Cont
        · rw [glueRow_apply_of_mem haC] at hβ
          omega
        · rw [glueRow_apply_of_notMem haC] at hβ
          exact haC (hpre a (mem_candRows.2 hβ) hae)
  | cast d =>
    rcases p.2 d with h0 | ⟨e, he, hde, hprev⟩
    · left
      simpa using h0
    · right
      refine ⟨e.castSucc, by simpa using he, ?_, ?_⟩
      · simp only [Fin.val_castSucc]
        by_cases heC : e.castSucc ∈ Cont
        · rw [glueRow_apply_of_mem heC]
          have := d.isLt
          omega
        · rw [glueRow_apply_of_notMem heC, βext_castSucc]
          exact hde
      · intro a hae hβ
        simp only [Fin.val_castSucc] at hβ
        have hd := d.isLt
        by_cases haC : a ∈ Cont
        · rw [glueRow_apply_of_mem haC] at hβ
          omega
        · rw [glueRow_apply_of_notMem haC] at hβ
          induction a using Fin.lastCases with
          | last => exact absurd hae (not_lt.2 (Fin.le_last _))
          | cast a =>
            rw [βext_castSucc] at hβ
            exact hprev a (Fin.castSucc_lt_castSucc_iff.1 hae) hβ

/-- The extension of `p` by the continued rows `Cont` and the new column cutoff `c`
(Lemma 7.2). -/
def glue (p : CutoffPair n) (Cont : Finset (Fin (n + 1))) (c : Option (Fin (n + 1)))
    (hc : Allowed p Cont c) : CutoffPair (n + 1) :=
  ⟨(glueRow p Cont, glueCol p c), criterion_glue p Cont c hc⟩

theorem restrict_glue (p : CutoffPair n) (Cont : Finset (Fin (n + 1))) (c : Option (Fin (n + 1)))
    (hC : Cont ⊆ candRows p) (hc : Allowed p Cont c) : (glue p Cont c hc).restrict = p := by
  apply Subtype.ext
  apply Prod.ext
  · apply RowCutoff.ext
    funext a
    show min ((glueRow p Cont).β a.castSucc) n = p.1.1.β a
    by_cases h : a.castSucc ∈ Cont
    · rw [glueRow_apply_of_mem h]
      have := mem_candRows.1 (hC h)
      rw [βext_castSucc] at this
      omega
    · rw [glueRow_apply_of_notMem h, βext_castSucc]
      exact min_eq_left (p.1.1.β_le a)
  · apply ColCutoff.ext
    funext d
    exact glueCol_castSucc p c d

/-! ### Every extension is a `glue` -/

/-- The continued rows of a cutoff pair on `n + 1` vertices. -/
def contOf (x : CutoffPair (n + 1)) : Finset (Fin (n + 1)) :=
  univ.filter (fun a => x.1.1.β a = n + 1)

theorem mem_contOf {x : CutoffPair (n + 1)} {a : Fin (n + 1)} : a ∈ contOf x ↔ x.1.1.β a = n + 1 := by
  simp [contOf]

/-- The new column cutoff of a cutoff pair on `n + 1` vertices, as an option. -/
def colOf (x : CutoffPair (n + 1)) : Option (Fin (n + 1)) :=
  if h : x.1.2.α (Fin.last n) = 0 then none
  else some ⟨x.1.2.α (Fin.last n) - 1, by have := x.1.2.α_le (Fin.last n); rw [Fin.val_last] at this; omega⟩

theorem colValue_colOf (x : CutoffPair (n + 1)) : colValue (colOf x) = x.1.2.α (Fin.last n) := by
  unfold colOf
  split_ifs with h
  · simp [colValue, h]
  · simp only [colValue]
    omega

theorem βext_restrict (x : CutoffPair (n + 1)) (a : Fin (n + 1)) :
    βext x.restrict a = min (x.1.1.β a) n := by
  induction a using Fin.lastCases with
  | last =>
    rw [βext_last]
    have := x.1.1.le_β (Fin.last n)
    rw [Fin.val_last] at this
    omega
  | cast a =>
    rw [βext_castSucc]
    rfl

theorem contOf_subset (x : CutoffPair (n + 1)) : contOf x ⊆ candRows x.restrict := by
  intro a ha
  rw [mem_contOf] at ha
  rw [mem_candRows, βext_restrict, ha]
  omega

theorem allowed_colOf (x : CutoffPair (n + 1)) : Allowed x.restrict (contOf x) (colOf x) := by
  unfold colOf
  split_ifs with h0
  · trivial
  · rcases x.2 (Fin.last n) with h | ⟨e, he, hne, hprev⟩
    · exact absurd h h0
    · rw [Fin.val_last] at hne hprev
      have hee : (⟨x.1.2.α (Fin.last n) - 1, by have := x.1.2.α_le (Fin.last n); rw [Fin.val_last] at this; omega⟩ :
          Fin (n + 1)) = e := Fin.ext (by simp only; omega)
      show Allowed x.restrict (contOf x) (some _)
      rw [hee]
      refine ⟨mem_contOf.2 ?_, ?_⟩
      · have := x.1.1.β_le e
        omega
      · intro a ha hae
        rw [mem_candRows, βext_restrict] at ha
        rw [mem_contOf]
        have h1 := hprev a hae
        have h2 := x.1.1.β_le a
        omega

theorem glue_contOf_colOf (x : CutoffPair (n + 1)) :
    glue x.restrict (contOf x) (colOf x) (allowed_colOf x) = x := by
  apply Subtype.ext
  apply Prod.ext
  · apply RowCutoff.ext
    funext a
    show (if a ∈ contOf x then n + 1 else βext x.restrict a) = x.1.1.β a
    by_cases h : a ∈ contOf x
    · rw [if_pos h]
      exact (mem_contOf.1 h).symm
    · rw [if_neg h, βext_restrict]
      have h1 := x.1.1.β_le a
      have h2 : x.1.1.β a ≠ n + 1 := fun h' => h (mem_contOf.2 h')
      omega
  · apply ColCutoff.ext
    funext d
    induction d using Fin.lastCases with
    | last => exact (glueCol_last _ _).trans (colValue_colOf x)
    | cast d => exact glueCol_castSucc _ _ d

theorem contOf_glue (p : CutoffPair n) (Cont : Finset (Fin (n + 1))) (c : Option (Fin (n + 1)))
    (hc : Allowed p Cont c) : contOf (glue p Cont c hc) = Cont := by
  ext a
  rw [mem_contOf]
  exact glueRow_eq_succ_iff

theorem colOf_glue (p : CutoffPair n) (Cont : Finset (Fin (n + 1))) (c : Option (Fin (n + 1)))
    (hc : Allowed p Cont c) : colOf (glue p Cont c hc) = c := by
  unfold colOf
  have hcol : (glue p Cont c hc).1.2.α (Fin.last n) = colValue c := glueCol_last p c
  cases c with
  | none => simp [hcol, colValue]
  | some e =>
    rw [dif_neg (by rw [hcol]; simp [colValue])]
    congr 1
    apply Fin.ext
    simp [hcol, colValue]

/-! ### Weights of extensions -/

theorem rowsReaching_glueRow (p : CutoffPair n) (Cont : Finset (Fin (n + 1))) :
    (glueRow p Cont).rowsReaching = Cont.card := by
  unfold RowCutoff.rowsReaching
  rw [show univ.filter (fun a => (glueRow p Cont).β a = n + 1) = Cont from by
    ext a
    simp [glueRow_eq_succ_iff]]

theorem colCount_glue_castSucc (p : CutoffPair n) (Cont : Finset (Fin (n + 1)))
    (c : Option (Fin (n + 1))) (hC : Cont ⊆ candRows p) (d : Fin n) :
    colCount (glueRow p Cont) (glueCol p c) d.castSucc = colCount p.1.1 p.1.2 d := by
  unfold colCount
  conv_rhs => rw [← Finset.card_map Fin.castSuccEmb]
  apply congrArg Finset.card
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Fin.val_castSucc,
    glueCol_castSucc]
  induction a using Fin.lastCases with
  | last =>
    constructor
    · rintro ⟨h, -⟩
      exact absurd h (not_le.2 (Fin.castSucc_lt_last d))
    · rintro ⟨a', -, ha'⟩
      exact absurd ha' (Fin.castSucc_lt_last a').ne
  | cast a =>
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨a, ⟨Fin.castSucc_le_castSucc_iff.1 h1, ?_, h3⟩, rfl⟩
      by_cases haC : a.castSucc ∈ Cont
      · have := mem_candRows.1 (hC haC)
        rw [βext_castSucc] at this
        rw [this]
        exact d.isLt
      · rwa [glueRow_apply_of_notMem haC, βext_castSucc] at h2
    · rintro ⟨a', ⟨h1, h2, h3⟩, ha'⟩
      have : a' = a := Fin.castSucc_injective _ ha'
      subst this
      refine ⟨Fin.castSucc_le_castSucc_iff.2 h1, ?_, h3⟩
      by_cases haC : a'.castSucc ∈ Cont
      · rw [glueRow_apply_of_mem haC]
        have := d.isLt
        omega
      · rwa [glueRow_apply_of_notMem haC, βext_castSucc]

theorem colCount_glue_last (p : CutoffPair n) (Cont : Finset (Fin (n + 1))) (c : Option (Fin (n + 1))) :
    colCount (glueRow p Cont) (glueCol p c) (Fin.last n) =
      (Cont.filter (fun a => colValue c ≤ a.val)).card := by
  unfold colCount
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_last, Fin.val_last, glueCol_last,
    lt_glueRow_iff]

theorem middleCount_glue (p : CutoffPair n) (Cont : Finset (Fin (n + 1))) (c : Option (Fin (n + 1)))
    (hC : Cont ⊆ candRows p) :
    middleCount (glueRow p Cont) (glueCol p c) =
      middleCount p.1.1 p.1.2 + (Cont.filter (fun a => colValue c ≤ a.val)).card := by
  unfold middleCount
  rw [Fin.sum_univ_castSucc, colCount_glue_last]
  congr 1
  exact Finset.sum_congr rfl (fun d _ => colCount_glue_castSucc p Cont c hC d)

theorem cpWeight_glue (p : CutoffPair n) (Cont : Finset (Fin (n + 1))) (c : Option (Fin (n + 1)))
    (hC : Cont ⊆ candRows p) (hc : Allowed p Cont c) :
    cpWeight (glue p Cont c hc) = C (q ^ middleCount p.1.1 p.1.2) *
      (X ^ Cont.card * C (q ^ (Cont.filter (fun a => colValue c ≤ a.val)).card)) := by
  show X ^ (glueRow p Cont).rowsReaching * C (q ^ middleCount (glueRow p Cont) (glueCol p c)) = _
  rw [rowsReaching_glueRow, middleCount_glue p Cont c hC, pow_add, map_mul]
  ring

/-! ### The fibre sum -/

/-- The admissible new column cutoffs for a set of continued rows. -/
def choices (p : CutoffPair n) (Cont : Finset (Fin (n + 1))) : Finset (Option (Fin (n + 1))) :=
  insert none ((Cont.filter (fun e => ∀ a ∈ candRows p, a < e → a ∈ Cont)).image some)

theorem mem_choices_iff {p : CutoffPair n} {Cont : Finset (Fin (n + 1))} {c : Option (Fin (n + 1))} :
    c ∈ choices p Cont ↔ Allowed p Cont c := by
  cases c with
  | none => simp [choices, Allowed]
  | some e => simp [choices, Allowed]

/-- The extension data above `p`. -/
def model (p : CutoffPair n) : Finset (Σ _ : Finset (Fin (n + 1)), Option (Fin (n + 1))) :=
  (candRows p).powerset.sigma (fun Cont => choices p Cont)

theorem mem_model_iff {p : CutoffPair n} {y : Σ _ : Finset (Fin (n + 1)), Option (Fin (n + 1))} :
    y ∈ model p ↔ y.1 ⊆ candRows p ∧ Allowed p y.1 y.2 := by
  rw [model, Finset.mem_sigma, Finset.mem_powerset, mem_choices_iff]

/-- Lemma 7.3: the weights of the extensions of `p` sum to `q^{|ind(T ∩ F)|} · psi (candRows p)`. -/
theorem fiber_sum (p : CutoffPair n) :
    ∑ x ∈ univ.filter (fun x : CutoffPair (n + 1) => x.restrict = p), cpWeight x =
      C (q ^ middleCount p.1.1 p.1.2) * psi (candRows p) := by
  have h1 : ∑ x ∈ univ.filter (fun x : CutoffPair (n + 1) => x.restrict = p), cpWeight x =
      ∑ y ∈ model p, C (q ^ middleCount p.1.1 p.1.2) *
        (X ^ y.1.card * C (q ^ (y.1.filter (fun a => colValue y.2 ≤ a.val)).card)) := by
    refine Finset.sum_bij' (fun x _ => ⟨contOf x, colOf x⟩)
      (fun y hy => glue p y.1 y.2 (mem_model_iff.1 hy).2) ?_ ?_ ?_ ?_ ?_
    · -- `i` maps the fibre into the model
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [mem_model_iff]
      refine ⟨?_, ?_⟩
      · have := contOf_subset x
        rwa [hx.2] at this
      · have := allowed_colOf x
        rwa [hx.2] at this
    · -- `j` maps the model into the fibre
      intro y hy
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _,
        restrict_glue p y.1 y.2 (mem_model_iff.1 hy).1 (mem_model_iff.1 hy).2⟩
    · -- `j ∘ i = id`
      intro x hx
      rw [Finset.mem_filter] at hx
      have key : ∀ (p' : CutoffPair n) (_ : x.restrict = p') (hc : Allowed p' (contOf x) (colOf x)),
          glue p' (contOf x) (colOf x) hc = x := by
        rintro _ rfl hc
        exact glue_contOf_colOf x
      exact key p hx.2 _
    · -- `i ∘ j = id`
      rintro ⟨Cont, c⟩ hy
      simp only [Sigma.mk.injEq, heq_eq_eq]
      exact ⟨contOf_glue p Cont c _, colOf_glue p Cont c _⟩
    · -- the weights agree
      intro x hx
      rw [Finset.mem_filter] at hx
      have key : ∀ (p' : CutoffPair n) (_ : x.restrict = p') (hc : Allowed p' (contOf x) (colOf x)),
          cpWeight x = C (q ^ middleCount p'.1.1 p'.1.2) *
            (X ^ (contOf x).card *
              C (q ^ ((contOf x).filter (fun a => colValue (colOf x) ≤ a.val)).card)) := by
        rintro _ rfl hc
        rw [← cpWeight_glue x.restrict (contOf x) (colOf x) (contOf_subset x) hc,
          glue_contOf_colOf x]
      exact key p hx.2 (by have := allowed_colOf x; rwa [hx.2] at this)
  rw [h1, model, Finset.sum_sigma, psi, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro Cont _
  rw [choices, Finset.sum_insert (by simp), Finset.sum_image (fun _ _ _ _ h => Option.some_injective _ h)]
  have h0 : Cont.filter (fun a : Fin (n + 1) => colValue (none : Option (Fin (n + 1))) ≤ a.val) =
      Cont :=
    Finset.filter_true_of_mem (fun _ _ => Nat.zero_le _)
  have hs : ∀ e : Fin (n + 1), Cont.filter (fun a : Fin (n + 1) => colValue (some e) ≤ a.val) =
      Cont.filter (fun a => e < a) :=
    fun e => Finset.filter_congr (fun a _ => Iff.rfl)
  dsimp only
  simp only [h0, hs, psiTerm, mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr
  · ext e
    simp only [Finset.mem_filter]
  · intros
    rfl

/-! ### The total weight -/

/-- The total weight `∑_{(T,F) ∈ PT(Λ_n)} x^{ρ_n(T)} q^{|ind(T ∩ F)|}`, in cutoff coordinates. -/
def cpSum (n : ℕ) : Rq[X] := ∑ p : CutoffPair n, cpWeight p

theorem cpSum_succ (n : ℕ) :
    cpSum (n + 1) = ∑ p : CutoffPair n, C (q ^ middleCount p.1.1 p.1.2) * geomSum (p.1.1.rowsReaching + 1) := by
  unfold cpSum
  rw [← Finset.sum_fiberwise univ CutoffPair.restrict cpWeight]
  apply Finset.sum_congr rfl
  intro p _
  rw [fiber_sum, psi_eq_geomSum, card_candRows]

/-- Lemma 7.3, equation (7.6): `cpSum (n + 1) = Δ_q(x² cpSum n)`. -/
theorem isDelta_cpSum (n : ℕ) : IsDelta (X ^ 2 * cpSum n) (cpSum (n + 1)) := by
  rw [cpSum_succ, cpSum, Finset.mul_sum]
  apply IsDelta.sum
  intro p _
  have : X ^ 2 * cpWeight p = C (q ^ middleCount p.1.1 p.1.2) * X ^ (p.1.1.rowsReaching + 1 + 1) := by
    unfold cpWeight
    ring
  rw [this]
  exact (isDelta_X_pow_succ _).C_mul _

/-- The unique cutoff pair on no vertices. -/
def cutoffPairZero : CutoffPair 0 :=
  ⟨(⟨fun a => a.elim0, fun a => a.elim0, fun a => a.elim0⟩, ⟨fun d => d.elim0, fun d => d.elim0⟩),
    fun d => d.elim0⟩

instance : Subsingleton (CutoffPair 0) :=
  ⟨fun _ _ => Subtype.ext (Prod.ext (RowCutoff.ext (funext fun a => a.elim0))
    (ColCutoff.ext (funext fun d => d.elim0)))⟩

theorem cpSum_zero : cpSum 0 = 1 := by
  unfold cpSum
  rw [Fintype.sum_subsingleton _ cutoffPairZero]
  simp [cpWeight, RowCutoff.rowsReaching, middleCount]

/-- Theorem 7.5 in cutoff coordinates: `cpSum n = B_{n+1}`. -/
theorem cpSum_eq {B : ℕ → Rq[X]} (hB : IsGandhiFirst B) (n : ℕ) : cpSum n = B (n + 1) := by
  induction n with
  | zero => rw [cpSum_zero, hB.1]
  | succ n ih =>
    have h := hB.2 (n + 2) (by omega)
    have hm : n + 2 - 1 = n + 1 := rfl
    rw [hm, ← ih] at h
    exact (isDelta_cpSum n).unique h

end LinearQuiver

end PretorsionImageClosed
