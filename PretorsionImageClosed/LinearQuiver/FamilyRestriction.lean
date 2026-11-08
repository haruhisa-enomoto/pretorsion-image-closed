module

public import PretorsionImageClosed.LinearQuiver.IntervalFamilies
public import PretorsionImageClosed.Gandhi.ColumnSum

/-!
# Restriction and extension of interval families

Section 8 of the manuscript. An intersection-closed family on `n + 1`
vertices restricts to one on the first `n` vertices
(`ClosedFamily.restrict`); the families restricting to a given `D` are the
extensions `D_J` by intervals `[a, n]` with `a` in a subset `J` of the
admissible starts `adm D` (Construction 8.3, Lemma 8.4(1): `glue`,
`glue_JOf`, `JOf_subset_adm`), and the admissible starts of `D_J` are counted
by `admCount` (Lemma 8.4(2): `card_adm_glue`).

Summing over the fibres gives the recurrence (8.7) for the generating
polynomial `fSum n = Σ_D q^{|D|} z^{|adm D|}` (`fSum_succ`) and the formula
(8.8) `Σ_{C ∈ L_im(Λ_{n+1})} x^{ρ} q^{|ind C|} = fSum n (1 + qx)` (`xSum_succ`).
Substituting `z = 1 + qx` turns (8.7) into the recurrence of the `q`-Gandhi
polynomials of the second kind (`isGandhiSecond_gandhiSecondOf`), which proves
Theorem 8.5 (`xSum_eq`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PretorsionImageClosed

open Statement Polynomial Finset

namespace LinearQuiver

variable {n : ℕ}

theorem castSucc_max (a c : Fin n) : (max a c).castSucc = max a.castSucc c.castSucc :=
  Monotone.map_max (fun _ _ h => Fin.castSucc_le_castSucc_iff.2 h)

theorem castSucc_min (a c : Fin n) : (min a c).castSucc = min a.castSucc c.castSucc :=
  Monotone.map_min (fun _ _ h => Fin.castSucc_le_castSucc_iff.2 h)

/-! ### Restriction -/

/-- Restriction of a family to the first `n` vertices. -/
def IntervalFamily.restrict (D : IntervalFamily (n + 1)) : IntervalFamily n where
  D := univ.filter (fun p : Fin n × Fin n => (p.1.castSucc, p.2.castSucc) ∈ D.D)
  le_of_mem p hp := Fin.castSucc_le_castSucc_iff.1 (D.le_of_mem _ (Finset.mem_filter.1 hp).2)

theorem mem_restrict {D : IntervalFamily (n + 1)} {p : Fin n × Fin n} :
    p ∈ D.restrict.D ↔ (p.1.castSucc, p.2.castSucc) ∈ D.D := by
  simp [IntervalFamily.restrict]

theorem IntervalFamily.IsClosed.restrict {D : IntervalFamily (n + 1)} (hD : D.IsClosed) :
    D.restrict.IsClosed := by
  intro a b c d hab hcd hmin
  rw [mem_restrict] at hab hcd ⊢
  have := hD _ _ _ _ hab hcd
    (by rw [← castSucc_max, ← castSucc_min]; exact Fin.castSucc_le_castSucc_iff.2 hmin)
  rwa [← castSucc_max, ← castSucc_min] at this

/-- Restriction of intersection-closed families. -/
def ClosedFamily.restrict (D : ClosedFamily (n + 1)) : ClosedFamily n := ⟨D.1.restrict, D.2.restrict⟩

/-! ### Admissible starts -/

/-- The admissible starts `a < n` for the vertex `n` (Definition 8.1): every interval of the
family containing `a` has its suffix from `a` in the family. -/
def admFin (D : IntervalFamily n) : Finset (Fin n) :=
  univ.filter (fun a => ∀ p ∈ D.D, p.1 ≤ a → a ≤ p.2 → (a, p.2) ∈ D.D)

/-- The admissible starts for the vertex `n`: `admFin D` together with `n` itself. -/
def adm (D : IntervalFamily n) : Finset (Fin (n + 1)) :=
  insert (Fin.last n) ((admFin D).map Fin.castSuccEmb)

theorem mem_admFin {D : IntervalFamily n} {a : Fin n} :
    a ∈ admFin D ↔ ∀ p ∈ D.D, p.1 ≤ a → a ≤ p.2 → (a, p.2) ∈ D.D := by
  simp [admFin]

theorem last_mem_adm (D : IntervalFamily n) : Fin.last n ∈ adm D := Finset.mem_insert_self _ _

theorem castSucc_mem_adm {D : IntervalFamily n} {a : Fin n} : a.castSucc ∈ adm D ↔ a ∈ admFin D := by
  simp [adm, (Fin.castSucc_lt_last a).ne]

theorem card_adm (D : IntervalFamily n) : (adm D).card = (admFin D).card + 1 := by
  rw [adm, Finset.card_insert_of_notMem, Finset.card_map]
  simp only [Finset.mem_map, not_exists, not_and]
  intro a _ h
  exact (Fin.castSucc_lt_last a).ne h

/-! ### Extension by a set of starts -/

open Classical in
/-- The extension `D_J` of `D` by the intervals `[a, n]`, `a ∈ J` (Construction 8.3). -/
def IntervalFamily.glue (D : IntervalFamily n) (J : Finset (Fin (n + 1))) : IntervalFamily (n + 1) where
  D := univ.filter (fun p : Fin (n + 1) × Fin (n + 1) =>
    (∃ a d : Fin n, p = (a.castSucc, d.castSucc) ∧ (a, d) ∈ D.D) ∨ (p.2 = Fin.last n ∧ p.1 ∈ J))
  le_of_mem p hp := by
    rw [Finset.mem_filter] at hp
    rcases hp.2 with ⟨a, d, rfl, had⟩ | ⟨h2, -⟩
    · exact Fin.castSucc_le_castSucc_iff.2 (D.le_of_mem _ had)
    · rw [h2]
      exact Fin.le_last _

theorem mem_glue {D : IntervalFamily n} {J : Finset (Fin (n + 1))} {p : Fin (n + 1) × Fin (n + 1)} :
    p ∈ (D.glue J).D ↔
      (∃ a d : Fin n, p = (a.castSucc, d.castSucc) ∧ (a, d) ∈ D.D) ∨ (p.2 = Fin.last n ∧ p.1 ∈ J) := by
  show p ∈ univ.filter _ ↔ _
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

theorem mem_glue_castSucc {D : IntervalFamily n} {J : Finset (Fin (n + 1))} {a d : Fin n} :
    (a.castSucc, d.castSucc) ∈ (D.glue J).D ↔ (a, d) ∈ D.D := by
  rw [mem_glue]
  constructor
  · rintro (⟨a', d', h, had⟩ | ⟨h, -⟩)
    · rw [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      rw [Fin.castSucc_inj] at h1 h2
      rw [h1, h2]
      exact had
    · exact absurd h (Fin.castSucc_lt_last d).ne
  · intro h
    exact Or.inl ⟨a, d, rfl, h⟩

theorem mem_glue_last {D : IntervalFamily n} {J : Finset (Fin (n + 1))} {a : Fin (n + 1)} :
    (a, Fin.last n) ∈ (D.glue J).D ↔ a ∈ J := by
  rw [mem_glue]
  constructor
  · rintro (⟨a', d', h, -⟩ | ⟨-, h⟩)
    · rw [Prod.mk.injEq] at h
      exact absurd h.2.symm (Fin.castSucc_lt_last d').ne
    · exact h
  · intro h
    exact Or.inr ⟨rfl, h⟩

theorem IntervalFamily.restrict_glue (D : IntervalFamily n) (J : Finset (Fin (n + 1))) : (D.glue J).restrict = D := by
  ext p
  rw [mem_restrict, mem_glue_castSucc]

/-- The set of starts of the intervals ending at the last vertex. -/
def JOf (D : IntervalFamily (n + 1)) : Finset (Fin (n + 1)) :=
  univ.filter (fun a => (a, Fin.last n) ∈ D.D)

theorem mem_JOf {D : IntervalFamily (n + 1)} {a : Fin (n + 1)} : a ∈ JOf D ↔ (a, Fin.last n) ∈ D.D := by
  simp [JOf]

/-- Construction 8.3: every family on `n + 1` vertices is the extension of its restriction. -/
theorem IntervalFamily.glue_JOf (D : IntervalFamily (n + 1)) : D.restrict.glue (JOf D) = D := by
  ext p
  rw [mem_glue]
  constructor
  · rintro (⟨a, d, rfl, had⟩ | ⟨h2, h1⟩)
    · exact mem_restrict.1 had
    · rw [mem_JOf] at h1
      have : p = (p.1, Fin.last n) := Prod.ext rfl h2
      rw [this]
      exact h1
  · intro hp
    obtain ⟨p1, p2⟩ := p
    induction p2 using Fin.lastCases with
    | last => exact Or.inr ⟨rfl, mem_JOf.2 hp⟩
    | cast d =>
      have hle : p1 ≤ d.castSucc := D.le_of_mem _ hp
      induction p1 using Fin.lastCases with
      | last => exact absurd hle (not_le.2 (Fin.castSucc_lt_last d))
      | cast a => exact Or.inl ⟨a, d, rfl, mem_restrict.2 hp⟩

theorem IntervalFamily.JOf_glue (D : IntervalFamily n) (J : Finset (Fin (n + 1))) : JOf (D.glue J) = J := by
  ext a
  rw [mem_JOf, mem_glue_last]

/-- Lemma 8.4(1), "only if": the starts of a closed family are admissible for its restriction. -/
theorem JOf_subset_adm {D : IntervalFamily (n + 1)} (hD : D.IsClosed) : JOf D ⊆ adm D.restrict := by
  intro a ha
  rw [mem_JOf] at ha
  induction a using Fin.lastCases with
  | last => exact last_mem_adm _
  | cast a =>
    rw [castSucc_mem_adm, mem_admFin]
    intro p hp h1 h2
    rw [mem_restrict] at hp ⊢
    have := hD _ _ _ _ hp ha (by
      rw [max_eq_right (Fin.castSucc_le_castSucc_iff.2 h1), min_eq_left (Fin.le_last _)]
      exact Fin.castSucc_le_castSucc_iff.2 h2)
    rwa [max_eq_right (Fin.castSucc_le_castSucc_iff.2 h1), min_eq_left (Fin.le_last _)] at this

/-- Lemma 8.4(1), "if": the extension by admissible starts is closed. -/
theorem IntervalFamily.IsClosed.glue {D : IntervalFamily n} (hD : D.IsClosed) {J : Finset (Fin (n + 1))}
    (hJ : J ⊆ adm D) : (D.glue J).IsClosed := by
  -- a new interval `[c, n]` meets an old interval `[a, b]` in `[max a c, b]`
  have key : ∀ (a b : Fin n) (c : Fin (n + 1)), (a, b) ∈ D.D → c ∈ J →
      max a.castSucc c ≤ b.castSucc → (max a.castSucc c, b.castSucc) ∈ (D.glue J).D := by
    intro a b c hab hc hmin
    rcases le_total c a.castSucc with hca | hac
    · rw [max_eq_left hca]
      exact mem_glue_castSucc.2 hab
    · rw [max_eq_right hac] at hmin ⊢
      induction c using Fin.lastCases with
      | last => exact absurd hmin (not_le.2 (Fin.castSucc_lt_last b))
      | cast c =>
        have hc' : c ∈ admFin D := castSucc_mem_adm.1 (hJ hc)
        rw [mem_admFin] at hc'
        exact mem_glue_castSucc.2 (hc' (a, b) hab (Fin.castSucc_le_castSucc_iff.1 hac)
          (Fin.castSucc_le_castSucc_iff.1 hmin))
  intro a b c d hab hcd hmin
  rw [mem_glue] at hab hcd
  rcases hab with ⟨a', b', hab', hab⟩ | ⟨hb, ha⟩ <;> rcases hcd with ⟨c', d', hcd', hcd⟩ | ⟨hd, hc⟩
  · rw [Prod.mk.injEq] at hab' hcd'
    obtain ⟨rfl, rfl⟩ := hab'
    obtain ⟨rfl, rfl⟩ := hcd'
    rw [← castSucc_max, ← castSucc_min] at hmin ⊢
    exact mem_glue_castSucc.2 (hD _ _ _ _ hab hcd (Fin.castSucc_le_castSucc_iff.1 hmin))
  · rw [Prod.mk.injEq] at hab'
    obtain ⟨rfl, rfl⟩ := hab'
    have hd' : d = Fin.last n := hd
    have hc' : c ∈ J := hc
    rw [hd', min_eq_left (Fin.le_last _)] at hmin ⊢
    exact key a' b' c hab hc' hmin
  · rw [Prod.mk.injEq] at hcd'
    obtain ⟨rfl, rfl⟩ := hcd'
    have hb' : b = Fin.last n := hb
    have ha' : a ∈ J := ha
    rw [hb', min_eq_right (Fin.le_last _), max_comm] at hmin ⊢
    exact key c' d' a hcd ha' hmin
  · have hb' : b = Fin.last n := hb
    have hd' : d = Fin.last n := hd
    have ha' : a ∈ J := ha
    have hc' : c ∈ J := hc
    rw [hb', hd', min_self, mem_glue_last]
    rcases max_choice a c with h | h <;> rw [h]
    · exact ha'
    · exact hc'

/-- The extension of an intersection-closed family by admissible starts. -/
def ClosedFamily.glue (D : ClosedFamily n) (J : Finset (Fin (n + 1))) (hJ : J ⊆ adm D.1) :
    ClosedFamily (n + 1) :=
  ⟨D.1.glue J, D.2.glue hJ⟩

theorem ClosedFamily.restrict_glue (D : ClosedFamily n) (J : Finset (Fin (n + 1))) (hJ : J ⊆ adm D.1) :
    (D.glue J hJ).restrict = D :=
  Subtype.ext (IntervalFamily.restrict_glue D.1 J)

theorem ClosedFamily.glue_JOf (D : ClosedFamily (n + 1)) :
    D.restrict.glue (JOf D.1) (JOf_subset_adm D.2) = D :=
  Subtype.ext (IntervalFamily.glue_JOf D.1)

/-! ### Sizes and admissible starts of an extension -/

theorem card_glue (D : IntervalFamily n) (J : Finset (Fin (n + 1))) :
    (D.glue J).D.card = D.D.card + J.card := by
  have h : (D.glue J).D = D.D.image (Prod.map Fin.castSucc Fin.castSucc) ∪
      J.image (fun a => (a, Fin.last n)) := by
    ext p
    rw [mem_glue, Finset.mem_union, Finset.mem_image, Finset.mem_image]
    constructor
    · rintro (⟨a, d, rfl, had⟩ | ⟨h2, h1⟩)
      · exact Or.inl ⟨(a, d), had, rfl⟩
      · exact Or.inr ⟨p.1, h1, Prod.ext rfl h2.symm⟩
    · rintro (⟨⟨a, d⟩, had, rfl⟩ | ⟨a, ha, rfl⟩)
      · exact Or.inl ⟨a, d, rfl, had⟩
      · exact Or.inr ⟨rfl, ha⟩
  rw [h, Finset.card_union_of_disjoint, Finset.card_image_of_injective _
    (Fin.castSucc_injective n |>.prodMap (Fin.castSucc_injective n)),
    Finset.card_image_of_injective _ (fun a b h => (Prod.mk.injEq _ _ _ _ ▸ h).1)]
  rw [Finset.disjoint_left]
  rintro p hp hp'
  rw [Finset.mem_image] at hp hp'
  obtain ⟨⟨a, d⟩, -, rfl⟩ := hp
  obtain ⟨a', -, h⟩ := hp'
  rw [Prod.mk.injEq] at h
  exact (Fin.castSucc_lt_last d).ne h.2.symm

theorem lastCount_glue (D : IntervalFamily n) (J : Finset (Fin (n + 1))) :
    (D.glue J).lastCount = J.card := by
  rw [lastCount_succ]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_glue_last]

/-- Lemma 8.4(2): the admissible starts `< n + 1` of `D_J`. -/
theorem admFin_glue {D : IntervalFamily n} {J : Finset (Fin (n + 1))} (hJ : J ⊆ adm D) :
    admFin (D.glue J) = J ∪ (adm D).filter (fun c => ∀ a ∈ J, c ≤ a) := by
  ext c
  rw [mem_admFin, Finset.mem_union, Finset.mem_filter]
  -- the condition on old intervals is admissibility for `D`
  have hold : (∀ a d : Fin n, (a, d) ∈ D.D → a.castSucc ≤ c → c ≤ d.castSucc →
      (c, d.castSucc) ∈ (D.glue J).D) ↔ c ∈ adm D := by
    induction c using Fin.lastCases with
    | last =>
      refine ⟨fun _ => last_mem_adm D, fun _ a d _ _ h => ?_⟩
      exact absurd h (not_le.2 (Fin.castSucc_lt_last d))
    | cast c =>
      rw [castSucc_mem_adm, mem_admFin]
      constructor
      · intro h p hp h1 h2
        exact mem_glue_castSucc.1 (h p.1 p.2 hp (Fin.castSucc_le_castSucc_iff.2 h1)
          (Fin.castSucc_le_castSucc_iff.2 h2))
      · intro h a d had h1 h2
        exact mem_glue_castSucc.2 (h (a, d) had (Fin.castSucc_le_castSucc_iff.1 h1)
          (Fin.castSucc_le_castSucc_iff.1 h2))
  constructor
  · intro h
    by_cases hcJ : c ∈ J
    · exact Or.inl hcJ
    · right
      refine ⟨hold.1 fun a d had h1 h2 => h _ (mem_glue_castSucc.2 had) h1 h2, ?_⟩
      intro a ha
      by_contra hlt
      have := h (a, Fin.last n) (mem_glue_last.2 ha) (not_le.1 hlt).le (Fin.le_last _)
      exact hcJ (mem_glue_last.1 this)
  · intro h p hp h1 h2
    rw [mem_glue] at hp
    rcases hp with ⟨a, d, rfl, had⟩ | ⟨hp2, hp1⟩
    · have hc : c ∈ adm D := by
        rcases h with hcJ | ⟨hc, -⟩
        · exact hJ hcJ
        · exact hc
      exact hold.2 hc a d had h1 h2
    · rw [hp2] at h2 ⊢
      rw [mem_glue_last]
      rcases h with hcJ | ⟨-, hle⟩
      · exact hcJ
      · have := le_antisymm h1 (hle p.1 hp1)
        rw [← this]
        exact hp1

theorem card_admFin_glue {D : IntervalFamily n} {J : Finset (Fin (n + 1))} (hJ : J ⊆ adm D) :
    (admFin (D.glue J)).card + (if J = ∅ then 0 else 1) =
      J.card + ((adm D).filter (fun c => ∀ a ∈ J, c ≤ a)).card := by
  rw [admFin_glue hJ, ← Finset.card_union_add_card_inter, Finset.inter_filter,
    Finset.inter_eq_left.2 hJ]
  congr 1
  by_cases hJe : J = ∅
  · rw [if_pos hJe, hJe]
    simp
  · rw [if_neg hJe]
    have hne : J.Nonempty := Finset.nonempty_iff_ne_empty.2 hJe
    symm
    rw [Finset.card_eq_one]
    refine ⟨J.min' hne, ?_⟩
    ext c
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hc, hle⟩
      exact le_antisymm (hle _ (Finset.min'_mem J hne)) (Finset.min'_le J c hc)
    · rintro rfl
      exact ⟨Finset.min'_mem J hne, fun a ha => Finset.min'_le J a ha⟩

/-- Lemma 8.4(2): the number of admissible starts of `D_J` is `admCount (adm D) J`. -/
theorem card_adm_glue {D : IntervalFamily n} {J : Finset (Fin (n + 1))} (hJ : J ⊆ adm D) :
    (adm (D.glue J)).card = admCount (adm D) J := by
  rw [card_adm, admCount]
  have := card_admFin_glue hJ
  have e : ((adm D).filter (fun c => ∀ a ∈ J, c ≤ a)).card =
      ((adm D).filter (fun c => ∀ j ∈ J, c ≤ j)).card := by
    congr 1
  split_ifs at this ⊢
  · rw [add_zero] at this
    rw [this, e]
    ring_nf <;> congr
  · rw [this, e]
    ring_nf <;> congr

/-! ### The fibre sums -/

/-- Equality of intersection-closed families is decided classically. -/
noncomputable instance : DecidableEq (ClosedFamily n) := Classical.decEq _

theorem fiber_sum_family (D : ClosedFamily n) (f : ClosedFamily (n + 1) → Rq[X])
    (g : Finset (Fin (n + 1)) → Rq[X]) (hfg : ∀ J (hJ : J ⊆ adm D.1), f (D.glue J hJ) = g J) :
    ∑ D' ∈ univ.filter (fun D' : ClosedFamily (n + 1) => D'.restrict = D), f D' =
      ∑ J ∈ (adm D.1).powerset, g J := by
  refine Finset.sum_bij' (fun D' _ => JOf D'.1) (fun J hJ => D.glue J (Finset.mem_powerset.1 hJ))
    ?_ ?_ ?_ ?_ ?_
  · intro D' hD'
    rw [Finset.mem_filter] at hD'
    rw [Finset.mem_powerset]
    have := JOf_subset_adm D'.2
    rwa [show D'.1.restrict = D.1 from congrArg Subtype.val hD'.2] at this
  · intro J hJ
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, D.restrict_glue J _⟩
  · intro D' hD'
    rw [Finset.mem_filter] at hD'
    have key : ∀ (E : ClosedFamily n) (_ : D'.restrict = E) (hJ : JOf D'.1 ⊆ adm E.1),
        E.glue (JOf D'.1) hJ = D' := by
      rintro _ rfl hJ
      exact D'.glue_JOf
    exact key D hD'.2 _
  · intro J hJ
    exact IntervalFamily.JOf_glue D.1 J
  · intro D' hD'
    rw [Finset.mem_filter] at hD'
    have hJ' : JOf D'.1 ⊆ adm D.1 := by
      have := JOf_subset_adm D'.2
      rwa [show D'.1.restrict = D.1 from congrArg Subtype.val hD'.2] at this
    have key : ∀ (E : ClosedFamily n) (_ : D'.restrict = E) (hJ : JOf D'.1 ⊆ adm E.1),
        E.glue (JOf D'.1) hJ = D' := by
      rintro _ rfl hJ
      exact D'.glue_JOf
    rw [← hfg _ hJ', key D hD'.2 hJ']

/-- The generating polynomial `Q_n(z, q) = Σ_D q^{|D|} z^{|adm D|}` (equation (8.5)), with `z = X`. -/
def fSum (n : ℕ) : Rq[X] := ∑ D : ClosedFamily n, C (q ^ D.1.D.card) * X ^ (adm D.1).card

/-- The weighted count `Σ_{C ∈ L_im(Λ_n)} x^{ρ_n(C)} q^{|ind C|}` in terms of families. -/
def xSum (n : ℕ) : Rq[X] := ∑ D : ClosedFamily n, fWeight D

theorem fSum_succ_eq (n : ℕ) :
    fSum (n + 1) = ∑ D : ClosedFamily n, C (q ^ D.1.D.card) * theta (adm D.1) := by
  unfold fSum
  rw [← Finset.sum_fiberwise univ ClosedFamily.restrict]
  apply Finset.sum_congr rfl
  intro D _
  rw [theta, Finset.mul_sum]
  apply fiber_sum_family D _ (fun J => C (q ^ D.1.D.card) * thetaTerm (adm D.1) J)
  intro J hJ
  show C (q ^ (D.1.glue J).D.card) * X ^ (adm (D.1.glue J)).card = _
  rw [card_glue, card_adm_glue hJ, thetaTerm, pow_add, map_mul]
  ring

/-- Equation (8.7): `Q_{n+1} = z Q_n + q z² Δ_q Q_n`. -/
theorem fSum_succ (n : ℕ) :
    ∃ G, IsDelta (fSum n) G ∧ fSum (n + 1) = X * fSum n + C q * X ^ 2 * G := by
  refine ⟨∑ D : ClosedFamily n, C (q ^ D.1.D.card) * deltaXPow (adm D.1).card, ?_, ?_⟩
  · unfold fSum
    apply IsDelta.sum
    intro D _
    exact (isDelta_X_pow _).C_mul _
  · rw [fSum_succ_eq]
    unfold fSum
    simp only [theta_eq, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intros
      ring
    · apply Finset.sum_congr rfl
      intros
      ring

/-- Equation (8.8): the weighted count for `n + 1` vertices is `Q_n(1 + qx, q)`. -/
theorem xSum_succ (n : ℕ) : xSum (n + 1) = (fSum n).comp U := by
  unfold xSum fSum
  rw [← Polynomial.coe_compRingHom_apply, map_sum]
  rw [← Finset.sum_fiberwise univ ClosedFamily.restrict]
  apply Finset.sum_congr rfl
  intro D _
  rw [Polynomial.coe_compRingHom_apply, mul_comp, C_comp, X_pow_comp]
  rw [fiber_sum_family D _ (fun J => C (q ^ D.1.D.card) * ((C q * X) ^ J.card * 1 ^ ((adm D.1).card - J.card)))]
  · rw [← Finset.mul_sum, Finset.sum_pow_mul_eq_add_pow, add_comm]
  · intro J hJ
    show X ^ (D.1.glue J).lastCount * C (q ^ (D.1.glue J).D.card) = _
    rw [lastCount_glue, card_glue, pow_add, map_mul, one_pow, mul_one, mul_pow, ← C_pow]
    ring

/-! ### No vertices -/

/-- The empty family on no vertices. -/
def closedFamilyZero : ClosedFamily 0 :=
  ⟨⟨∅, fun p _ => p.1.elim0⟩, fun a => a.elim0⟩

instance : Subsingleton (ClosedFamily 0) :=
  ⟨fun D E => Subtype.ext (IntervalFamily.ext
    ((Finset.eq_empty_of_isEmpty D.1.D).trans (Finset.eq_empty_of_isEmpty E.1.D).symm))⟩

theorem fSum_zero : fSum 0 = X := by
  unfold fSum
  rw [Fintype.sum_subsingleton _ closedFamilyZero, card_adm]
  have : admFin closedFamilyZero.1 = ∅ := Finset.eq_empty_of_isEmpty _
  rw [this]
  simp [closedFamilyZero]

theorem xSum_zero : xSum 0 = 1 := by
  unfold xSum
  rw [Fintype.sum_subsingleton _ closedFamilyZero]
  simp [fWeight, closedFamilyZero, IntervalFamily.lastCount]

/-! ### The Gandhi polynomials of the second kind -/

/-- The sequence `C_1 = 1`, `C_{m+2} = Q_m(1 + qx, q)`. -/
def gandhiSecondOf : ℕ → Rq[X]
  | 0 => 0
  | 1 => 1
  | m + 2 => (fSum m).comp U

/-- Theorem 8.5, the recurrence: `gandhiSecondOf` is the sequence of `q`-Gandhi polynomials of
the second kind. -/
theorem isGandhiSecond_gandhiSecondOf : IsGandhiSecond gandhiSecondOf := by
  refine ⟨rfl, fun m hm => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  cases m with
  | zero =>
    refine ⟨1, ?_, ?_⟩
    · show IsDelta (X * 1) 1
      rw [mul_one, ← geomSum_zero, ← pow_one X]
      exact isDelta_X_pow_succ 0
    · show (fSum 0).comp U = U * 1
      rw [fSum_zero, X_comp, mul_one]
  | succ m =>
    obtain ⟨G, hG, hrec⟩ := fSum_succ m
    refine ⟨(fSum m).comp U + C q * U * G.comp U, isDelta_X_mul_comp hG, ?_⟩
    show (fSum (m + 1)).comp U = U * ((fSum m).comp U + C q * U * G.comp U)
    rw [hrec]
    simp only [add_comp, mul_comp, X_comp, C_comp, pow_comp]
    ring

/-- Theorem 8.5 in terms of families: `xSum n = C_{n+1}`. -/
theorem xSum_eq (n : ℕ) : xSum n = gandhiSecondOf (n + 1) := by
  cases n with
  | zero => exact xSum_zero
  | succ m => exact xSum_succ m

end LinearQuiver

end PretorsionImageClosed
