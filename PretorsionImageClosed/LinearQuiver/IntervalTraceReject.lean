module

public import PretorsionImageClosed.LinearQuiver.ImageClosed
public import PretorsionImageClosed.Subobjects.Quotients
public import PretorsionImageClosed.Pretorsion.Criterion

/-!
# Traces and rejects of interval representations

Lemma 6.3 of the manuscript, in the form used for the cutoff criterion:

* the kernel of the projection `M_{c,d} → M_{c,ℓ}` is the suffix `M_{ℓ+1,d}`
  (`kernelSubobject_intervalProj`), so the quotient of `M_{c,d}` by the suffix
  `M_{v,d}` is `M_{c,v-1}` (`cokernelSuffixIso`);
* for a quotient-closed `T`, the trace of `M_{c,d}` is the suffix `M_{u,d}` with
  `u` the least row in `[c, d]` such that `M_{u,d} ∈ T`, or zero if there is
  none (`trace_interval_eq_suffix`, `trace_interval_eq_bot`);
* for a subobject-closed `F`, the reject of `M_{c,d}` is the suffix `M_{b+1,d}`
  with `b` the largest column in `[c, d]` such that `M_{c,b} ∈ F`, or all of
  `M_{c,d}` if there is none (`reject_interval_eq_suffix`, `reject_interval_eq_top`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PretorsionImageClosed

open CategoryTheory Limits Statement Subcategory

namespace LinearQuiver

universe u

variable {k : Type u} [Field k] {n : ℕ}

/-! ### Projections and inclusions -/

theorem intervalIncl_le_refl (a d : Fin n) : intervalIncl k d (le_refl a) = 𝟙 (interval k a d) :=
  hom_ext_coord fun i => by rw [coord_intervalIncl, coord_id]

theorem intervalProj_eq_canonicalHom (a : Fin n) {ℓ d : Fin n} (h : ℓ ≤ d) :
    intervalProj k a h = canonicalHom (k := k) (le_refl a) h := by
  rw [canonicalHom_eq, intervalIncl_le_refl, Category.comp_id]

theorem coord_intervalProj (a : Fin n) {ℓ d : Fin n} (h : ℓ ≤ d) (i : Fin n) :
    coord (intervalProj k a h) i = if a ≤ i ∧ i ≤ ℓ then 1 else 0 := by
  rw [intervalProj_eq_canonicalHom, coord_canonicalHom]

/-- The composite `M_{u,d} ↪ M_{c,d} ↠ M_{c,ℓ}` is the canonical morphism. -/
theorem intervalIncl_comp_intervalProj {c u ℓ d : Fin n} (hcu : c ≤ u) (hℓd : ℓ ≤ d) :
    intervalIncl k d hcu ≫ intervalProj k c hℓd = canonicalHom (k := k) hcu hℓd := by
  apply hom_ext_coord
  intro i
  rw [coord_comp, coord_intervalIncl, coord_intervalProj, coord_canonicalHom]
  by_cases h1 : u ≤ i ∧ i ≤ ℓ
  · rw [if_pos h1, if_pos ⟨h1.1, h1.2.trans hℓd⟩, if_pos ⟨hcu.trans h1.1, h1.2⟩, one_mul]
  · rw [if_neg h1]
    by_cases h2 : u ≤ i ∧ i ≤ d
    · rw [if_pos h2, one_mul, if_neg]
      intro h3
      exact h1 ⟨h2.1, h3.2⟩
    · rw [if_neg h2, zero_mul]

theorem canonicalHom_eq_zero_of_lt {c u ℓ d : Fin n} (hcu : c ≤ u) (hℓd : ℓ ≤ d) (h : ℓ < u) :
    canonicalHom (k := k) hcu hℓd = 0 := by
  apply hom_ext_coord
  intro i
  rw [coord_canonicalHom, coord_zero, if_neg]
  rintro ⟨h1, h2⟩
  exact (h.trans_le h1).not_ge h2

/-- The image of `M_{u,d} → M_{c,ℓ}` is the suffix `M_{u,ℓ}` of `M_{c,ℓ}`. -/
theorem imageSubobject_intervalIncl_comp_intervalProj {c u ℓ d : Fin n} (hcu : c ≤ u) (hℓd : ℓ ≤ d) :
    imageSubobject (intervalIncl k d hcu ≫ intervalProj k c hℓd) = suffix c ℓ u hcu := by
  rw [intervalIncl_comp_intervalProj, imageSubobject_canonicalHom]
  rfl

/-- The kernel of `M_{c,d} ↠ M_{c,ℓ}` is the suffix `M_{ℓ+1,d}`. -/
theorem kernelSubobject_intervalProj {c ℓ d v : Fin n} (hℓd : ℓ ≤ d) (hcv : c ≤ v)
    (hv : ℓ.val + 1 = v.val) :
    kernelSubobject (intervalProj k c hℓd) = suffix c d v hcv := by
  have hℓv : ℓ < v := Fin.lt_def.2 (by omega)
  apply le_antisymm
  · rcases eq_bot_or_eq_suffix (kernelSubobject (intervalProj k c hℓd)) with h0 | ⟨u', hcu', -, hK⟩
    · rw [h0]
      exact bot_le
    · have hvu' : v ≤ u' := by
        by_contra hlt
        have hu'ℓ : u' ≤ ℓ := Fin.le_def.2 (by have := Fin.lt_def.1 (not_le.1 hlt); omega)
        have hle : suffix c d u' hcu' ≤ kernelSubobject (intervalProj k c hℓd) := hK.ge
        rw [Subobject.le_kernelSubobject_iff, suffix, ← Subobject.underlyingIso_hom_comp_eq_mk,
          Category.assoc] at hle
        have hle' : intervalIncl k d hcu' ≫ intervalProj k c hℓd = 0 :=
          (cancel_epi (Subobject.underlyingIso (intervalIncl k d hcu')).hom).1
            (by rw [hle, comp_zero])
        rw [intervalIncl_comp_intervalProj] at hle'
        have := congrArg (fun η => coord η u') hle'
        simp only [coord_canonicalHom, coord_zero] at this
        rw [if_pos ⟨le_rfl, hu'ℓ⟩] at this
        exact one_ne_zero this
      rw [hK]
      exact suffix_le_suffix hcv hvu'
  · apply le_kernelSubobject
    rw [suffix, ← Subobject.underlyingIso_hom_comp_eq_mk, Category.assoc,
      intervalIncl_comp_intervalProj, canonicalHom_eq_zero_of_lt hcv hℓd hℓv, comp_zero]

/-- The quotient of `M_{c,d}` by the suffix `M_{v,d}` is `M_{c,v-1}`. -/
def cokernelSuffixIso {c ℓ d v : Fin n} (hℓd : ℓ ≤ d) (hcv : c ≤ v) (hv : ℓ.val + 1 = v.val) :
    cokernel (suffix (k := k) c d v hcv).arrow ≅ interval k c ℓ :=
  eqToIso (congrArg (fun S : Subobject (interval k c d) => cokernel S.arrow)
    (kernelSubobject_intervalProj hℓd hcv hv).symm) ≪≫
    cokernelKernelSubobjectArrowIso (intervalProj k c hℓd)

theorem prop_cokernel_suffix_iff (Z : Subcategory (Statement.LinRep k n)) {c ℓ d v : Fin n}
    (hℓd : ℓ ≤ d) (hcv : c ≤ v) (hv : ℓ.val + 1 = v.val) :
    Z.prop (cokernel (suffix (k := k) c d v hcv).arrow) ↔ Z.prop (interval k c ℓ) :=
  Z.prop_iff_of_iso (cokernelSuffixIso hℓd hcv hv)

theorem prop_cokernel_top_arrow (Z : Subcategory (Statement.LinRep k n)) (X : Statement.LinRep k n) :
    Z.prop (cokernel (⊤ : Subobject X).arrow) :=
  Z.prop_of_isZero ((isZero_zero _).of_iso (cokernel.ofEpi _))

/-! ### The trace of an interval -/

variable {T F : Subcategory (Statement.LinRep k n)}

/-- Lemma 6.3: the trace of `M_{c,d}` is the suffix `M_{u,d}` for the least `u ∈ [c, d]` with
`M_{u,d} ∈ T`. -/
theorem trace_interval_eq_suffix (hT : T.IsQuotientClosed) {c u d : Fin n} (hcu : c ≤ u)
    (hu : T.prop (interval k u d)) (hmin : ∀ i, c ≤ i → i < u → ¬ T.prop (interval k i d)) :
    T.trace (interval k c d) = suffix c d u hcu := by
  apply le_antisymm
  · rcases eq_bot_or_eq_suffix (T.trace (interval k c d)) with h0 | ⟨u', hcu', -, hK⟩
    · rw [h0]
      exact bot_le
    · have hu' : T.prop (interval k u' d) :=
        prop_interval_of_prop_suffix T hcu' (by rw [← hK]; exact T.prop_trace _)
      rw [hK]
      rcases le_or_gt u u' with huu' | hu'u
      · exact suffix_le_suffix hcu huu'
      · exact absurd hu' (hmin u' hcu' hu'u)
  · exact le_trace hT (T.prop_of_iso (Subobject.underlyingIso _).symm hu)

/-- Lemma 6.3: the trace of `M_{c,d}` vanishes when no `M_{u,d}` with `u ∈ [c, d]` lies in `T`. -/
theorem trace_interval_eq_bot {c d : Fin n}
    (h : ∀ i, c ≤ i → i ≤ d → ¬ T.prop (interval k i d)) : T.trace (interval k c d) = ⊥ := by
  rcases eq_bot_or_eq_suffix (T.trace (interval k c d)) with h0 | ⟨u', hcu', hu'd, hK⟩
  · exact h0
  · exact absurd (prop_interval_of_prop_suffix T hcu' (by rw [← hK]; exact T.prop_trace _))
      (h u' hcu' hu'd)

/-! ### The reject of an interval -/

/-- Lemma 6.3: the reject of `M_{c,d}` is the suffix `M_{b+1,d}` for the largest `b ∈ [c, d]`
with `M_{c,b} ∈ F`. -/
theorem reject_interval_eq_suffix (hF : F.IsSubobjectClosed) {c ℓ d v : Fin n} (hℓd : ℓ ≤ d)
    (hcv : c ≤ v) (hv : ℓ.val + 1 = v.val) (hb : F.prop (interval k c ℓ))
    (hmax : ∀ j, ℓ < j → j ≤ d → ¬ F.prop (interval k c j)) :
    F.reject (interval k c d) = suffix c d v hcv := by
  apply le_antisymm
  · apply reject_le hF
    exact (prop_cokernel_suffix_iff F hℓd hcv hv).2 hb
  · rcases eq_bot_or_eq_suffix (F.reject (interval k c d)) with h0 | ⟨u', hcu', hu'd, hK⟩
    · have hcd : F.prop (interval k c d) := (reject_eq_bot_iff hF).1 h0
      have hℓd' : ℓ = d := by
        by_contra hne
        exact hmax d (lt_of_le_of_ne hℓd hne) le_rfl hcd
      subst hℓd'
      rw [h0, suffix_eq_bot_of_lt hcv (Fin.lt_def.2 (by omega))]
    · have hco : F.prop (cokernel (suffix (k := k) c d u' hcu').arrow) := by
        rw [← hK]
        exact F.prop_cokernel_reject _
      rw [hK]
      rcases eq_or_lt_of_le hcu' with hcu'' | hcu''
      · have : suffix (k := k) c d u' hcu' = ⊤ := by
          subst hcu''
          exact suffix_self c d
        rw [this]
        exact le_top
      · obtain ⟨ℓ', hℓ'⟩ : ∃ ℓ' : Fin n, ℓ'.val + 1 = u'.val :=
          ⟨⟨u'.val - 1, by omega⟩, by simp only; have := Fin.lt_def.1 hcu''; omega⟩
        have hℓ'd : ℓ' ≤ d := Fin.le_def.2 (by have := Fin.le_def.1 hu'd; omega)
        have hF' : F.prop (interval k c ℓ') := (prop_cokernel_suffix_iff F hℓ'd hcu' hℓ').1 hco
        have hle : ℓ' ≤ ℓ := by
          by_contra hlt
          exact hmax ℓ' (not_le.1 hlt) hℓ'd hF'
        have hu'v : u' ≤ v := Fin.le_def.2 (by have := Fin.le_def.1 hle; omega)
        exact suffix_le_suffix hcu' hu'v

/-- Lemma 6.3: the reject of `M_{c,d}` is all of `M_{c,d}` when no nonzero quotient `M_{c,j}`
lies in `F`. -/
theorem reject_interval_eq_top (hF : F.IsSubobjectClosed) {c d : Fin n} (hcd : c ≤ d)
    (h : ∀ j, c ≤ j → j ≤ d → ¬ F.prop (interval k c j)) : F.reject (interval k c d) = ⊤ := by
  rcases eq_bot_or_eq_suffix (F.reject (interval k c d)) with h0 | ⟨u', hcu', hu'd, hK⟩
  · exact absurd ((reject_eq_bot_iff hF).1 h0) (h d hcd le_rfl)
  · have hco : F.prop (cokernel (suffix (k := k) c d u' hcu').arrow) := by
      rw [← hK]
      exact F.prop_cokernel_reject _
    rcases eq_or_lt_of_le hcu' with hcu'' | hcu''
    · rw [hK]
      subst hcu''
      exact suffix_self c d
    · exfalso
      obtain ⟨ℓ', hℓ'⟩ : ∃ ℓ' : Fin n, ℓ'.val + 1 = u'.val :=
        ⟨⟨u'.val - 1, by omega⟩, by simp only; have := Fin.lt_def.1 hcu''; omega⟩
      have hℓ'd : ℓ' ≤ d := Fin.le_def.2 (by have := Fin.le_def.1 hu'd; omega)
      have hcℓ' : c ≤ ℓ' := Fin.le_def.2 (by have := Fin.lt_def.1 hcu''; omega)
      exact h ℓ' hcℓ' hℓ'd ((prop_cokernel_suffix_iff F hℓ'd hcu' hℓ').1 hco)

end LinearQuiver

end PretorsionImageClosed
