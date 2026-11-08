module

public import PretorsionImageClosed.Pretorsion.Lifting
public import PretorsionImageClosed.Pretorsion.Criterion
public import PretorsionImageClosed.Pretorsion.Realization

/-!
# Pretorsion theories with a fixed component

* `(T, mod)` and `(mod, F)` are pretorsion theories for every quotient-closed
  `T` and subobject-closed `F` (Section 3, before Lemma 3.1).
* **Proposition 3.2.** For a fixed quotient-closed `T`, the second components
  `F` with `(T, F)` a pretorsion theory are closed under arbitrary
  intersections (`isPretorsionTheory_iInf`). The finite case
  (`isPretorsionTheory_inf`) is proved by induction on length, dividing by one
  reject at a time with `IsShortPreexact.of_quotient`; this replaces Lemma 3.1
  and the transport (3.1) of the manuscript. The arbitrary case chooses, for
  each object, a finite subfamily with maximal reject.
* **Lemma 3.3** (`isPretorsionTheory_of_reject_trace`), **Lemma 3.4**
  (`prop_of_prop_cokernel_reject`) and **Proposition 3.5**
  (`isPretorsionTheory_iInf_left`), the last two via the realization criterion
  (Lemma 3.7).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PretorsionImageClosed.Statement

open CategoryTheory Limits Subcategory

variable {C : Type*} [Category C] [Abelian C] [HasLength C]

/-! ### The extreme partners -/

/-- `(T, mod)` is a pretorsion theory for every quotient-closed `T`. -/
theorem isPretorsionTheory_top_right {T : Subcategory C} (hT : T.IsQuotientClosed) :
    IsPretorsionTheory T.prop (⊤ : Subcategory C).prop := by
  refine isPretorsionTheory_of_realization hT isSubobjectClosed_top (fun Y => ?_) (fun E => ?_)
  · exact ⟨fun _ => ⟨T.prop_trace Y, trivial⟩, fun _ => trivial⟩
  · refine ⟨fun hE {Y} f _ => isTrivial_of_closed hT isSubobjectClosed_top f hE trivial, fun h => ?_⟩
    obtain ⟨W, hW, g, k, hgk⟩ := h (𝟙 E) trivial
    exact T.prop_of_retract ⟨g, k, hgk⟩ hW.1

/-- `(mod, F)` is a pretorsion theory for every subobject-closed `F`. -/
theorem isPretorsionTheory_top_left {F : Subcategory C} (hF : F.IsSubobjectClosed) :
    IsPretorsionTheory (⊤ : Subcategory C).prop F.prop := by
  refine isPretorsionTheory_of_realization isQuotientClosed_top hF (fun Y => ?_) (fun E => ?_)
  · have ht : (⊤ : Subcategory C).trace Y = ⊤ := (trace_eq_top_iff isQuotientClosed_top).2 trivial
    haveI : IsIso ((⊤ : Subcategory C).trace Y).arrow := (Subobject.isIso_arrow_iff_eq_top _).2 ht
    exact ⟨fun h => ⟨trivial, F.prop_of_iso (asIso ((⊤ : Subcategory C).trace Y).arrow).symm h⟩,
      fun h => F.prop_of_iso (asIso ((⊤ : Subcategory C).trace Y).arrow) h.2⟩
  · exact ⟨fun _ {Y} f hY => isTrivial_of_closed isQuotientClosed_top hF f trivial hY, fun _ => trivial⟩

/-! ### Dividing by one reject -/

/-- A nonzero subobject has a strictly shorter quotient. -/
theorem length_cokernel_lt {X : C} {S : Subobject X} (hS : S ≠ ⊥) :
    length (cokernel S.arrow) < length X := by
  apply length_lt_of_epi (cokernel.π S.arrow)
  intro hiso
  apply hS
  rw [← Subobject.mk_arrow S, Subobject.mk_eq_bot_iff_zero, ← cancel_mono (cokernel.π S.arrow),
    cokernel.condition, zero_comp]

/-- The inductive step of Proposition 3.2: if `(T, F)` satisfies (2.4) at `X`, `G ⊆ F` is
subobject-closed and `(T, G)` satisfies (2.4) at `X / r_F(X)`, then `(T, G)` satisfies (2.4)
at `X`. -/
theorem traceRejectCondition_of_quotient_reject {T F G : Subcategory C} (hT : T.IsQuotientClosed)
    (hF : F.IsSubobjectClosed) (hG : G.IsSubobjectClosed) (hGF : ∀ Y, G.prop Y → F.prop Y) {X : C}
    (hX : TraceRejectCondition T F X) (hV : TraceRejectCondition T G (cokernel (F.reject X).arrow)) :
    TraceRejectCondition T G X := by
  have h3 := hX.trace_cokernel
  let πA : (T.trace X : C) ⟶ (T.trace (cokernel (F.reject X).arrow) : C) :=
    factorThruImageSubobject ((T.trace X).arrow ≫ cokernel.π (F.reject X).arrow) ≫
      (Subobject.isoOfEq' h3.symm).hom
  haveI : Epi πA := epi_comp _ _
  have hcomm : πA ≫ (T.trace (cokernel (F.reject X).arrow)).arrow =
      (T.trace X).arrow ≫ cokernel.π (F.reject X).arrow := by
    simp only [πA, Category.assoc, Subobject.isoOfEq'_hom_arrow, imageSubobject_arrow_comp]
  clear_value πA
  have hs : IsShortPreexact (T.prop ⊓ G.prop) (T.trace (cokernel (F.reject X).arrow)).arrow
      (cokernel.π (G.reject (cokernel (F.reject X).arrow)).arrow) :=
    ⟨hV.isPrekernel hT hG, hV.isPrecokernel hT hG⟩
  have hpull : ∀ {Y : C} (u' : Y ⟶ X) (w : Y ⟶ (T.trace (cokernel (F.reject X).arrow) : C)),
      w ≫ (T.trace (cokernel (F.reject X).arrow)).arrow = u' ≫ cokernel.π (F.reject X).arrow →
        ∃ w' : Y ⟶ (T.trace X : C), w' ≫ (T.trace X).arrow = u' := by
    intro Y u' w hw
    have hfac : (Subobject.preimage (cokernel.π (F.reject X).arrow)
        (T.trace (cokernel (F.reject X).arrow))).Factors u' :=
      (Subobject.preimage_factors_iff _ _ _).2 ((Subobject.factors_iff _ _).2 ⟨w, hw⟩)
    rw [h3, Subobject.preimage_imageSubobject_arrow_comp _ _
      (by rw [kernelSubobject_cokernel_π_arrow]; exact hX.reject_le_trace)] at hfac
    exact ⟨_, Subobject.factorThru_arrow _ _ hfac⟩
  have hK : ∀ {W : C} (g : (T.trace X : C) ⟶ W), (T.prop ⊓ G.prop) W → kernel.ι πA ≫ g = 0 := by
    intro W g hW
    have h0 : (kernel.ι πA ≫ (T.trace X).arrow) ≫ cokernel.π (F.reject X).arrow = 0 := by
      rw [Category.assoc, ← hcomm, ← Category.assoc, kernel.condition, zero_comp]
    have hfr : (F.reject X).Factors (kernel.ι πA ≫ (T.trace X).arrow) := by
      have := kernelSubobject_factors (cokernel.π (F.reject X).arrow) _ h0
      rwa [kernelSubobject_cokernel_π_arrow] at this
    have hc : kernel.ι πA =
        (F.reject X).factorThru _ hfr ≫ Subobject.ofLE _ _ hX.reject_le_trace := by
      rw [← cancel_mono (T.trace X).arrow, Category.assoc, Subobject.ofLE_arrow,
        Subobject.factorThru_arrow]
    have hmk : (Subobject.mk (Subobject.ofLE (F.reject X) (T.trace X) hX.reject_le_trace)).arrow ≫
        g = 0 := by
      rw [← hX.reject_trace]
      exact reject_arrow_comp_eq_zero hF g (hGF W hW.2)
    rw [hc, Category.assoc, ← Subobject.underlyingIso_arrow
      (Subobject.ofLE (F.reject X) (T.trace X) hX.reject_le_trace), Category.assoc, hmk,
      comp_zero, comp_zero]
  have hseq := IsShortPreexact.of_quotient (cokernel.π (F.reject X).arrow) (T.trace X).arrow πA
    (T.trace (cokernel (F.reject X).arrow)).arrow
    (cokernel.π (G.reject (cokernel (F.reject X).arrow)).arrow) hs hcomm hpull hK
  exact traceRejectCondition_of_isShortPreexact hT hG (T.prop_trace X)
    (G.prop_cokernel_reject _) hseq

/-! ### Proposition 3.2 -/

/-- **Proposition 3.2**, binary case: if `(T, F₁)` and `(T, F₂)` are pretorsion theories, so is
`(T, F₁ ∩ F₂)`. -/
theorem isPretorsionTheory_inf {T F₁ F₂ : Subcategory C} (h₁ : IsPretorsionTheory T.prop F₁.prop)
    (h₂ : IsPretorsionTheory T.prop F₂.prop) : IsPretorsionTheory T.prop (F₁ ⊓ F₂).prop := by
  have hT : T.IsQuotientClosed := h₁.isQuotientClosed
  have hF₁ : F₁.IsSubobjectClosed := h₁.isSubobjectClosed
  have hF₂ : F₂.IsSubobjectClosed := h₂.isSubobjectClosed
  have hG : (F₁ ⊓ F₂).IsSubobjectClosed := hF₁.inf hF₂
  have key : ∀ (n : ℕ) (X : C), length X = n → TraceRejectCondition T (F₁ ⊓ F₂) X := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro X hX
      by_cases hr₁ : F₁.reject X = ⊥
      · by_cases hr₂ : F₂.reject X = ⊥
        · exact traceRejectCondition_of_prop hT hG
            ⟨(reject_eq_bot_iff hF₁).1 hr₁, (reject_eq_bot_iff hF₂).1 hr₂⟩
        · exact traceRejectCondition_of_quotient_reject hT hF₂ hG (fun _ h => h.2)
            (h₂.traceRejectCondition X) (ih _ (hX ▸ length_cokernel_lt hr₂) _ rfl)
      · exact traceRejectCondition_of_quotient_reject hT hF₁ hG (fun _ h => h.1)
          (h₁.traceRejectCondition X) (ih _ (hX ▸ length_cokernel_lt hr₁) _ rfl)
  exact isPretorsionTheory_of_traceRejectCondition hT hG fun X => key _ X rfl

/-- Changing the second component without changing the rejects of `X` and `t(X)` preserves the
trace–reject condition at `X`. -/
theorem TraceRejectCondition.of_reject_eq {T F G : Subcategory C} {X : C}
    (h : TraceRejectCondition T F X) (h1 : G.reject X = F.reject X)
    (h2 : G.reject (T.trace X : C) = F.reject (T.trace X : C)) : TraceRejectCondition T G X := by
  obtain ⟨a, b, c⟩ := h
  have a' : G.reject X ≤ T.trace X := h1 ▸ a
  refine ⟨a', ?_, ?_⟩
  · have key : ∀ (r : Subobject X) (_ : r = F.reject X) (hle : r ≤ T.trace X),
        Subobject.mk (Subobject.ofLE r _ hle) = Subobject.mk (Subobject.ofLE (F.reject X) _ a) := by
      rintro _ rfl _
      rfl
    rw [h2, b, key _ h1 a']
  · have key : ∀ (r : Subobject X), r = F.reject X →
        T.trace (cokernel r.arrow) = imageSubobject ((T.trace X).arrow ≫ cokernel.π r.arrow) := by
      rintro _ rfl
      exact c
    exact key _ h1

section Family

variable {ι : Type*} (F : ι → Subcategory C)

/-- The intersection of a finite subfamily. -/
def finInf (J : Finset ι) : Subcategory C := Subcategory.iInf (fun i : J => F i)

theorem finInf_prop_iff (J : Finset ι) (X : C) : (finInf F J).prop X ↔ ∀ i ∈ J, (F i).prop X := by
  rw [finInf, iInf_prop_iff]
  exact ⟨fun h i hi => h ⟨i, hi⟩, fun h i => h i.1 i.2⟩

variable {F} {T : Subcategory C} (hT : T.IsQuotientClosed) (h : ∀ i, IsPretorsionTheory T.prop (F i).prop)
include hT h

theorem isPretorsionTheory_finInf (J : Finset ι) : IsPretorsionTheory T.prop (finInf F J).prop := by
  classical
  induction J using Finset.induction_on with
  | empty =>
    have : (finInf F ∅).prop = (⊤ : Subcategory C).prop := by
      funext X
      apply propext
      rw [finInf_prop_iff]
      exact ⟨fun _ => trivial, fun _ i hi => absurd hi (Finset.notMem_empty i)⟩
    rw [this]
    exact isPretorsionTheory_top_right hT
  | insert a J _ ih =>
    have : (finInf F (insert a J)).prop = (F a ⊓ finInf F J).prop := by
      funext X
      apply propext
      rw [finInf_prop_iff, inf_prop, Pi.inf_apply, finInf_prop_iff]
      simp only [Finset.mem_insert, forall_eq_or_imp]
      rfl
    rw [this]
    exact isPretorsionTheory_inf (h a) ih

omit hT in
theorem isSubobjectClosed_finInf (J : Finset ι) : (finInf F J).IsSubobjectClosed :=
  IsSubobjectClosed.iInf fun i => (h i.1).isSubobjectClosed

omit hT in
theorem isSubobjectClosed_iInf : (Subcategory.iInf F).IsSubobjectClosed :=
  IsSubobjectClosed.iInf fun i => (h i).isSubobjectClosed

omit hT in
/-- The reject of the full intersection agrees with the reject of a finite subintersection. -/
theorem exists_reject_finInf_eq (X : C) :
    ∃ J₀ : Finset ι, ∀ J : Finset ι, J₀ ⊆ J →
      (finInf F J).reject X = (Subcategory.iInf F).reject X := by
  classical
  have hle : ∀ J : Finset ι, (finInf F J).reject X ≤ (Subcategory.iInf F).reject X := by
    intro J
    rw [le_reject_iff (isSubobjectClosed_iInf h)]
    intro Y g hY
    exact reject_arrow_comp_eq_zero (isSubobjectClosed_finInf h J) g
      ((finInf_prop_iff F J Y).2 fun i _ => (iInf_prop_iff F Y).1 hY i)
  have hmono : ∀ J J' : Finset ι, J ⊆ J' → (finInf F J).reject X ≤ (finInf F J').reject X := by
    intro J J' hJJ'
    rw [le_reject_iff (isSubobjectClosed_finInf h J')]
    intro Y g hY
    exact reject_arrow_comp_eq_zero (isSubobjectClosed_finInf h J) g
      ((finInf_prop_iff F J Y).2 fun i hi => (finInf_prop_iff F J' Y).1 hY i (hJJ' hi))
  obtain ⟨S, ⟨J₀, rfl⟩, hmax⟩ := Subobject.exists_maximal_of_nonempty
    (Set.range fun J : Finset ι => (finInf F J).reject X) ⟨_, ⟨∅, rfl⟩⟩
  have heq : (finInf F J₀).reject X = (Subcategory.iInf F).reject X := by
    apply le_antisymm (hle J₀)
    apply reject_le (isSubobjectClosed_iInf h)
    rw [iInf_prop_iff]
    intro i
    have hi : (finInf F J₀).reject X = (finInf F (insert i J₀)).reject X :=
      hmax _ ⟨insert i J₀, rfl⟩ (hmono _ _ (Finset.subset_insert _ _))
    rw [hi]
    exact (finInf_prop_iff F _ _).1 ((finInf F _).prop_cokernel_reject X) i (Finset.mem_insert_self _ _)
  refine ⟨J₀, fun J hJ => le_antisymm (hle J) ?_⟩
  rw [← heq]
  exact hmono _ _ hJ

/-- **Proposition 3.2.** If `(T, Fᵢ)` is a pretorsion theory for every `i`, so is `(T, ⋂ Fᵢ)`. -/
theorem isPretorsionTheory_iInf : IsPretorsionTheory T.prop (Subcategory.iInf F).prop := by
  classical
  refine isPretorsionTheory_of_traceRejectCondition hT (isSubobjectClosed_iInf h) fun X => ?_
  obtain ⟨J₀, hJ₀⟩ := exists_reject_finInf_eq h X
  obtain ⟨J₁, hJ₁⟩ := exists_reject_finInf_eq h (T.trace X : C)
  have hc := (isPretorsionTheory_finInf hT h (J₀ ∪ J₁)).traceRejectCondition X
  exact hc.of_reject_eq (hJ₀ _ Finset.subset_union_left).symm
    (hJ₁ _ Finset.subset_union_right).symm

end Family

/-! ### Lemmas 3.3 and 3.4 -/

/-- **Lemma 3.3.** If `r(X) = r(t(X))` for every `X` and `T = {X : X/r(X) ∈ T ∩ F}`, then
`(T, F)` is a pretorsion theory. -/
theorem isPretorsionTheory_of_reject_trace {T F : Subcategory C} (hT : T.IsQuotientClosed)
    (hF : F.IsSubobjectClosed)
    (hrt : ∀ X : C, ∃ h : F.reject X ≤ T.trace X,
      F.reject (T.trace X : C) = Subobject.mk (Subobject.ofLE _ _ h))
    (hTZ : ∀ X : C, T.prop X ↔ (T.prop ⊓ F.prop) (cokernel (F.reject X).arrow)) :
    IsPretorsionTheory T.prop F.prop := by
  refine isPretorsionTheory_of_realization hT hF (fun Y => ?_) (fun E => ?_)
  · refine ⟨fun hY => ⟨T.prop_trace Y, hF (T.trace Y).arrow inferInstance hY⟩, fun hZ => ?_⟩
    obtain ⟨hle, heq⟩ := hrt Y
    have hr : F.reject (T.trace Y : C) = ⊥ := (reject_eq_bot_iff hF).2 hZ.2
    rw [heq, Subobject.mk_eq_bot_iff_zero] at hr
    rw [← reject_eq_bot_iff hF, ← Subobject.mk_arrow (F.reject Y), Subobject.mk_eq_bot_iff_zero,
      ← Subobject.ofLE_arrow hle, hr, zero_comp]
  · refine ⟨fun hE {Y} f hY => isTrivial_of_closed hT hF f hE hY, fun h => ?_⟩
    obtain ⟨W, hW, g, k, hgk⟩ := h (cokernel.π (F.reject E).arrow) (F.prop_cokernel_reject E)
    haveI : Epi k := epi_of_epi_fac hgk
    exact (hTZ E).2 ⟨hT k inferInstance hW.1, F.prop_cokernel_reject E⟩

/-- **Lemma 3.4.** Let `(T, F)` be a pretorsion theory and `G ⊇ F` subobject-closed. If
`X / r_G(X) ∈ T`, then `X ∈ T`. -/
theorem prop_of_prop_cokernel_reject {T F G : Subcategory C} (hP : IsPretorsionTheory T.prop F.prop)
    (hG : G.IsSubobjectClosed) (hFG : ∀ Y, F.prop Y → G.prop Y) {X : C}
    (hX : T.prop (cokernel (G.reject X).arrow)) : T.prop X := by
  have hF : F.IsSubobjectClosed := hP.isSubobjectClosed
  have hle : G.reject X ≤ F.reject X := by
    rw [le_reject_iff hF]
    intro Y g hY
    exact reject_arrow_comp_eq_zero hG g (hFG Y hY)
  have hz : (G.reject X).arrow ≫ cokernel.π (F.reject X).arrow = 0 := by
    rw [← Subobject.ofLE_arrow hle, Category.assoc, cokernel.condition, comp_zero]
  have hfac : cokernel.π (G.reject X).arrow ≫ cokernel.desc _ _ hz = cokernel.π (F.reject X).arrow :=
    cokernel.π_desc _ _ _
  haveI : Epi (cokernel.desc _ _ hz) := epi_of_epi_fac hfac
  exact (hP.prop_iff_prop_cokernel_reject X).2
    ⟨hP.isQuotientClosed (cokernel.desc _ _ hz) inferInstance hX, F.prop_cokernel_reject X⟩

/-! ### Proposition 3.5 -/

/-- **Proposition 3.5.** If `(T'', F'')` is a lower bound of a family `(Tᵢ, Fᵢ)` of pretorsion
theories, then `(⋂ Tᵢ, F'')` is a pretorsion theory. -/
theorem isPretorsionTheory_iInf_left {ι : Type*} {T F : ι → Subcategory C} {T'' F'' : Subcategory C}
    (h : ∀ i, IsPretorsionTheory (T i).prop (F i).prop) (h'' : IsPretorsionTheory T''.prop F''.prop)
    (hT : ∀ i, T'' ≤ T i) (hF : ∀ i, F i ≤ F'') :
    IsPretorsionTheory (Subcategory.iInf T).prop F''.prop := by
  have hTq : (Subcategory.iInf T).IsQuotientClosed :=
    IsQuotientClosed.iInf fun i => (h i).isQuotientClosed
  have hF'' : F''.IsSubobjectClosed := h''.isSubobjectClosed
  refine isPretorsionTheory_of_realization hTq hF'' (fun Y => ?_) (fun E => ?_)
  · refine ⟨fun hY => ⟨(Subcategory.iInf T).prop_trace Y,
      hF'' ((Subcategory.iInf T).trace Y).arrow inferInstance hY⟩, fun hZ => ?_⟩
    -- `t''(Y) ⊆ t̂(Y) ∈ F''`
    have hle : T''.trace Y ≤ (Subcategory.iInf T).trace Y := by
      apply le_trace hTq
      rw [iInf_prop_iff]
      exact fun i => hT i _ (T''.prop_trace Y)
    exact (h''.prop_iff_prop_trace Y).2
      ⟨T''.prop_trace Y, hF'' (Subobject.ofLE _ _ hle) inferInstance hZ.2⟩
  · refine ⟨fun hE {Y} f hY => isTrivial_of_closed hTq hF'' f hE hY, fun hE => ?_⟩
    rw [iInf_prop_iff]
    intro i
    have hFi : (F i).IsSubobjectClosed := (h i).isSubobjectClosed
    obtain ⟨W, hW, g, k, hgk⟩ := hE (cokernel.π ((F i).reject E).arrow)
      (hF i _ ((F i).prop_cokernel_reject E))
    have hWi : (T i).prop W := (iInf_prop_iff T W).1 hW.1 i
    have htriv : IsTrivial ((T i).prop ⊓ (F i).prop) (𝟙 E ≫ cokernel.π ((F i).reject E).arrow) := by
      rw [Category.id_comp, ← hgk]
      exact (isTrivial_of_closed (h i).isQuotientClosed hFi k hWi
        ((F i).prop_cokernel_reject E)).comp_left g
    obtain ⟨w, hw, -⟩ := ((h i).traceRejectCondition E).isPrekernel (h i).isQuotientClosed hFi |>.2
      (𝟙 E) htriv
    exact (T i).prop_of_retract ⟨w, _, hw⟩ ((T i).prop_trace E)

end PretorsionImageClosed.Statement
