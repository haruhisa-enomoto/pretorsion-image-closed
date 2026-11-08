module

public import PretorsionImageClosed.Pretorsion.Lattice

/-!
# Pretorsion theories with a fixed intersection

**Proposition 3.8.** For every subcategory `Z`, the pretorsion theories with
`T ∩ F = Z` are closed under nonempty meets (`sInf_middle`) and joins
(`sSup_middle`). For the meet, with `T = ⋂ Tᵢ`, the subcategory
`F_Z = {Y : t_T(Y) ∈ Z}` (`fixedF`) is a second component with
`(T, F_Z)` a pretorsion theory containing every `Fᵢ` (Lemma 3.7), so the meet
lies between `(T, Fᵢ)` and `(T, F_Z)`. Joins follow by duality.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PretorsionImageClosed.Statement

open CategoryTheory Limits Subcategory

variable {C : Type*} [Category C] [Abelian C] [HasLength C]

namespace PretorsionTheory

variable (S : Set (PretorsionTheory C)) (Z : Subcategory C)

theorem isQuotientClosed_meetT : (meetT S).IsQuotientClosed :=
  IsQuotientClosed.iInf fun P : S => P.1.isPretorsionTheory.isQuotientClosed

theorem meetT_le {P : PretorsionTheory C} (hP : P ∈ S) : (meetT S).prop ≤ P.T.prop :=
  fun X hX => (iInf_prop_iff _ X).1 hX ⟨P, hP⟩

/-- `F_Z = {Y : t(Y) ∈ Z}` for `t` the trace of `⋂ Tᵢ`. -/
def fixedF : Subcategory C where
  prop Y := Z.prop ((meetT S).trace Y : C)
  prop_of_retract h hY := Z.prop_of_retract (traceRetract (isQuotientClosed_meetT S) h) hY
  prop_biprod hX hY :=
    Z.prop_of_iso (traceBiprodIso (isQuotientClosed_meetT S) _ _).symm (Z.prop_biprod hX hY)
  prop_of_isZero h := Z.prop_of_isZero (IsZero.of_mono ((meetT S).trace _).arrow h)

variable {S Z} {P₀ : PretorsionTheory C} (hP₀ : P₀ ∈ S) (hS : ∀ P ∈ S, P.middle = Z.prop)
include hP₀ hS

/-- An object of `⋂ Tᵢ` embedding in an object of `Z` lies in `Z`. -/
theorem prop_of_mono_of_meetT {M N : C} (i : M ⟶ N) [Mono i] (hM : (meetT S).prop M)
    (hN : Z.prop N) : Z.prop M := by
  have hmid := hS P₀ hP₀
  rw [← hmid] at hN ⊢
  exact ⟨meetT_le S hP₀ M hM, P₀.isPretorsionTheory.isSubobjectClosed i inferInstance hN.2⟩

theorem isSubobjectClosed_fixedF : (fixedF S Z).IsSubobjectClosed := by
  intro X Y f hf hY
  haveI := hf
  haveI : Mono (traceMap (isQuotientClosed_meetT S) f) :=
    mono_of_mono_fac (traceMap_arrow (isQuotientClosed_meetT S) f)
  exact prop_of_mono_of_meetT hP₀ hS (traceMap (isQuotientClosed_meetT S) f)
    ((meetT S).prop_trace X) hY

omit hP₀ in
theorem F_le_fixedF {P : PretorsionTheory C} (hP : P ∈ S) : P.F ≤ fixedF S Z := by
  intro Y hY
  have hle : (meetT S).trace Y ≤ P.T.trace Y :=
    le_trace P.isPretorsionTheory.isQuotientClosed (meetT_le S hP _ ((meetT S).prop_trace Y))
  have hZ : Z.prop (P.T.trace Y : C) := by
    rw [← hS P hP]
    exact (P.isPretorsionTheory.prop_iff_prop_trace Y).1 hY
  exact prop_of_mono_of_meetT hP hS (Subobject.ofLE _ _ hle) ((meetT S).prop_trace Y) hZ

omit hP₀ hS in
/-- An object of `⋂ Tᵢ ∩ F_Z` lies in `Z`. -/
theorem prop_of_meetT_fixedF {X : C} (hX : (meetT S).prop X) (hF : (fixedF S Z).prop X) :
    Z.prop X := by
  have ht : (meetT S).trace X = ⊤ := (trace_eq_top_iff (isQuotientClosed_meetT S)).2 hX
  haveI : IsIso ((meetT S).trace X).arrow := (Subobject.isIso_arrow_iff_eq_top _).2 ht
  exact Z.prop_of_iso (asIso ((meetT S).trace X).arrow) hF

theorem isPretorsionTheory_fixedF : IsPretorsionTheory (meetT S).prop (fixedF S Z).prop := by
  have hTm : (meetT S).IsQuotientClosed := isQuotientClosed_meetT S
  have hFz : (fixedF S Z).IsSubobjectClosed := isSubobjectClosed_fixedF hP₀ hS
  refine isPretorsionTheory_of_realization hTm hFz (fun Y => ?_) (fun E => ?_)
  · have ht : (meetT S).trace ((meetT S).trace Y : C) = ⊤ :=
      (trace_eq_top_iff hTm).2 ((meetT S).prop_trace Y)
    haveI : IsIso ((meetT S).trace ((meetT S).trace Y : C)).arrow :=
      (Subobject.isIso_arrow_iff_eq_top _).2 ht
    exact ⟨fun h => ⟨(meetT S).prop_trace Y,
      Z.prop_of_iso (asIso ((meetT S).trace ((meetT S).trace Y : C)).arrow).symm h⟩,
      fun h => Z.prop_of_iso (asIso ((meetT S).trace ((meetT S).trace Y : C)).arrow) h.2⟩
  · refine ⟨fun hE {Y} f hY => isTrivial_of_closed hTm hFz f hE hY, fun hE => ?_⟩
    show (meetT S).prop E
    rw [meetT, iInf_prop_iff]
    intro P
    have hPF : P.1.F.IsSubobjectClosed := P.1.isPretorsionTheory.isSubobjectClosed
    obtain ⟨W, hW, g, k, hgk⟩ := hE (cokernel.π (P.1.F.reject E).arrow)
      (F_le_fixedF hS P.2 _ (P.1.F.prop_cokernel_reject E))
    have hWZ : Z.prop W := prop_of_meetT_fixedF hW.1 hW.2
    have hWP : (P.1.T.prop ⊓ P.1.F.prop) W := by
      have := hS P.1 P.2
      rw [PretorsionTheory.middle] at this
      rw [this]
      exact hWZ
    have htriv : IsTrivial (P.1.T.prop ⊓ P.1.F.prop) (𝟙 E ≫ cokernel.π (P.1.F.reject E).arrow) :=
      ⟨W, hWP, g, k, by rw [Category.id_comp, hgk]⟩
    obtain ⟨w, hw, -⟩ := (P.1.isPretorsionTheory.traceRejectCondition E).isPrekernel
      P.1.isPretorsionTheory.isQuotientClosed hPF |>.2 (𝟙 E) htriv
    exact P.1.T.prop_of_retract ⟨w, _, hw⟩ (P.1.T.prop_trace E)

/-- **Proposition 3.8**, meets: a nonempty meet of pretorsion theories with intersection `Z`
has intersection `Z`. -/
theorem sInf_middle : (sInf S).middle = Z.prop := by
  rw [sInf_eq]
  funext X
  apply propext
  constructor
  · rintro ⟨hT, hF⟩
    have hmem : (fixedF S Z).prop X := (iInf_prop_iff _ X).1 hF
      ⟨fixedF S Z, isPretorsionTheory_fixedF hP₀ hS, fun P hP => F_le_fixedF hS hP⟩
    exact prop_of_meetT_fixedF hT hmem
  · intro hX
    refine ⟨?_, ?_⟩
    · show (meetT S).prop X
      rw [meetT, iInf_prop_iff]
      intro P
      have := hS P.1 P.2
      rw [← this] at hX
      exact hX.1
    · rw [meet_F, iInf_prop_iff]
      intro F
      have := hS P₀ hP₀
      rw [← this] at hX
      exact F.2.2 P₀ hP₀ X hX.2

omit hP₀ hS in
theorem op_middle (P : PretorsionTheory C) : P.op.middle = P.middle.op := by
  unfold PretorsionTheory.middle PretorsionTheory.op
  rw [ObjectProperty.op_inf, inf_comm]
  rfl

omit hP₀ hS in
theorem unop_middle (P : PretorsionTheory Cᵒᵖ) : P.unop.middle = P.middle.unop := by
  unfold PretorsionTheory.middle PretorsionTheory.unop
  rw [ObjectProperty.unop_inf, inf_comm]
  rfl

/-- **Proposition 3.8**, joins. -/
theorem sSup_middle : (sSup S).middle = Z.prop := by
  rw [sSup_eq_join, join, unop_middle]
  have h := sInf_middle (S := PretorsionTheory.op '' S) (Z := Z.op) ⟨P₀, hP₀, rfl⟩ (by
    rintro _ ⟨P, hP, rfl⟩
    rw [op_middle, hS P hP]
    rfl)
  rw [sInf_eq] at h
  rw [h]
  rfl

end PretorsionTheory

end PretorsionImageClosed.Statement
