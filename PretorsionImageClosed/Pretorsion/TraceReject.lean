module

public import PretorsionImageClosed.Pretorsion.Basic
public import PretorsionImageClosed.Subcategories.Trace
public import PretorsionImageClosed.Subobjects.Preimage

/-!
# The trace–reject criterion

Theorem 2.12 of the manuscript: for a quotient-closed `T` and a
subobject-closed `F`, the pair `(T, F)` is a pretorsion theory iff for every
object `X`

* `r(X) = r(t(X))` and
* `t(X / r(X)) = t(X) / r(X)`,

where `t = t_T` is the trace and `r = r_F` the reject. In Lean the first
equality is stated as `r(X) ≤ t(X)` together with
`r(t(X)) = mk (ofLE r(X) t(X))`, the subobject of `t(X)` given by `r(X)`; the
second as `t(X/r(X)) = image (t(X) → X → X/r(X))`. When the condition holds,
`t(X)/r(X)` lies in `T ∩ F` and `t(X) → X → X/r(X)` is short
`(T ∩ F)`-preexact.

Corollary 2.13 (Facchini–Finocchiaro–Gran): for a pretorsion theory `(T, F)`
with `Z = T ∩ F`, `F = {Y : t_T(Y) ∈ Z}` and `T = {X : X/r_F(X) ∈ Z}`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PretorsionImageClosed

open CategoryTheory Limits ZeroObject

namespace Statement

open Subcategory

variable {C : Type*} [Category C] [Abelian C] [HasLength C]

variable (T F : Subcategory C) (X : C)

/-- The trace–reject condition (2.4) at an object `X`. -/
structure TraceRejectCondition : Prop where
  /-- `r(X) ⊆ t(X)`. -/
  reject_le_trace : F.reject X ≤ T.trace X
  /-- `r(t(X)) = r(X)`, as subobjects of `t(X)`. -/
  reject_trace : F.reject (T.trace X : C) =
    Subobject.mk (Subobject.ofLE (F.reject X) (T.trace X) reject_le_trace)
  /-- `t(X/r(X)) = t(X)/r(X)`, as subobjects of `X/r(X)`. -/
  trace_cokernel : T.trace (cokernel (F.reject X).arrow) =
    imageSubobject ((T.trace X).arrow ≫ (cokernel.π (F.reject X).arrow))

variable {T F X}

/-! ### From the condition to a pretorsion theory -/

section Converse

variable (hT : T.IsQuotientClosed) (hF : F.IsSubobjectClosed) (h : TraceRejectCondition T F X)
include hT hF h

/-- When (2.4) holds, `t(X)/r(X)` lies in `T ∩ F`. -/
theorem TraceRejectCondition.prop_image :
    (T.prop ⊓ F.prop)
      (imageSubobject ((T.trace X).arrow ≫ (cokernel.π (F.reject X).arrow)) : C) :=
  ⟨T.prop_of_iso (imageSubobjectIso _).symm
      (hT (factorThruImage _) inferInstance (T.prop_trace X)),
   hF (imageSubobject _).arrow inferInstance (F.prop_cokernel_reject X)⟩

theorem TraceRejectCondition.isTrivial_arrow_comp_π :
    IsTrivial (T.prop ⊓ F.prop) ((T.trace X).arrow ≫ (cokernel.π (F.reject X).arrow)) :=
  ⟨_, h.prop_image hT hF, factorThruImageSubobject _, (imageSubobject _).arrow,
    imageSubobject_arrow_comp _⟩

/-- When (2.4) holds, `t(X) → X` is a `(T ∩ F)`-prekernel of `X → X/r(X)`. -/
theorem TraceRejectCondition.isPrekernel :
    IsPrekernel (T.prop ⊓ F.prop) (T.trace X).arrow (cokernel.π (F.reject X).arrow) := by
  refine ⟨h.isTrivial_arrow_comp_π hT hF, fun {W} f hf => ?_⟩
  obtain ⟨N, hN, a, b, hab⟩ := hf
  have hb : imageSubobject b ≤ (imageSubobject ((T.trace X).arrow ≫ (cokernel.π (F.reject X).arrow))) := by
    rw [← h.trace_cokernel]
    exact le_trace hT
      (T.prop_of_iso (imageSubobjectIso b).symm (hT (factorThruImage b) inferInstance hN.1))
  have hfac : (imageSubobject ((T.trace X).arrow ≫ (cokernel.π (F.reject X).arrow))).Factors (f ≫ (cokernel.π (F.reject X).arrow)) := by
    rw [← hab]
    exact Subobject.factors_of_le _ hb (imageSubobject_factors_comp_self b a)
  have hP : Subobject.preimage (cokernel.π (F.reject X).arrow) (imageSubobject ((T.trace X).arrow ≫ (cokernel.π (F.reject X).arrow))) = T.trace X :=
    Subobject.preimage_imageSubobject_arrow_comp (cokernel.π (F.reject X).arrow) (T.trace X)
      (by rw [kernelSubobject_cokernel_π_arrow]; exact h.reject_le_trace)
  have hf' : (T.trace X).Factors f := hP ▸ (Subobject.preimage_factors_iff (cokernel.π (F.reject X).arrow) (imageSubobject ((T.trace X).arrow ≫ (cokernel.π (F.reject X).arrow))) f).2 hfac
  refine ⟨(T.trace X).factorThru f hf', Subobject.factorThru_arrow _ _ _, fun w hw => ?_⟩
  rw [← cancel_mono (T.trace X).arrow, hw, Subobject.factorThru_arrow]

/-- When (2.4) holds, `X → X/r(X)` is a `(T ∩ F)`-precokernel of `t(X) → X`. -/
theorem TraceRejectCondition.isPrecokernel :
    IsPrecokernel (T.prop ⊓ F.prop) (T.trace X).arrow (cokernel.π (F.reject X).arrow) := by
  refine ⟨h.isTrivial_arrow_comp_π hT hF, fun {W} g hg => ?_⟩
  obtain ⟨N, hN, a, b, hab⟩ := hg
  have hle : F.reject (T.trace X : C) ≤ kernelSubobject a :=
    reject_le_kernelSubobject hF a hN.2
  rw [h.reject_trace, Subobject.le_kernelSubobject_iff] at hle
  have hza : Subobject.ofLE (F.reject X) (T.trace X) h.reject_le_trace ≫ a = 0 := by
    rw [← Subobject.underlyingIso_hom_comp_eq_mk, Category.assoc] at hle
    rwa [← cancel_epi (Subobject.underlyingIso (Subobject.ofLE (F.reject X) (T.trace X)
      h.reject_le_trace)).hom, comp_zero]
  have hrg : (F.reject X).arrow ≫ g = 0 := by
    rw [← Subobject.ofLE_arrow h.reject_le_trace, Category.assoc, ← hab, ← Category.assoc, hza,
      zero_comp]
  refine ⟨cokernel.desc _ g hrg, cokernel.π_desc _ _ _, fun w hw => ?_⟩
  rw [← cancel_epi (cokernel.π (F.reject X).arrow), hw, cokernel.π_desc]

end Converse

/-- Theorem 2.12, the "if" direction: a pair `(T, F)` with `T` quotient-closed
and `F` subobject-closed satisfying (2.4) at every object is a pretorsion
theory, with the canonical short preexact sequences `t(X) → X → X/r(X)`. -/
theorem isPretorsionTheory_of_traceRejectCondition (hT : T.IsQuotientClosed)
    (hF : F.IsSubobjectClosed) (h : ∀ X, TraceRejectCondition T F X) :
    IsPretorsionTheory T.prop F.prop := by
  refine ⟨fun {X Y} f hX hY => ?_, fun X => ⟨_, _, (T.trace X).arrow,
    (cokernel.π (F.reject X).arrow), T.prop_trace X, F.prop_cokernel_reject X,
    (h X).isPrekernel hT hF, (h X).isPrecokernel hT hF⟩⟩
  exact ⟨image f, ⟨hT (factorThruImage f) inferInstance hX, hF (image.ι f) inferInstance hY⟩,
    factorThruImage f, image.ι f, image.fac f⟩

/-! ### From a short preexact sequence to the condition -/

/-- A morphism from an object of a quotient-closed `T` to an object of a subobject-closed `F`
factors through its image, which lies in `T ∩ F`. -/
theorem isTrivial_of_closed (hT : T.IsQuotientClosed) (hF : F.IsSubobjectClosed) {X Y : C}
    (f : X ⟶ Y) (hX : T.prop X) (hY : F.prop Y) : IsTrivial (T.prop ⊓ F.prop) f :=
  ⟨_, ⟨T.prop_of_iso (imageSubobjectIso f).symm (hT (factorThruImage f) inferInstance hX),
    hF (imageSubobject f).arrow inferInstance hY⟩, factorThruImageSubobject f,
    (imageSubobject f).arrow, imageSubobject_arrow_comp f⟩

section Forward

variable (hT : T.IsQuotientClosed) (hF : F.IsSubobjectClosed)
include hT hF

/-- The first term of a short preexact sequence of `X` is the trace of `X`. -/
theorem mk_eq_trace_of_isPrekernel {T' F' : C} {u : T' ⟶ X} {v : X ⟶ F'} (hT' : T.prop T')
    (hF' : F.prop F') (hu : IsPrekernel (T.prop ⊓ F.prop) u v) :
    haveI := hu.mono
    Subobject.mk u = T.trace X := by
  haveI := hu.mono
  apply le_antisymm
  · exact le_trace hT (T.prop_of_iso (Subobject.underlyingIso u).symm hT')
  · obtain ⟨w, hw, -⟩ := hu.2 (T.trace X).arrow (isTrivial_of_closed hT hF _ (T.prop_trace X) hF')
    exact Subobject.le_mk_of_comm w hw

/-- The kernel of the last map of a short preexact sequence of `X` is the reject of `X`. -/
theorem kernelSubobject_eq_reject_of_isPrecokernel {T' F' : C} {u : T' ⟶ X} {v : X ⟶ F'}
    (hT' : T.prop T') (hF' : F.prop F') (hv : IsPrecokernel (T.prop ⊓ F.prop) u v) :
    kernelSubobject v = F.reject X := by
  apply le_antisymm
  · rw [le_reject_iff hF]
    intro Y g hY
    obtain ⟨w, hw, -⟩ := hv.2 g (isTrivial_of_closed hT hF (u ≫ g) hT' hY)
    rw [← hw, ← Category.assoc, kernelSubobject_arrow_comp, zero_comp]
  · exact reject_le_kernelSubobject hF v hF'

/-- The trace–reject condition at `X` holds as soon as `X` has a short preexact sequence
`T' → X → F'` with `T' ∈ T` and `F' ∈ F` (the local form of Theorem 2.12, "only if"). -/
theorem traceRejectCondition_of_isShortPreexact {T' F' : C} {u : T' ⟶ X} {v : X ⟶ F'}
    (hT' : T.prop T') (hF' : F.prop F') (hs : IsShortPreexact (T.prop ⊓ F.prop) u v) :
    TraceRejectCondition T F X := by
  obtain ⟨hu, hv⟩ := hs
  haveI := hu.mono
  haveI := hv.epi
  have hmk : Subobject.mk u = T.trace X := mk_eq_trace_of_isPrekernel hT hF hT' hF' hu
  have hker : kernelSubobject v = F.reject X := kernelSubobject_eq_reject_of_isPrecokernel hT hF hT' hF' hv
  -- replace `u` by the inclusion of the trace
  have hu' : IsPrekernel (T.prop ⊓ F.prop) (T.trace X).arrow v := by
    rw [← hmk, ← Subobject.underlyingIso_hom_comp_eq_mk]
    exact hu.of_iso_left _
  have hv' : IsPrecokernel (T.prop ⊓ F.prop) (T.trace X).arrow v := by
    rw [← hmk, ← Subobject.underlyingIso_hom_comp_eq_mk]
    exact hv.of_iso_left _
  -- replace `v` by the projection onto `X/r(X)`
  have hrv : (F.reject X).arrow ≫ v = 0 := by
    rw [← hker, kernelSubobject_arrow_comp]
  have hexact : (ShortComplex.mk (F.reject X).arrow v hrv).Exact := by
    rw [ShortComplex.exact_iff_image_eq_kernel]
    change imageSubobject (F.reject X).arrow = kernelSubobject v
    rw [imageSubobject_mono, Subobject.mk_arrow, hker]
  haveI : Mono (cokernel.desc (F.reject X).arrow v hrv) := hexact.mono_cokernelDesc
  haveI : Epi (cokernel.desc (F.reject X).arrow v hrv) :=
    epi_of_epi_fac (cokernel.π_desc (F.reject X).arrow v hrv)
  haveI : IsIso (cokernel.desc (F.reject X).arrow v hrv) := isIso_of_mono_of_epi _
  set e : cokernel (F.reject X).arrow ≅ F' := asIso (cokernel.desc (F.reject X).arrow v hrv)
  have hpe : (cokernel.π (F.reject X).arrow) ≫ e.hom = v := cokernel.π_desc _ _ _
  have hu'' : IsPrekernel (T.prop ⊓ F.prop) (T.trace X).arrow (cokernel.π (F.reject X).arrow) := by
    have := (hu'.comp_iso_right e.symm)
    rwa [Iso.symm_hom, ← hpe, Category.assoc, e.hom_inv_id, Category.comp_id] at this
  have hv'' : IsPrecokernel (T.prop ⊓ F.prop) (T.trace X).arrow (cokernel.π (F.reject X).arrow) := by
    have := (hv'.comp_iso_right e.symm)
    rwa [Iso.symm_hom, ← hpe, Category.assoc, e.hom_inv_id, Category.comp_id] at this
  -- the preimage of `t(X/r(X))`
  set U := T.trace (cokernel (F.reject X).arrow)
  set P := Subobject.preimage (cokernel.π (F.reject X).arrow) U
  have hUZ : (T.prop ⊓ F.prop) (U : C) :=
    ⟨T.prop_trace _, hF U.arrow inferInstance (F.prop_cokernel_reject X)⟩
  have hPt : P ≤ T.trace X := by
    have htriv : IsTrivial (T.prop ⊓ F.prop) (P.arrow ≫ (cokernel.π (F.reject X).arrow)) :=
      ⟨_, hUZ, U.factorThru _ (Subobject.preimage_arrow_comp_factors (cokernel.π (F.reject X).arrow) U), U.arrow,
        Subobject.factorThru_arrow _ _ _⟩
    obtain ⟨w, hw, -⟩ := hu''.2 P.arrow htriv
    exact Subobject.le_of_comm w hw
  have hrt : F.reject X ≤ T.trace X := by
    have := Subobject.kernelSubobject_le_preimage (cokernel.π (F.reject X).arrow) U
    rw [kernelSubobject_cokernel_π_arrow] at this
    exact this.trans hPt
  refine ⟨hrt, ?_, ?_⟩
  · -- `r(t(X)) = r(X)`
    apply le_antisymm
    · apply reject_le hF
      have hz : Subobject.ofLE (F.reject X) (T.trace X) hrt ≫ (T.trace X).arrow ≫ (cokernel.π (F.reject X).arrow) = 0 := by
        rw [← Category.assoc, Subobject.ofLE_arrow, cokernel.condition]
      have hexact' : (ShortComplex.mk (Subobject.ofLE (F.reject X) (T.trace X) hrt)
          ((T.trace X).arrow ≫ (cokernel.π (F.reject X).arrow)) hz).Exact := by
        rw [ShortComplex.exact_iff_image_eq_kernel]
        change imageSubobject (Subobject.ofLE (F.reject X) (T.trace X) hrt) =
          kernelSubobject ((T.trace X).arrow ≫ (cokernel.π (F.reject X).arrow))
        rw [imageSubobject_mono]
        apply le_antisymm
        · exact le_kernelSubobject _ _
            (by rw [← Subobject.underlyingIso_hom_comp_eq_mk, Category.assoc, hz, comp_zero])
        · have h1 : (kernelSubobject (cokernel.π (F.reject X).arrow)).Factors
              ((kernelSubobject ((T.trace X).arrow ≫ (cokernel.π (F.reject X).arrow))).arrow ≫ (T.trace X).arrow) :=
            kernelSubobject_factors _ _ (by rw [Category.assoc, kernelSubobject_arrow_comp])
          rw [kernelSubobject_cokernel_π_arrow] at h1
          refine Subobject.le_mk_of_comm ((F.reject X).factorThru _ h1) ?_
          rw [← cancel_mono (T.trace X).arrow, Category.assoc, Subobject.ofLE_arrow,
            Subobject.factorThru_arrow]
      have hmono : Mono (cokernel.desc (Subobject.ofLE (F.reject X) (T.trace X) hrt)
          ((T.trace X).arrow ≫ (cokernel.π (F.reject X).arrow)) hz) :=
        hexact'.mono_cokernelDesc
      have hiso : cokernel (Subobject.mk (Subobject.ofLE (F.reject X) (T.trace X) hrt)).arrow ≅
          cokernel (Subobject.ofLE (F.reject X) (T.trace X) hrt) := by
        rw [← Subobject.underlyingIso_hom_comp_eq_mk]
        exact cokernelEpiComp _ _
      exact F.prop_of_iso hiso.symm (hF _ hmono (F.prop_cokernel_reject X))
    · rw [le_reject_iff hF]
      intro Y g hY
      have hc : IsTrivial (T.prop ⊓ F.prop) ((T.trace X).arrow ≫ (cokernel.π ((F.reject (T.trace X : C)).arrow ≫ (T.trace X).arrow))) :=
        ⟨cokernel (F.reject (T.trace X : C)).arrow,
          ⟨hT (cokernel.π (F.reject (T.trace X : C)).arrow) inferInstance (T.prop_trace X), F.prop_cokernel_reject _⟩,
          cokernel.π (F.reject (T.trace X : C)).arrow,
          cokernel.desc (F.reject (T.trace X : C)).arrow ((T.trace X).arrow ≫ (cokernel.π ((F.reject (T.trace X : C)).arrow ≫ (T.trace X).arrow)))
            (by rw [← Category.assoc, cokernel.condition]),
          cokernel.π_desc _ _ _⟩
      obtain ⟨w, hw, -⟩ := hv''.2 (cokernel.π ((F.reject (T.trace X : C)).arrow ≫ (T.trace X).arrow)) hc
      have hr : (F.reject X).arrow ≫ (cokernel.π ((F.reject (T.trace X : C)).arrow ≫ (T.trace X).arrow)) = 0 := by
        rw [← hw, ← Category.assoc, cokernel.condition, zero_comp]
      have hle : F.reject X ≤ Subobject.mk ((F.reject (T.trace X : C)).arrow ≫ (T.trace X).arrow) := by
        have := le_kernelSubobject _ _ hr
        rwa [← imageSubobject_eq_kernelSubobject_cokernel_π, imageSubobject_mono] at this
      have hw' : Subobject.ofLEMk (F.reject X) ((F.reject (T.trace X : C)).arrow ≫ (T.trace X).arrow) hle ≫ (F.reject (T.trace X : C)).arrow =
          Subobject.ofLE (F.reject X) (T.trace X) hrt := by
        rw [← cancel_mono (T.trace X).arrow, Category.assoc, Subobject.ofLEMk_comp,
          Subobject.ofLE_arrow]
      have hzero : Subobject.ofLE (F.reject X) (T.trace X) hrt ≫ g = 0 := by
        rw [← hw', Category.assoc, reject_arrow_comp_eq_zero hF g hY, comp_zero]
      rw [← Subobject.underlyingIso_hom_comp_eq_mk, Category.assoc, hzero, comp_zero]
  · -- `t(X/r(X)) = t(X)/r(X)`
    apply le_antisymm
    · calc U ≤ imageSubobject (P.arrow ≫ (cokernel.π (F.reject X).arrow)) :=
            Subobject.le_imageSubobject_preimage_arrow_comp (cokernel.π (F.reject X).arrow) U
        _ ≤ imageSubobject ((T.trace X).arrow ≫ (cokernel.π (F.reject X).arrow)) := imageSubobject_arrow_comp_le_of_le hPt (cokernel.π (F.reject X).arrow)
    · exact le_trace hT (T.prop_of_iso (imageSubobjectIso _).symm
        (hT (factorThruImage _) inferInstance (T.prop_trace X)))

end Forward

/-- Theorem 2.12, the "only if" direction: a pretorsion theory satisfies (2.4)
at every object. -/
theorem IsPretorsionTheory.traceRejectCondition (hP : IsPretorsionTheory T.prop F.prop) (X : C) :
    TraceRejectCondition T F X := by
  obtain ⟨T', F', u, v, hT', hF', hs⟩ := hP.2 X
  exact traceRejectCondition_of_isShortPreexact hP.isQuotientClosed hP.isSubobjectClosed hT' hF' hs

/-- **Theorem 2.12.** For a quotient-closed `T` and a subobject-closed `F`, the
pair `(T, F)` is a pretorsion theory iff the trace–reject condition (2.4)
holds at every object. -/
theorem isPretorsionTheory_iff_traceRejectCondition (hT : T.IsQuotientClosed)
    (hF : F.IsSubobjectClosed) :
    IsPretorsionTheory T.prop F.prop ↔ ∀ X, TraceRejectCondition T F X :=
  ⟨fun hP X => hP.traceRejectCondition X, isPretorsionTheory_of_traceRejectCondition hT hF⟩

/-! ### Corollary 2.13: reconstruction -/

section Reconstruction

variable (hP : IsPretorsionTheory T.prop F.prop)
include hP

/-- Corollary 2.13, first formula: `F = {Y : t_T(Y) ∈ T ∩ F}`. -/
theorem IsPretorsionTheory.prop_iff_prop_trace (Y : C) :
    F.prop Y ↔ (T.prop ⊓ F.prop) (T.trace Y : C) := by
  have hF : F.IsSubobjectClosed := hP.isSubobjectClosed
  have hc := hP.traceRejectCondition Y
  constructor
  · intro hY
    refine ⟨T.prop_trace Y, ?_⟩
    rw [← reject_eq_bot_iff hF, hc.reject_trace, Subobject.mk_eq_bot_iff_zero,
      ← cancel_mono (T.trace Y).arrow, Subobject.ofLE_arrow, zero_comp]
    have hr : F.reject Y = ⊥ := (reject_eq_bot_iff hF).2 hY
    rw [hr, Subobject.bot_arrow]
  · intro hZ
    have hr : F.reject (T.trace Y : C) = ⊥ := (reject_eq_bot_iff hF).2 hZ.2
    rw [hc.reject_trace, Subobject.mk_eq_bot_iff_zero] at hr
    rw [← reject_eq_bot_iff hF, ← Subobject.mk_arrow (F.reject Y), Subobject.mk_eq_bot_iff_zero,
      ← Subobject.ofLE_arrow hc.reject_le_trace, hr, zero_comp]

/-- Corollary 2.13, second formula: `T = {X : X/r_F(X) ∈ T ∩ F}`. -/
theorem IsPretorsionTheory.prop_iff_prop_cokernel_reject (X : C) :
    T.prop X ↔ (T.prop ⊓ F.prop) (cokernel (F.reject X).arrow) := by
  have hT : T.IsQuotientClosed := hP.isQuotientClosed
  have hc := hP.traceRejectCondition X
  constructor
  · intro hX
    refine ⟨?_, F.prop_cokernel_reject X⟩
    rw [← trace_eq_top_iff hT, hc.trace_cokernel]
    have ht : T.trace X = ⊤ := (trace_eq_top_iff hT).2 hX
    rw [ht]
    haveI : IsIso (⊤ : Subobject X).arrow := inferInstance
    exact imageSubobject_eq_top_of_epi _
  · intro hQ
    have ht : T.trace (cokernel (F.reject X).arrow) = ⊤ := (trace_eq_top_iff hT).2 hQ.1
    rw [hc.trace_cokernel] at ht
    haveI : Epi ((T.trace X).arrow ≫ (cokernel.π (F.reject X).arrow)) := epi_of_imageSubobject_eq_top _ ht
    -- `t(X) → X` is then an epimorphism, hence an isomorphism
    have hk : kernel.ι (cokernel.π (F.reject X).arrow) ≫ cokernel.π (T.trace X).arrow = 0 := by
      have hle : kernelSubobject (cokernel.π (F.reject X).arrow) ≤
          kernelSubobject (cokernel.π (T.trace X).arrow) :=
        (kernelSubobject_cokernel_π_arrow _).le.trans
          (hc.reject_le_trace.trans (kernelSubobject_cokernel_π_arrow _).ge)
      rw [← kernelSubobject_arrow', Category.assoc, (Subobject.le_kernelSubobject_iff _ _).1 hle,
        comp_zero]
    have he : Abelian.epiDesc (cokernel.π (F.reject X).arrow) _ hk = 0 := by
      rw [← cancel_epi ((T.trace X).arrow ≫ (cokernel.π (F.reject X).arrow)), Category.assoc, Abelian.comp_epiDesc,
        cokernel.condition, comp_zero]
    have hc0 : cokernel.π (T.trace X).arrow = 0 := by
      rw [← Abelian.comp_epiDesc (cokernel.π (F.reject X).arrow) _ hk, he, comp_zero]
    haveI : Epi (T.trace X).arrow := Abelian.epi_of_cokernel_π_eq_zero _ hc0
    haveI : IsIso (T.trace X).arrow := isIso_of_mono_of_epi _
    rw [← trace_eq_top_iff hT, ← Subobject.isIso_arrow_iff_eq_top]
    infer_instance

end Reconstruction

end Statement

end PretorsionImageClosed
