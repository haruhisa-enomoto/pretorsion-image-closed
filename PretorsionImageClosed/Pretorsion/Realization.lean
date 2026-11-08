module

public import PretorsionImageClosed.Pretorsion.TraceReject

/-!
# The realization criterion

Lemma 3.7 of the manuscript: let `T` be quotient-closed, `F` subobject-closed
and `Z = T ∩ F`. If `F = {Y : t_T(Y) ∈ Z}` and `T` consists exactly of the
objects all of whose morphisms to objects of `F` are `Z`-trivial, then `(T, F)`
is a pretorsion theory. It is used to construct meets with a prescribed
intersection and to realize image-closed subcategories (Theorem 4.4).

The proof follows the manuscript with `K = r_F(t(X))` in place of
`r_Z(t(X))`: both are the kernel of the trace against `F`, since `Z ⊆ F` and
morphisms from `t(X)` to `F` factor through `Z`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PretorsionImageClosed

open CategoryTheory Limits ZeroObject


namespace Statement

open Subcategory

variable {C : Type*} [Category C] [Abelian C] [HasLength C] {T F : Subcategory C}

/-- **Lemma 3.7.** -/
theorem isPretorsionTheory_of_realization (hT : T.IsQuotientClosed) (hF : F.IsSubobjectClosed)
    (hF' : ∀ Y, F.prop Y ↔ (T.prop ⊓ F.prop) (T.trace Y : C))
    (hT' : ∀ E, T.prop E ↔ ∀ {Y : C} (f : E ⟶ Y), F.prop Y → IsTrivial (T.prop ⊓ F.prop) f) :
    IsPretorsionTheory T.prop F.prop := by
  refine isPretorsionTheory_of_traceRejectCondition hT hF fun X => ?_
  set t := T.trace X with ht
  set K := F.reject (t : C) with hK
  -- the quotient `X/K'` for `K' = push t K`, its trace and the preimage `E`
  set E := Subobject.preimage (cokernel.π (Subobject.push t K).arrow)
    (T.trace (cokernel (Subobject.push t K).arrow)) with hE
  -- every morphism from `t` to an object of `F` kills `K`
  have hKg : ∀ {Y : C} (g : (t : C) ⟶ Y), F.prop Y → K.arrow ≫ g = 0 :=
    fun g hY => reject_arrow_comp_eq_zero hF g hY
  have hK'g : ∀ {Y : C} (g : X ⟶ Y), F.prop Y → (Subobject.push t K).arrow ≫ g = 0 := by
    intro Y g hY
    rw [Subobject.push_arrow, Category.assoc, Category.assoc, hKg (t.arrow ≫ g) hY, comp_zero]
  -- `t ≤ E`
  have htE : t ≤ E := by
    rw [hE, Subobject.le_preimage_iff]
    exact Subobject.factors_of_le _ (le_trace hT (T.prop_of_iso (imageSubobjectIso _).symm
      (hT (factorThruImage _) inferInstance (T.prop_trace X)))) (imageSubobject_factors_self _)
  -- `E ∈ T`
  have hET : T.prop (E : C) := by
    refine (hT' _).2 fun {Y} g hY => ?_
    have hker : kernel.ι (Subobject.preimageToSubobject (cokernel.π (Subobject.push t K).arrow)
        (T.trace (cokernel (Subobject.push t K).arrow))) ≫ g = 0 := by
      have h0 : (kernel.ι (Subobject.preimageToSubobject (cokernel.π (Subobject.push t K).arrow)
          (T.trace (cokernel (Subobject.push t K).arrow))) ≫ E.arrow) ≫
          cokernel.π (Subobject.push t K).arrow = 0 := by
        rw [Category.assoc, ← Subobject.preimageToSubobject_arrow, ← Category.assoc,
          kernel.condition, zero_comp]
      have hfac := Subobject.factors_of_comp_cokernel_π_eq_zero (Subobject.push t K) _ h0
      have hw := Subobject.factorThru_arrow _ _ hfac
      have hw' : kernel.ι (Subobject.preimageToSubobject (cokernel.π (Subobject.push t K).arrow)
          (T.trace (cokernel (Subobject.push t K).arrow))) =
          (Subobject.factorThru _ _ hfac ≫ (Subobject.underlyingIso (K.arrow ≫ t.arrow)).hom ≫
            K.arrow) ≫ Subobject.ofLE t E htE := by
        have hw2 : Subobject.factorThru _ _ hfac ≫ (Subobject.underlyingIso (K.arrow ≫ t.arrow)).hom ≫
            K.arrow ≫ t.arrow = kernel.ι (Subobject.preimageToSubobject
              (cokernel.π (Subobject.push t K).arrow)
              (T.trace (cokernel (Subobject.push t K).arrow))) ≫ E.arrow := by
          rw [← Subobject.push_arrow]
          exact hw
        rw [← cancel_mono E.arrow, Category.assoc, Subobject.ofLE_arrow]
        conv_lhs => rw [← hw2]
        simp only [Category.assoc]
      rw [hw', Category.assoc, Category.assoc, Category.assoc, hKg (Subobject.ofLE t E htE ≫ g) hY]
      simp only [comp_zero]
    rw [← Abelian.comp_epiDesc _ g hker]
    exact ((hT' _).1 (T.prop_trace _) _ hY).comp_left _
  have hEt : E = t := le_antisymm (le_trace hT hET) htE
  -- `t(X/K') = t(X)/K'`
  have hb : T.trace (cokernel (Subobject.push t K).arrow) =
      imageSubobject (t.arrow ≫ cokernel.π (Subobject.push t K).arrow) := by
    have := Subobject.imageSubobject_preimage_arrow_comp (cokernel.π (Subobject.push t K).arrow)
      (T.trace (cokernel (Subobject.push t K).arrow))
    rw [← hE, hEt] at this
    exact this.symm
  -- the kernel of `t → X → X/K'` is `K`, so `t/K` embeds into `X/K'`
  have hz : K.arrow ≫ t.arrow ≫ cokernel.π (Subobject.push t K).arrow = 0 := by
    rw [← Category.assoc, ← Subobject.underlyingIso_inv_comp_push_arrow t K, Category.assoc,
      cokernel.condition, comp_zero]
  have hexact : (ShortComplex.mk K.arrow (t.arrow ≫ cokernel.π (Subobject.push t K).arrow) hz).Exact := by
    rw [ShortComplex.exact_iff_image_eq_kernel]
    change imageSubobject K.arrow = kernelSubobject (t.arrow ≫ cokernel.π (Subobject.push t K).arrow)
    rw [imageSubobject_mono, Subobject.mk_arrow, Subobject.kernelSubobject_arrow_comp_cokernel_π_push]
  have hmono : Mono (cokernel.desc K.arrow (t.arrow ≫ cokernel.π (Subobject.push t K).arrow) hz) :=
    hexact.mono_cokernelDesc
  -- the image of `t` in `X/K'` lies in `Z`
  have himgZ : (T.prop ⊓ F.prop) (imageSubobject (t.arrow ≫ cokernel.π (Subobject.push t K).arrow) : C) := by
    refine ⟨T.prop_of_iso (imageSubobjectIso _).symm
      (hT (factorThruImage _) inferInstance (T.prop_trace X)), ?_⟩
    have hle : imageSubobject (t.arrow ≫ cokernel.π (Subobject.push t K).arrow) ≤
        Subobject.mk (cokernel.desc K.arrow (t.arrow ≫ cokernel.π (Subobject.push t K).arrow) hz) :=
      imageSubobject_le _ (cokernel.π K.arrow ≫ (Subobject.underlyingIso _).inv)
        (by rw [Category.assoc, Subobject.underlyingIso_arrow, cokernel.π_desc])
    exact hF (Subobject.ofLE _ _ hle ≫ (Subobject.underlyingIso _).hom) inferInstance
      (F.prop_cokernel_reject _)
  -- `X/K' ∈ F`
  have hXF : F.prop (cokernel (Subobject.push t K).arrow) := by
    rw [hF', hb]
    exact himgZ
  -- `r_F(X) = K'`
  have hrX : F.reject X = Subobject.push t K := by
    apply le_antisymm
    · exact reject_le hF hXF
    · rw [le_reject_iff hF]
      exact fun g hY => hK'g g hY
  have hrt : F.reject X ≤ t := hrX ▸ Subobject.push_le t K
  refine ⟨hrt, ?_, ?_⟩
  · -- `r_F(t) = r_F(X)`: both are `K`
    rw [← hK]
    conv_lhs => rw [← Subobject.mk_ofLE_push t K]
    symm
    apply Subobject.mk_eq_mk_of_comm _ _ (Subobject.isoOfEq' hrX)
    rw [← cancel_mono t.arrow, Category.assoc, Subobject.ofLE_arrow, Subobject.isoOfEq'_hom_arrow,
      Subobject.ofLE_arrow]
  · -- `t(X/r_F(X)) = t(X)/r_F(X)`
    rw [hrX]
    exact hb

end Statement

end PretorsionImageClosed
