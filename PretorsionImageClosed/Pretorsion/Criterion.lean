module

public import PretorsionImageClosed.Pretorsion.TraceReject
public import PretorsionImageClosed.Subobjects.Quotients

/-!
# Verifying the trace–reject condition

Sufficient conditions for the trace–reject condition (2.4) at an object `X`,
used to check it on indecomposable objects whose traces and rejects are known
explicitly:

* `traceRejectCondition_of_prop`: `X ∈ F`;
* `traceRejectCondition_of_eq_top`: `r(X) = X = t(X)`;
* `traceRejectCondition_of_quotient`: the general case, with the quotient
  `X / r(X)` presented by an epimorphism `π : X ⟶ Q` whose kernel is `r(X)`;
  the third condition is then the equality `t(Q) = image(t(X) → Q)`.

`reject_coe_eq_mk_ofLE` verifies the second condition `r(t(X)) = r(X)` from
representatives of the subobjects.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PretorsionImageClosed.Statement

open CategoryTheory Limits Subcategory

variable {C : Type*} [Category C] [Abelian C] [HasLength C] {T F : Subcategory C} {X : C}

/-- `r(t) = r` as subobjects of `t`, from representatives: `t = mk ι`, `r = mk (κ ≫ ι)` and
`r_F(A) = mk κ`. -/
theorem reject_coe_eq_mk_ofLE (hF : F.IsSubobjectClosed) {t r : Subobject X} (h : r ≤ t)
    {A B : C} (ι : A ⟶ X) [Mono ι] (κ : B ⟶ A) [Mono κ] (ht : t = Subobject.mk ι)
    (hr : r = Subobject.mk (κ ≫ ι)) (hA : F.reject A = Subobject.mk κ) :
    F.reject (t : C) = Subobject.mk (Subobject.ofLE r t h) := by
  subst ht hr
  rw [reject_iso hF (Subobject.underlyingIso ι).symm, hA]
  symm
  apply Subobject.mk_eq_mk_of_comm _ _
    ((Subobject.underlyingIso (κ ≫ ι)).trans (Subobject.underlyingIso κ).symm)
  rw [← cancel_mono (Subobject.mk ι).arrow, Category.assoc, Subobject.ofLE_arrow, Iso.trans_hom,
    Iso.symm_hom, Iso.symm_hom, Category.assoc, Category.assoc, Subobject.underlyingIso_arrow,
    ← Category.assoc (Subobject.underlyingIso κ).inv, Subobject.underlyingIso_arrow,
    Subobject.underlyingIso_hom_comp_eq_mk]

/-- The trace–reject condition at an object of `F`. -/
theorem traceRejectCondition_of_prop (hT : T.IsQuotientClosed) (hF : F.IsSubobjectClosed)
    (hX : F.prop X) : TraceRejectCondition T F X := by
  have hr : F.reject X = ⊥ := (reject_eq_bot_iff hF).2 hX
  have h1 : F.reject X ≤ T.trace X := by rw [hr]; exact bot_le
  refine ⟨h1, ?_, ?_⟩
  · have ht : F.prop (T.trace X : C) := hF (T.trace X).arrow inferInstance hX
    rw [(reject_eq_bot_iff hF).2 ht]
    symm
    rw [Subobject.mk_eq_bot_iff_zero, ← cancel_mono (T.trace X).arrow, Subobject.ofLE_arrow,
      zero_comp, hr, Subobject.bot_arrow]
  · have key : ∀ r : Subobject X, r = ⊥ →
        T.trace (cokernel r.arrow) = imageSubobject ((T.trace X).arrow ≫ cokernel.π r.arrow) := by
      rintro _ rfl
      haveI : IsIso (cokernel.π (⊥ : Subobject X).arrow) := cokernel.π_of_zero Subobject.bot_arrow
      rw [trace_iso hT (asIso (cokernel.π (⊥ : Subobject X).arrow)), imageSubobject_mono]
      rfl
    exact key _ hr

/-- The trace–reject condition when `r(X) = X = t(X)`. -/
theorem traceRejectCondition_of_eq_top (hT : T.IsQuotientClosed) (hF : F.IsSubobjectClosed)
    (hr : F.reject X = ⊤) (ht : T.trace X = ⊤) : TraceRejectCondition T F X := by
  have h1 : F.reject X ≤ T.trace X := by rw [hr, ht]
  refine ⟨h1, ?_, ?_⟩
  · have key : ∀ (t r : Subobject X) (h : r ≤ t), t = ⊤ → r = ⊤ →
        F.reject (t : C) = Subobject.mk (Subobject.ofLE r t h) := by
      rintro _ _ h rfl rfl
      haveI : IsIso (Subobject.ofLE (⊤ : Subobject X) ⊤ h) := by
        rw [Subobject.ofLE_refl]
        infer_instance
      rw [Subobject.mk_eq_top_of_isIso, reject_iso hF (asIso (⊤ : Subobject X).arrow).symm, hr]
      exact Subobject.mk_eq_top_of_isIso _
    exact key _ _ h1 ht hr
  · have key : ∀ r : Subobject X, r = ⊤ →
        T.trace (cokernel r.arrow) = imageSubobject ((T.trace X).arrow ≫ cokernel.π r.arrow) := by
      rintro _ rfl
      exact Subobject.eq_of_isZero (isZero_zero C |>.of_iso (cokernel.ofEpi _)) _ _
    exact key _ hr

/-- The trace–reject condition from a presentation of the quotient `X / r(X)` by an
epimorphism `π : X ⟶ Q`. -/
theorem traceRejectCondition_of_quotient (hT : T.IsQuotientClosed) {Q : C} (π : X ⟶ Q) [Epi π]
    (hker : kernelSubobject π = F.reject X) (h1 : F.reject X ≤ T.trace X)
    (h2 : F.reject (T.trace X : C) = Subobject.mk (Subobject.ofLE _ _ h1))
    (h3 : T.trace Q = imageSubobject ((T.trace X).arrow ≫ π)) : TraceRejectCondition T F X := by
  refine ⟨h1, h2, ?_⟩
  have key : ∀ r : Subobject X, kernelSubobject π = r →
      T.trace (cokernel r.arrow) = imageSubobject ((T.trace X).arrow ≫ cokernel.π r.arrow) := by
    rintro _ rfl
    rw [trace_iso hT (cokernelKernelSubobjectArrowIso π).symm, h3,
      ← imageSubobject_comp_iso_hom _ (cokernelKernelSubobjectArrowIso π).symm]
    congr 1
    rw [Category.assoc, Iso.symm_hom, π_comp_cokernelKernelSubobjectArrowIso_inv]
  exact key _ hker


end PretorsionImageClosed.Statement
