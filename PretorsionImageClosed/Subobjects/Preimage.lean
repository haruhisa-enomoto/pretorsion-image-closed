module

public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Images, kernels and preimages of subobjects in an abelian category

Small lemmas about `Subobject` used throughout: the image of a morphism is the
kernel of its cokernel, a subobject is the kernel of its cokernel, images are
monotone, and the preimage `p⁻¹(U)` of a subobject `U` of the target of `p`,
defined as the kernel of `X ⟶ Y ⟶ Y/U`. For an epimorphism `p` the image of
`p⁻¹(U)` is `U`, and for a subobject `S` containing `ker p` the preimage of
`p(S)` is `S`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PretorsionImageClosed

open CategoryTheory Limits

variable {C : Type*} [Category C] [Abelian C]

theorem imageSubobject_eq_kernelSubobject_cokernel_π {X Y : C} (f : X ⟶ Y) :
    imageSubobject f = kernelSubobject (cokernel.π f) :=
  (ShortComplex.exact_iff_image_eq_kernel _).1 (ShortComplex.exact_cokernel f)

theorem kernelSubobject_cokernel_π_arrow {X : C} (L : Subobject X) :
    kernelSubobject (cokernel.π L.arrow) = L := by
  rw [← imageSubobject_eq_kernelSubobject_cokernel_π, imageSubobject_mono, Subobject.mk_arrow]

/-- A morphism killed by `X → X/L` factors through `L`. -/
theorem Subobject.factors_of_comp_cokernel_π_eq_zero {X W : C} (L : Subobject X) (f : W ⟶ X)
    (h : f ≫ cokernel.π L.arrow = 0) : L.Factors f := by
  rw [← kernelSubobject_cokernel_π_arrow L]
  exact kernelSubobject_factors _ _ h

/-- A subobject killed by `X → X/L` is contained in `L`. -/
theorem Subobject.le_of_arrow_comp_cokernel_π_eq_zero {X : C} {S L : Subobject X}
    (h : S.arrow ≫ cokernel.π L.arrow = 0) : S ≤ L :=
  (le_kernelSubobject _ _ h).trans_eq (kernelSubobject_cokernel_π_arrow L)

theorem Subobject.le_kernelSubobject_iff {X Y : C} (g : X ⟶ Y) (S : Subobject X) :
    S ≤ kernelSubobject g ↔ S.arrow ≫ g = 0 :=
  ⟨fun h => by rw [← Subobject.ofLE_arrow h, Category.assoc, kernelSubobject_arrow_comp, comp_zero],
   fun h => le_kernelSubobject _ _ h⟩

theorem imageSubobject_arrow_comp_le_of_le {X Y : C} {S S' : Subobject X} (h : S ≤ S')
    (p : X ⟶ Y) : imageSubobject (S.arrow ≫ p) ≤ imageSubobject (S'.arrow ≫ p) := by
  rw [← Subobject.ofLE_arrow h, Category.assoc]
  exact imageSubobject_comp_le _ _

theorem imageSubobject_factors_self {X Y : C} (f : X ⟶ Y) : (imageSubobject f).Factors f :=
  (Subobject.factors_iff _ _).2 ⟨factorThruImageSubobject f, imageSubobject_arrow_comp f⟩

theorem Subobject.factors_zero {X Y : C} (U : Subobject Y) : U.Factors (0 : X ⟶ Y) :=
  (Subobject.factors_iff _ _).2 ⟨0, zero_comp⟩

/-- Precomposing with an epimorphism does not change the image. -/
theorem imageSubobject_epi_comp {W X Y : C} (e : W ⟶ X) [Epi e] (f : X ⟶ Y) :
    imageSubobject (e ≫ f) = imageSubobject f := by
  rw [imageSubobject_eq_kernelSubobject_cokernel_π, imageSubobject_eq_kernelSubobject_cokernel_π f]
  have : cokernel.π (e ≫ f) = cokernel.π f ≫ (cokernelEpiComp e f).inv := by
    rw [Iso.eq_comp_inv]
    exact cokernel.π_desc _ _ _
  rw [this, kernelSubobject_comp_mono]

/-- The image of an epimorphism is everything. -/
theorem imageSubobject_eq_top_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] : imageSubobject f = ⊤ := by
  rw [← Subobject.isIso_arrow_iff_eq_top]
  have : Epi (imageSubobject f).arrow := by
    have h := imageSubobject_arrow_comp f
    exact epi_of_epi_fac h
  exact isIso_of_mono_of_epi _

/-- A morphism whose image is everything is an epimorphism. -/
theorem epi_of_imageSubobject_eq_top {X Y : C} (f : X ⟶ Y) (h : imageSubobject f = ⊤) : Epi f := by
  have : IsIso (imageSubobject f).arrow := (Subobject.isIso_arrow_iff_eq_top _).2 h
  rw [← imageSubobject_arrow_comp f]
  exact epi_comp _ _

/-- The isomorphism of underlying objects of two equal subobjects, built from
`ofLE` in both directions. -/
def Subobject.isoOfEq' {X : C} {S S' : Subobject X} (h : S = S') : (S : C) ≅ (S' : C) where
  hom := Subobject.ofLE S S' h.le
  inv := Subobject.ofLE S' S h.ge
  hom_inv_id := by rw [Subobject.ofLE_comp_ofLE, Subobject.ofLE_refl]
  inv_hom_id := by rw [Subobject.ofLE_comp_ofLE, Subobject.ofLE_refl]

@[reassoc (attr := simp)]
theorem Subobject.isoOfEq'_hom_arrow {X : C} {S S' : Subobject X} (h : S = S') :
    (Subobject.isoOfEq' h).hom ≫ S'.arrow = S.arrow :=
  Subobject.ofLE_arrow _

/-- A subobject of a subobject, pushed forward: `mk (K.arrow ≫ S.arrow)`. -/
theorem Subobject.mk_comp_arrow_le {X : C} (S : Subobject X) (K : Subobject (S : C)) :
    Subobject.mk (K.arrow ≫ S.arrow) ≤ S :=
  Subobject.mk_le_of_comm K.arrow rfl

/-- The subobject of `S` given by `mk (K.arrow ≫ S.arrow) ≤ S` is `K` again. -/
theorem Subobject.mk_ofLE_mk_comp_arrow {X : C} (S : Subobject X) (K : Subobject (S : C)) :
    Subobject.mk (Subobject.ofLE _ S (Subobject.mk_comp_arrow_le S K)) = K := by
  conv_rhs => rw [← Subobject.mk_arrow K]
  apply Subobject.mk_eq_mk_of_comm _ _ (Subobject.underlyingIso (K.arrow ≫ S.arrow))
  rw [← cancel_mono S.arrow, Category.assoc, Subobject.ofLE_arrow,
    Subobject.underlyingIso_hom_comp_eq_mk]

/-! ### Preimages -/

/-- The preimage `p⁻¹(U)` of a subobject `U` of `Y` under `p : X ⟶ Y`: the
kernel of `X ⟶ Y ⟶ Y/U`. -/
abbrev Subobject.preimage {X Y : C} (p : X ⟶ Y) (U : Subobject Y) : Subobject X :=
  kernelSubobject (p ≫ cokernel.π U.arrow)

theorem Subobject.preimage_factors_iff {X Y W : C} (p : X ⟶ Y) (U : Subobject Y) (f : W ⟶ X) :
    (Subobject.preimage p U).Factors f ↔ U.Factors (f ≫ p) := by
  rw [kernelSubobject_factors_iff, ← Category.assoc,
    ← kernelSubobject_factors_iff, kernelSubobject_cokernel_π_arrow]

theorem Subobject.le_preimage_iff {X Y : C} (p : X ⟶ Y) (U : Subobject Y) (S : Subobject X) :
    S ≤ Subobject.preimage p U ↔ U.Factors (S.arrow ≫ p) := by
  rw [Subobject.le_kernelSubobject_iff, ← Category.assoc,
    ← kernelSubobject_factors_iff, kernelSubobject_cokernel_π_arrow]

theorem Subobject.preimage_arrow_comp_factors {X Y : C} (p : X ⟶ Y) (U : Subobject Y) :
    U.Factors ((Subobject.preimage p U).arrow ≫ p) :=
  (Subobject.le_preimage_iff p U _).1 le_rfl

/-- The morphism `p⁻¹(U) → U` induced by `p`. -/
def Subobject.preimageToSubobject {X Y : C} (p : X ⟶ Y) (U : Subobject Y) :
    (Subobject.preimage p U : C) ⟶ (U : C) :=
  U.factorThru _ (Subobject.preimage_arrow_comp_factors p U)

@[reassoc (attr := simp)]
theorem Subobject.preimageToSubobject_arrow {X Y : C} (p : X ⟶ Y) (U : Subobject Y) :
    Subobject.preimageToSubobject p U ≫ U.arrow = (Subobject.preimage p U).arrow ≫ p :=
  Subobject.factorThru_arrow _ _ _

theorem Subobject.kernelSubobject_le_preimage {X Y : C} (p : X ⟶ Y) (U : Subobject Y) :
    kernelSubobject p ≤ Subobject.preimage p U := by
  rw [Subobject.le_preimage_iff, kernelSubobject_arrow_comp]
  exact Subobject.factors_zero U

/-- For an epimorphism `p`, the image of the preimage of `U` is `U`. -/
theorem Subobject.le_imageSubobject_preimage_arrow_comp {X Y : C} (p : X ⟶ Y) [Epi p]
    (U : Subobject Y) : U ≤ imageSubobject ((Subobject.preimage p U).arrow ≫ p) := by
  rw [imageSubobject_eq_kernelSubobject_cokernel_π, Subobject.le_kernelSubobject_iff]
  have hker : kernel.ι (p ≫ cokernel.π U.arrow) ≫
      (p ≫ cokernel.π ((Subobject.preimage p U).arrow ≫ p)) = 0 := by
    rw [← kernelSubobject_arrow' (p ≫ cokernel.π U.arrow), Category.assoc,
      ← Category.assoc (kernelSubobject (p ≫ cokernel.π U.arrow)).arrow, cokernel.condition,
      comp_zero]
  have hdesc := Abelian.comp_epiDesc (p ≫ cokernel.π U.arrow) _ hker
  have hc : cokernel.π U.arrow ≫ Abelian.epiDesc (p ≫ cokernel.π U.arrow) _ hker =
      cokernel.π ((Subobject.preimage p U).arrow ≫ p) := by
    rw [← cancel_epi p, ← Category.assoc]
    exact hdesc
  rw [← hc, ← Category.assoc, cokernel.condition, zero_comp]

/-- For an epimorphism `p`, the image of the preimage of `U` is exactly `U`. -/
theorem Subobject.imageSubobject_preimage_arrow_comp {X Y : C} (p : X ⟶ Y) [Epi p]
    (U : Subobject Y) : imageSubobject ((Subobject.preimage p U).arrow ≫ p) = U :=
  le_antisymm (imageSubobject_le _ _ (Subobject.preimageToSubobject_arrow p U))
    (Subobject.le_imageSubobject_preimage_arrow_comp p U)

/-- For an epimorphism `p`, the induced morphism `p⁻¹(U) → U` is an epimorphism. -/
instance Subobject.epi_preimageToSubobject {X Y : C} (p : X ⟶ Y) [Epi p] (U : Subobject Y) :
    Epi (Subobject.preimageToSubobject p U) := by
  have heq : Subobject.preimageToSubobject p U =
      factorThruImageSubobject ((Subobject.preimage p U).arrow ≫ p) ≫
        (Subobject.isoOfEq' (Subobject.imageSubobject_preimage_arrow_comp p U)).hom := by
    rw [← cancel_mono U.arrow, Category.assoc, Subobject.isoOfEq'_hom_arrow,
      imageSubobject_arrow_comp, Subobject.preimageToSubobject_arrow]
  rw [heq]
  exact epi_comp _ _

/-- For an epimorphism `p` and a subobject `S` containing `ker p`, the preimage
of the image of `S` is `S`. -/
theorem Subobject.preimage_imageSubobject_arrow_comp {X Y : C} (p : X ⟶ Y) [Epi p]
    (S : Subobject X) (hS : kernelSubobject p ≤ S) :
    Subobject.preimage p (imageSubobject (S.arrow ≫ p)) = S := by
  apply le_antisymm
  · have hk : kernel.ι p ≫ cokernel.π S.arrow = 0 := by
      rw [← kernelSubobject_arrow' p, Category.assoc, ← Subobject.ofLE_arrow hS, Category.assoc,
        cokernel.condition, comp_zero, comp_zero]
    have hVe : (imageSubobject (S.arrow ≫ p)).arrow ≫ Abelian.epiDesc p _ hk = 0 := by
      rw [← cancel_epi (factorThruImageSubobject (S.arrow ≫ p)), ← Category.assoc,
        imageSubobject_arrow_comp, Category.assoc, Abelian.comp_epiDesc, cokernel.condition,
        comp_zero]
    have hzero : (Subobject.preimage p (imageSubobject (S.arrow ≫ p))).arrow ≫
        cokernel.π S.arrow = 0 := by
      rw [← Abelian.comp_epiDesc p _ hk, ← Category.assoc,
        ← Subobject.factorThru_arrow _ _ (Subobject.preimage_arrow_comp_factors p _),
        Category.assoc, hVe, comp_zero]
    exact (le_kernelSubobject _ _ hzero).trans_eq (kernelSubobject_cokernel_π_arrow S)
  · rw [Subobject.le_preimage_iff]
    exact imageSubobject_factors_self _

/-! ### Subobjects of subobjects -/

/-- A subobject `K` of a subobject `S` of `X`, as a subobject of `X`. -/
abbrev Subobject.push {C : Type*} [Category C] {X : C} (S : Subobject X) (K : Subobject (S : C)) :
    Subobject X :=
  Subobject.mk (K.arrow ≫ S.arrow)

section Push

variable {C : Type*} [Category C] [Abelian C] {X : C} (S : Subobject X) (K : Subobject (S : C))

theorem Subobject.push_le : Subobject.push S K ≤ S :=
  Subobject.mk_le_of_comm K.arrow rfl

@[reassoc (attr := simp)]
theorem Subobject.underlyingIso_inv_comp_push_arrow :
    (Subobject.underlyingIso (K.arrow ≫ S.arrow)).inv ≫ (Subobject.push S K).arrow =
      K.arrow ≫ S.arrow :=
  Subobject.underlyingIso_arrow _

theorem Subobject.push_arrow :
    (Subobject.push S K).arrow = (Subobject.underlyingIso (K.arrow ≫ S.arrow)).hom ≫ K.arrow ≫ S.arrow :=
  (Subobject.underlyingIso_hom_comp_eq_mk _).symm

/-- The subobject of `S` given by `push S K ≤ S` is `K` again. -/
theorem Subobject.mk_ofLE_push :
    Subobject.mk (Subobject.ofLE _ S (Subobject.push_le S K)) = K := by
  conv_rhs => rw [← Subobject.mk_arrow K]
  apply Subobject.mk_eq_mk_of_comm _ _ (Subobject.underlyingIso (K.arrow ≫ S.arrow))
  rw [← cancel_mono S.arrow, Category.assoc, Subobject.ofLE_arrow, Subobject.push_arrow]

/-- The kernel of `S → X → X/(push S K)` is `K`. -/
theorem Subobject.kernelSubobject_arrow_comp_cokernel_π_push :
    kernelSubobject (S.arrow ≫ cokernel.π (Subobject.push S K).arrow) = K := by
  apply le_antisymm
  · have hfac : (Subobject.push S K).Factors
        ((kernelSubobject (S.arrow ≫ cokernel.π (Subobject.push S K).arrow)).arrow ≫ S.arrow) :=
      Subobject.factors_of_comp_cokernel_π_eq_zero _ _
        (by rw [Category.assoc, kernelSubobject_arrow_comp])
    have hw := Subobject.factorThru_arrow _ _ hfac
    conv_rhs => rw [← Subobject.mk_arrow K]
    refine Subobject.le_mk_of_comm (Subobject.factorThru _ _ hfac ≫
      (Subobject.underlyingIso (K.arrow ≫ S.arrow)).hom) ?_
    rw [← cancel_mono S.arrow, Category.assoc, Category.assoc, ← Subobject.push_arrow, hw]
  · exact le_kernelSubobject _ _ (by
      rw [← Category.assoc, ← Subobject.underlyingIso_inv_comp_push_arrow S K, Category.assoc,
        cokernel.condition, comp_zero])

end Push

end PretorsionImageClosed
