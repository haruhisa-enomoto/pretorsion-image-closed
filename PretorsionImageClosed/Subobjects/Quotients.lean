module

public import PretorsionImageClosed.Subobjects.Preimage

/-!
# Quotients by subobjects

Generalities on cokernels of subobject inclusions in an abelian category:

* an epimorphism `π : X ⟶ Q` identifies `Q` with the quotient of `X` by the
  kernel subobject of `π` (`cokernelKernelSubobjectArrowIso`);
* images transport along isomorphisms of the target
  (`imageSubobject_comp_iso_hom`);
* a zero object has only one subobject (`Subobject.eq_of_isZero`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PretorsionImageClosed

open CategoryTheory Limits

variable {C : Type*} [Category C] [Abelian C]

/-- The short complex `ker π → X → Q` is exact. -/
theorem exact_kernelSubobject_arrow {X Q : C} (π : X ⟶ Q) :
    (ShortComplex.mk (kernelSubobject π).arrow π (kernelSubobject_arrow_comp π)).Exact := by
  rw [ShortComplex.exact_iff_image_eq_kernel]
  change imageSubobject (kernelSubobject π).arrow = kernelSubobject π
  rw [imageSubobject_mono, Subobject.mk_arrow]

instance mono_cokernelDesc_kernelSubobject_arrow {X Q : C} (π : X ⟶ Q) :
    Mono (cokernel.desc (kernelSubobject π).arrow π (kernelSubobject_arrow_comp π)) :=
  (exact_kernelSubobject_arrow π).mono_cokernelDesc

instance epi_cokernelDesc_kernelSubobject_arrow {X Q : C} (π : X ⟶ Q) [Epi π] :
    Epi (cokernel.desc (kernelSubobject π).arrow π (kernelSubobject_arrow_comp π)) :=
  epi_of_epi_fac (cokernel.π_desc _ _ _)

/-- An epimorphism `π : X ⟶ Q` identifies `Q` with `X / ker π`. -/
def cokernelKernelSubobjectArrowIso {X Q : C} (π : X ⟶ Q) [Epi π] :
    cokernel (kernelSubobject π).arrow ≅ Q :=
  haveI : IsIso (cokernel.desc (kernelSubobject π).arrow π (kernelSubobject_arrow_comp π)) :=
    isIso_of_mono_of_epi _
  asIso (cokernel.desc (kernelSubobject π).arrow π (kernelSubobject_arrow_comp π))

@[reassoc (attr := simp)]
theorem π_comp_cokernelKernelSubobjectArrowIso_hom {X Q : C} (π : X ⟶ Q) [Epi π] :
    cokernel.π (kernelSubobject π).arrow ≫ (cokernelKernelSubobjectArrowIso π).hom = π :=
  cokernel.π_desc _ _ _

theorem π_comp_cokernelKernelSubobjectArrowIso_inv {X Q : C} (π : X ⟶ Q) [Epi π] :
    π ≫ (cokernelKernelSubobjectArrowIso π).inv = cokernel.π (kernelSubobject π).arrow := by
  rw [Iso.comp_inv_eq, π_comp_cokernelKernelSubobjectArrowIso_hom]

/-- The image of `f ≫ e` for an isomorphism `e` is the transport of the image of `f`. -/
theorem imageSubobject_comp_iso_hom {X Y Y' : C} (f : X ⟶ Y) (e : Y ≅ Y') :
    imageSubobject (f ≫ e.hom) = Subobject.mk ((imageSubobject f).arrow ≫ e.hom) := by
  conv_lhs => rw [← Subobject.mk_arrow (imageSubobject (f ≫ e.hom))]
  apply Subobject.mk_eq_mk_of_comm _ _ (imageSubobjectCompIso f e.hom)
  rw [← Category.assoc, imageSubobjectCompIso_hom_arrow, Category.assoc, IsIso.Iso.inv_hom,
    Iso.inv_hom_id, Category.comp_id]

/-- A zero object has a unique subobject. -/
theorem Subobject.eq_of_isZero {X : C} (hX : IsZero X) (S S' : Subobject X) : S = S' :=
  le_antisymm (Subobject.le_of_comm 0 (hX.eq_of_tgt _ _)) (Subobject.le_of_comm 0 (hX.eq_of_tgt _ _))

end PretorsionImageClosed
