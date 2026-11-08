module

public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Category.FGModuleCat.Limits
public import Mathlib.Algebra.Category.FGModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Monomorphisms, epimorphisms and zero objects of finitely generated modules

For a Noetherian ring `R`, a morphism of `FGModuleCat R` is a monomorphism iff
it is injective, an epimorphism iff it is surjective, and an isomorphism iff it
is bijective; an object is zero iff its carrier is a subsingleton. These
transfer the corresponding facts about `ModuleCat R` along the forgetful
functor, which is fully faithful and preserves finite limits and colimits.
The underlying linear map of a finite sum of morphisms is the sum of the
underlying linear maps (`hom_hom_sum`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PretorsionImageClosed

open CategoryTheory Limits

namespace FGModuleCat

variable {R : Type*} [Ring R] [IsNoetherianRing R]

theorem mono_iff_injective {X Y : FGModuleCat R} (f : X ⟶ Y) : Mono f ↔ Function.Injective f.hom.hom := by
  constructor
  · intro hf
    have : Mono ((forget₂ (FGModuleCat R) (ModuleCat R)).map f) := inferInstance
    exact (ModuleCat.mono_iff_injective _).1 this
  · intro hf
    have : Mono ((forget₂ (FGModuleCat R) (ModuleCat R)).map f) :=
      (ModuleCat.mono_iff_injective _).2 hf
    exact (forget₂ (FGModuleCat R) (ModuleCat R)).mono_of_mono_map this

theorem epi_iff_surjective {X Y : FGModuleCat R} (f : X ⟶ Y) : Epi f ↔ Function.Surjective f.hom.hom := by
  constructor
  · intro hf
    have : Epi ((forget₂ (FGModuleCat R) (ModuleCat R)).map f) := inferInstance
    exact (ModuleCat.epi_iff_surjective _).1 this
  · intro hf
    have : Epi ((forget₂ (FGModuleCat R) (ModuleCat R)).map f) :=
      (ModuleCat.epi_iff_surjective _).2 hf
    exact (forget₂ (FGModuleCat R) (ModuleCat R)).epi_of_epi_map this

theorem isIso_iff_bijective {X Y : FGModuleCat R} (f : X ⟶ Y) : IsIso f ↔ Function.Bijective f.hom.hom := by
  constructor
  · intro hf
    exact ⟨(mono_iff_injective f).1 inferInstance, (epi_iff_surjective f).1 inferInstance⟩
  · rintro ⟨hi, hs⟩
    haveI := (mono_iff_injective f).2 hi
    haveI := (epi_iff_surjective f).2 hs
    exact isIso_of_mono_of_epi f

theorem range_eq_top_of_epi {X Y : FGModuleCat R} (f : X ⟶ Y) [Epi f] :
    LinearMap.range f.hom.hom = ⊤ :=
  LinearMap.range_eq_top.2 ((epi_iff_surjective f).1 inferInstance)

theorem ker_eq_bot_of_mono {X Y : FGModuleCat R} (f : X ⟶ Y) [Mono f] :
    LinearMap.ker f.hom.hom = ⊥ :=
  LinearMap.ker_eq_bot.2 ((mono_iff_injective f).1 inferInstance)

omit [IsNoetherianRing R] in
/-- The underlying linear map of a finite sum of morphisms. -/
theorem hom_hom_sum {J : Type*} [Fintype J] {X Y : FGModuleCat R} (f : J → (X ⟶ Y)) :
    (∑ j, f j).hom.hom = ∑ j, (f j).hom.hom := by
  have h : (∑ j, f j).hom = ∑ j, (f j).hom :=
    map_sum (InducedCategory.homAddEquiv : (X ⟶ Y) ≃+ (X.obj ⟶ Y.obj)) f Finset.univ
  rw [h, ModuleCat.hom_sum]

omit [IsNoetherianRing R] in
theorem hom_hom_sum_apply {J : Type*} [Fintype J] {X Y : FGModuleCat R} (f : J → (X ⟶ Y))
    (x : X) : (∑ j, f j).hom.hom x = ∑ j, (f j).hom.hom x := by
  rw [hom_hom_sum, LinearMap.sum_apply]

theorem isZero_iff_subsingleton (X : FGModuleCat R) : IsZero X ↔ Subsingleton X := by
  rw [IsZero.iff_id_eq_zero]
  constructor
  · intro h
    refine ⟨fun x y => ?_⟩
    have hx : x = 0 := congrArg (fun g : X ⟶ X => g.hom.hom x) h
    have hy : y = 0 := congrArg (fun g : X ⟶ X => g.hom.hom y) h
    rw [hx, hy]
  · intro h
    ext x
    exact Subsingleton.elim _ _

end FGModuleCat

end PretorsionImageClosed
