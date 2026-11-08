module

public import PretorsionImageClosed.Length.Basic
public import PretorsionImageClosed.Modules.FiniteModules
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# The length function on finitely generated modules

Over a ring that is both Noetherian and Artinian, every finitely generated
module has finite composition length, and the composition length is a length
function on `FGModuleCat R` in the sense of `HasLength`. Finite-dimensional
algebras over a field are such rings, so this covers `mod Λ`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PretorsionImageClosed

open CategoryTheory Limits

theorem ENat.toNat_lt_toNat_of_lt {m n : ℕ∞} (h : m < n) (hn : n ≠ ⊤) : m.toNat < n.toNat := by
  have hm : m ≠ ⊤ := ne_top_of_lt h
  exact Nat.cast_lt.1 (by rwa [ENat.natCast_toNat hm, ENat.natCast_toNat hn])

namespace FGModuleCat

variable {R : Type*} [Ring R] [IsNoetherianRing R] [IsArtinianRing R]

/-- The composition length of a finitely generated module over a Noetherian
Artinian ring, as a natural number. -/
def moduleLength (X : FGModuleCat R) : ℕ := (Module.length R X).toNat

theorem moduleLength_coe (X : FGModuleCat R) : (moduleLength X : ℕ∞) = Module.length R X :=
  ENat.natCast_toNat Module.length_ne_top

theorem moduleLength_eq_zero_iff (X : FGModuleCat R) : moduleLength X = 0 ↔ Subsingleton X := by
  rw [← Module.length_eq_zero_iff (R := R), ← moduleLength_coe]
  exact_mod_cast Iff.rfl

instance : HasLength (FGModuleCat R) where
  length := moduleLength
  length_eq_zero_iff X := by rw [moduleLength_eq_zero_iff, isZero_iff_subsingleton]
  length_eq_of_iso e := by
    change moduleLength _ = moduleLength _
    rw [moduleLength, moduleLength, LinearEquiv.length_eq (FGModuleCat.isoToLinearEquiv e)]
  length_lt_of_mono {X Y} f hf hni := by
    change moduleLength X < moduleLength Y
    have hinj : Function.Injective f.hom.hom := (mono_iff_injective f).1 hf
    have hns : LinearMap.range f.hom.hom ≠ ⊤ := fun h =>
      hni ((isIso_iff_bijective f).2 ⟨hinj, LinearMap.range_eq_top.1 h⟩)
    have h1 : Module.length R X = Module.length R (LinearMap.range f.hom.hom) :=
      LinearEquiv.length_eq (LinearEquiv.ofInjective f.hom.hom hinj)
    have h2 := Submodule.length_lt hns
    rw [moduleLength, moduleLength, h1]
    exact ENat.toNat_lt_toNat_of_lt h2 Module.length_ne_top
  length_lt_of_epi {X Y} f hf hni := by
    change moduleLength Y < moduleLength X
    have hsurj : Function.Surjective f.hom.hom := (epi_iff_surjective f).1 hf
    have hni' : LinearMap.ker f.hom.hom ≠ ⊥ := fun h =>
      hni ((isIso_iff_bijective f).2 ⟨LinearMap.ker_eq_bot.1 h, hsurj⟩)
    have hadd : Module.length R X = Module.length R (LinearMap.ker f.hom.hom) + Module.length R Y :=
      Module.length_eq_add_of_exact (LinearMap.ker f.hom.hom).subtype f.hom.hom
        (Submodule.subtype_injective _) hsurj (LinearMap.exact_subtype_ker_map f.hom.hom)
    have hpos : 0 < Module.length R (LinearMap.ker f.hom.hom) :=
      Module.length_pos_iff.2 (Submodule.nontrivial_iff_ne_bot.2 hni')
    have hlt : Module.length R Y < Module.length R X := by
      rw [hadd]
      exact ENat.lt_add_left Module.length_ne_top hpos
    exact ENat.toNat_lt_toNat_of_lt hlt Module.length_ne_top

end FGModuleCat

/-- A finite-dimensional algebra over a field is Artinian, and so is its
opposite ring; together with `Statement.isNoetherianRing_mop` this gives the
length function on `mod Λ`. -/
theorem isArtinianRing_mop (k : Type*) [Field k] (Λ : Type*) [Ring Λ] [Algebra k Λ]
    [FiniteDimensional k Λ] : IsArtinianRing Λᵐᵒᵖ :=
  isArtinian_of_tower k (inferInstance : IsArtinian k Λᵐᵒᵖ)

end PretorsionImageClosed
