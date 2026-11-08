module

public import PretorsionImageClosed.IndecomposableClosures.ImageClosure
public import PretorsionImageClosed.IndecomposableClosures.Decomposition

/-!
# Section 4.3 for finite-dimensional algebras

For a finite-dimensional algebra `Λ` over a field `k`, the category
`mod Λ = FGModuleCat Λᵐᵒᵖ` has an indecomposable skeleton (`modSkeleton`): every
module has finite length (`isFiniteLength_mod`), and the endomorphism ring of
every module is a finite-dimensional `k`-algebra, hence Artinian
(`isArtinianRing_end_mod`). The results of `ImageClosure.lean` therefore apply
to `mod Λ`; `theorem_4_11` records Theorem 4.11 in this setting.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace PretorsionImageClosed

universe u

/-- Every finite-dimensional `Λ`-module has finite length. -/
theorem isFiniteLength_mod (k : Type u) [Field k] (Λ : Type u) [Ring Λ] [Algebra k Λ] [FiniteDimensional k Λ] :
    haveI := Statement.isNoetherianRing_mop k Λ
    ∀ X : FGModuleCat.{u} Λᵐᵒᵖ, IsFiniteLength Λᵐᵒᵖ X := by
  haveI := Statement.isNoetherianRing_mop k Λ
  haveI := isArtinianRing_mop k Λ
  intro X
  exact isFiniteLength_iff_isNoetherian_isArtinian.2 ⟨inferInstance, inferInstance⟩

/-- The endomorphism ring of a finite-dimensional `Λ`-module is Artinian. -/
theorem isArtinianRing_end_mod (k : Type u) [Field k] (Λ : Type u) [Ring Λ] [Algebra k Λ] [FiniteDimensional k Λ]
    (X : FGModuleCat.{u} Λᵐᵒᵖ) :
    IsArtinianRing (Module.End Λᵐᵒᵖ X) := by
  letI : Module k X := Module.compHom X (algebraMap k Λᵐᵒᵖ)
  haveI : IsScalarTower k Λᵐᵒᵖ X :=
    ⟨fun c r x => by
      show (c • r) • x = algebraMap k Λᵐᵒᵖ c • (r • x)
      rw [Algebra.smul_def, mul_smul]⟩
  haveI : Module.Finite k X := Module.Finite.trans Λᵐᵒᵖ X
  exact isArtinianRing_moduleEnd_of_finiteDimensional (K := k)

/-- The canonical indecomposable skeleton of `mod Λ`. -/
def modSkeleton (k : Type u) [Field k] (Λ : Type u) [Ring Λ] [Algebra k Λ] [FiniteDimensional k Λ] :
    haveI := Statement.isNoetherianRing_mop k Λ
    IndecomposableSkeleton.{u, u + 1, u} Λᵐᵒᵖ
      (FiniteLengthDecomposition.CanonicalIndecomposableIndex.{u, u} Λᵐᵒᵖ) :=
  haveI := Statement.isNoetherianRing_mop k Λ
  FiniteLengthDecomposition.canonicalIndecomposableSkeleton (isFiniteLength_mod k Λ)

/-- **Theorem 4.11** for `mod Λ`: the image closure on `ind Λ` is a finitary convex geometry
whose closed sets are the sets of indecomposables of the image-closed subcategories. -/
theorem theorem_4_11 (k : Type u) [Field k] (Λ : Type u) [Ring Λ] [Algebra k Λ] [FiniteDimensional k Λ] :
    haveI := Statement.isNoetherianRing_mop k Λ
    (modSkeleton k Λ).iClosure.IsFinitary ∧ (modSkeleton k Λ).iClosure.IsConvexGeometry ∧
      ∀ Z : Statement.Subcategory (Statement.Mod k Λ),
        Z.IsImageClosed ↔ (modSkeleton k Λ).iClosure.IsClosed ((modSkeleton k Λ).indOf Z) := by
  haveI := Statement.isNoetherianRing_mop k Λ
  haveI := isArtinianRing_mop k Λ
  haveI : ∀ i, IsArtinianRing (Module.End Λᵐᵒᵖ ((modSkeleton k Λ).obj i)) :=
    fun i => isArtinianRing_end_mod k Λ _
  exact ⟨(modSkeleton k Λ).iClosure_isFinitary,
    ⟨(modSkeleton k Λ).iClosure_isClosed_empty,
      (modSkeleton k Λ).iClosure_isAntiExchange (modSkeleton k Λ).qClosure_isAntiExchange
        (modSkeleton k Λ).sClosure_isAntiExchange⟩,
    fun Z => (modSkeleton k Λ).isImageClosed_iff_isClosed_indOf Z⟩

end PretorsionImageClosed
