module

public import PretorsionImageClosed.Pretorsion.Basic

/-!
# Lifting short preexact sequences along quotients

Let `π : X ⟶ V` be an epimorphism, and let `ι : A ⟶ X` be a subobject which is
the preimage of a subobject `u_V : B ⟶ V` along `π`, with `π` restricting to an
epimorphism `π_A : A ⟶ B`. If `B ⟶ V ⟶ F` is short `Z`-preexact and every
morphism from `A` to an object of `Z` vanishes on the kernel of `π_A`, then
`A ⟶ X ⟶ F` is short `Z`-preexact (`IsShortPreexact.of_quotient`).

This is the inductive step in the proof that the second components paired
with a fixed first component are closed under intersections (Proposition 3.2):
it replaces the manuscript's transport argument (3.1) and Lemma 3.1.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PretorsionImageClosed.Statement

open CategoryTheory Limits

variable {C : Type*} [Category C] [Abelian C] {Z : ObjectProperty C}

theorem IsShortPreexact.of_quotient {X V A B F : C} (π : X ⟶ V) [Epi π] (ι : A ⟶ X) [Mono ι]
    (πA : A ⟶ B) [Epi πA] (uV : B ⟶ V) [Mono uV] (vV : V ⟶ F) (hs : IsShortPreexact Z uV vV)
    (hcomm : πA ≫ uV = ι ≫ π)
    (hpull : ∀ {Y : C} (u' : Y ⟶ X) (w : Y ⟶ B), w ≫ uV = u' ≫ π → ∃ w' : Y ⟶ A, w' ≫ ι = u')
    (hK : ∀ {W : C} (g : A ⟶ W), Z W → kernel.ι πA ≫ g = 0) :
    IsShortPreexact Z ι (π ≫ vV) := by
  have htriv : IsTrivial Z (ι ≫ π ≫ vV) := by
    rw [← Category.assoc, ← hcomm, Category.assoc]
    exact hs.1.1.comp_left πA
  refine ⟨⟨htriv, fun {Y} u' hu' => ?_⟩, ⟨htriv, fun {Y} v' hv' => ?_⟩⟩
  · -- the prekernel property
    rw [← Category.assoc] at hu'
    obtain ⟨w, hw, -⟩ := hs.1.2 _ hu'
    obtain ⟨w', hw'⟩ := hpull u' w hw
    exact ⟨w', hw', fun w'' hw'' => (cancel_mono ι).1 (hw''.trans hw'.symm)⟩
  · -- the precokernel property
    obtain ⟨W, hW, g, h, hgh⟩ := hv'
    -- `v'` vanishes on the kernel of `π`
    obtain ⟨k, hk⟩ := hpull (kernel.ι π) 0 (by rw [zero_comp, kernel.condition])
    have hkπ : k ≫ πA = 0 := by
      rw [← cancel_mono uV, Category.assoc, hcomm, ← Category.assoc, hk, kernel.condition, zero_comp]
    have hker : kernel.ι π ≫ v' = 0 := by
      rw [← hk, Category.assoc, ← hgh, ← kernel.lift_ι πA k hkπ, Category.assoc, ← Category.assoc
        (kernel.ι πA), hK g hW, zero_comp, comp_zero]
    set d := Abelian.epiDesc π v' hker with hd
    have hπd : π ≫ d = v' := Abelian.comp_epiDesc π v' hker
    -- `u_V ≫ d` is trivial
    have hd' : IsTrivial Z (uV ≫ d) := by
      refine ⟨W, hW, Abelian.epiDesc πA g (hK g hW), h, ?_⟩
      rw [← cancel_epi πA, ← Category.assoc, Abelian.comp_epiDesc, hgh, ← Category.assoc, hcomm,
        Category.assoc, hπd]
    obtain ⟨e, he, huniq⟩ := hs.2.2 d hd'
    have he0 : vV ≫ e = d := he
    refine ⟨e, ?_, fun e' he' => huniq e' ?_⟩
    · show (π ≫ vV) ≫ e = v'
      rw [Category.assoc, he0, hπd]
    · have he1 : (π ≫ vV) ≫ e' = v' := he'
      show vV ≫ e' = d
      rw [← cancel_epi π, ← Category.assoc, he1, hπd]

end PretorsionImageClosed.Statement
