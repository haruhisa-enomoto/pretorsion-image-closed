module

public import PretorsionImageClosed.Pretorsion.FixedMiddle
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Torsion pairs

* **Definition 2.4**: torsion pairs (`IsTorsionPair`).
* **Proposition 2.5**: the torsion pairs are the pretorsion theories with
  `T ∩ F = 0` (`isTorsionPair_iff`). When `Z = 0`, `Z`-trivial morphisms are
  the zero morphisms, and short `Z`-preexact sequences are short exact
  sequences.
* **Corollary 3.9**: the torsion pairs form a complete sublattice of the
  pretorsion theories containing the least and greatest elements
  (`IsTorsion.sInf`, `IsTorsion.sSup`, `isTorsion_bot`, `isTorsion_top`), and
  a torsion pair is determined by, and ordered by, its first component
  (`IsTorsion.le_iff`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PretorsionImageClosed.Statement

open CategoryTheory Limits Subcategory ZeroObject

variable {C : Type*} [Category C] [Abelian C]

/-- **Definition 2.4.** `(T, F)` is a torsion pair: there are no nonzero morphisms from `T`
to `F`, and every object `X` sits in a short exact sequence `0 → T' → X → F' → 0` with
`T' ∈ T` and `F' ∈ F`. -/
def IsTorsionPair (T F : ObjectProperty C) : Prop :=
  (∀ {X Y : C} (f : X ⟶ Y), T X → F Y → f = 0) ∧
    ∀ X : C, ∃ (T' F' : C) (u : T' ⟶ X) (v : X ⟶ F') (w : u ≫ v = 0),
      T T' ∧ F F' ∧ (ShortComplex.mk u v w).ShortExact

/-- With `Z` consisting of zero objects, the `Z`-trivial morphisms are the zero morphisms. -/
theorem isTrivial_iff_eq_zero {Z : Subcategory C} (hZ : ∀ X, Z.prop X → IsZero X) {X Y : C}
    (f : X ⟶ Y) : IsTrivial Z.prop f ↔ f = 0 := by
  constructor
  · rintro ⟨W, hW, g, h, rfl⟩
    rw [(hZ W hW).eq_zero_of_src h, comp_zero]
  · rintro rfl
    exact ⟨0, Z.prop_zero, 0, 0, by rw [comp_zero]⟩

/-- **Proposition 2.5.** `(T, F)` is a torsion pair iff it is a pretorsion theory with
`T ∩ F = 0`. -/
theorem isTorsionPair_iff (T F : Subcategory C) :
    IsTorsionPair T.prop F.prop ↔
      IsPretorsionTheory T.prop F.prop ∧ ∀ X, (T.prop ⊓ F.prop) X → IsZero X := by
  constructor
  · rintro ⟨h0, hseq⟩
    have hZ : ∀ X, (T ⊓ F).prop X → IsZero X := fun X hX => by
      rw [IsZero.iff_id_eq_zero]
      exact h0 (𝟙 X) hX.1 hX.2
    have htriv : ∀ {X Y : C} (f : X ⟶ Y), IsTrivial (T.prop ⊓ F.prop) f ↔ f = 0 :=
      fun f => isTrivial_iff_eq_zero (Z := T ⊓ F) hZ f
    refine ⟨⟨fun f hX hY => (htriv f).2 (h0 f hX hY), fun X => ?_⟩, hZ⟩
    obtain ⟨T', F', u, v, w, hT', hF', hSE⟩ := hseq X
    haveI := hSE.mono_f
    haveI := hSE.epi_g
    have hK := hSE.exact.fIsKernel
    have hC := hSE.exact.gIsCokernel
    refine ⟨T', F', u, v, hT', hF', ⟨⟨(htriv _).2 w, fun {Y} u' hu' => ?_⟩,
      ⟨(htriv _).2 w, fun {Y} v' hv' => ?_⟩⟩⟩
    · obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' hK u' ((htriv _).1 hu')
      exact ⟨l, hl, fun l' hl' => (cancel_mono u).1 (hl'.trans hl.symm)⟩
    · obtain ⟨l, hl⟩ := CokernelCofork.IsColimit.desc' hC v' ((htriv _).1 hv')
      exact ⟨l, hl, fun l' hl' => (cancel_epi v).1 (hl'.trans hl.symm)⟩
  · rintro ⟨hP, hZ⟩
    have htriv : ∀ {X Y : C} (f : X ⟶ Y), IsTrivial (T.prop ⊓ F.prop) f ↔ f = 0 :=
      fun f => isTrivial_iff_eq_zero (Z := T ⊓ F) hZ f
    refine ⟨fun f hX hY => (htriv f).1 (hP.1 f hX hY), fun X => ?_⟩
    obtain ⟨T', F', u, v, hT', hF', hu, hv⟩ := hP.2 X
    have w : u ≫ v = 0 := (htriv _).1 hu.1
    haveI := hu.mono
    haveI := hv.epi
    refine ⟨T', F', u, v, w, hT', hF', ⟨?_⟩⟩
    apply ShortComplex.exact_of_f_is_kernel
    refine KernelFork.IsLimit.ofι _ _ (fun g hg => (hu.2 g ((htriv _).2 hg)).exists.choose)
      (fun g hg => (hu.2 g ((htriv _).2 hg)).exists.choose_spec) (fun g hg m hm => ?_)
    exact (hu.2 g ((htriv _).2 hg)).unique hm (hu.2 g ((htriv _).2 hg)).exists.choose_spec

/-! ### Corollary 3.9 -/

variable [HasLength C]

namespace PretorsionTheory

/-- A pretorsion theory which is a torsion pair. -/
def IsTorsion (P : PretorsionTheory C) : Prop := IsTorsionPair P.T.prop P.F.prop

theorem isTorsion_iff_middle (P : PretorsionTheory C) :
    P.IsTorsion ↔ P.middle = (⊥ : Subcategory C).prop := by
  rw [IsTorsion, isTorsionPair_iff]
  refine ⟨fun h => ?_, fun h => ⟨P.isPretorsionTheory, fun X hX => ?_⟩⟩
  · funext X
    apply propext
    exact ⟨h.2 X, fun hX => ⟨P.T.prop_of_isZero hX, P.F.prop_of_isZero hX⟩⟩
  · have : P.middle X := hX
    rw [h] at this
    exact this

/-- **Corollary 3.9**: nonempty meets of torsion pairs are torsion pairs. -/
theorem IsTorsion.sInf {S : Set (PretorsionTheory C)} (hne : S.Nonempty)
    (h : ∀ P ∈ S, P.IsTorsion) : (sInf S).IsTorsion := by
  obtain ⟨P₀, hP₀⟩ := hne
  rw [isTorsion_iff_middle]
  exact sInf_middle hP₀ fun P hP => (isTorsion_iff_middle P).1 (h P hP)

/-- **Corollary 3.9**: nonempty joins of torsion pairs are torsion pairs. -/
theorem IsTorsion.sSup {S : Set (PretorsionTheory C)} (hne : S.Nonempty)
    (h : ∀ P ∈ S, P.IsTorsion) : (sSup S).IsTorsion := by
  obtain ⟨P₀, hP₀⟩ := hne
  rw [isTorsion_iff_middle]
  exact sSup_middle hP₀ fun P hP => (isTorsion_iff_middle P).1 (h P hP)

/-- **Corollary 3.9**: `(0, mod)` is a torsion pair. -/
theorem isTorsion_bot : (⊥ : PretorsionTheory C).IsTorsion := by
  rw [isTorsion_iff_middle, bot_eq]
  funext X
  apply propext
  exact ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩

/-- **Corollary 3.9**: `(mod, 0)` is a torsion pair. -/
theorem isTorsion_top : (⊤ : PretorsionTheory C).IsTorsion := by
  rw [isTorsion_iff_middle, top_eq]
  funext X
  apply propext
  exact ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩

/-- **Corollary 3.9**: torsion pairs are ordered by their first components, so the
first component determines a torsion pair. -/
theorem IsTorsion.le_iff {P Q : PretorsionTheory C} (hP : P.IsTorsion) (hQ : Q.IsTorsion) :
    P ≤ Q ↔ P.T ≤ Q.T := by
  refine ⟨fun h => h.1, fun h => ⟨h, fun Y hY => ?_⟩⟩
  have hQm := (isTorsion_iff_middle Q).1 hQ
  have hPm := (isTorsion_iff_middle P).1 hP
  have hz : IsZero (Q.T.trace Y : C) := by
    have := (Q.isPretorsionTheory.prop_iff_prop_trace Y).1 hY
    have h' : Q.middle (Q.T.trace Y : C) := this
    rw [hQm] at h'
    exact h'
  have hle : P.T.trace Y ≤ Q.T.trace Y :=
    le_trace Q.isPretorsionTheory.isQuotientClosed (h _ (P.T.prop_trace Y))
  have hz' : IsZero (P.T.trace Y : C) := IsZero.of_mono (Subobject.ofLE _ _ hle) hz
  exact (P.isPretorsionTheory.prop_iff_prop_trace Y).2
    ⟨P.T.prop_of_isZero hz', P.F.prop_of_isZero hz'⟩

theorem IsTorsion.eq_of_T_eq {P Q : PretorsionTheory C} (hP : P.IsTorsion) (hQ : Q.IsTorsion)
    (h : P.T = Q.T) : P = Q :=
  le_antisymm ((hP.le_iff hQ).2 h.le) ((hQ.le_iff hP).2 h.ge)

end PretorsionTheory

end PretorsionImageClosed.Statement
