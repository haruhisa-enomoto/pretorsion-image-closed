module

public import PretorsionImageClosed.IndecomposableClosures.Subcategories
public import PretorsionImageClosed.IndecomposableClosures.SplitProjective
public import PretorsionImageClosed.ConvexGeometry.Compact
public import PretorsionImageClosed.Realizations.LeastRealization
public import PretorsionImageClosed.Length.Modules

/-!
# The convex geometry of image closure

Section 4.3 of the manuscript, for an indecomposable skeleton `σ` of
`FGModuleCat R` over a Noetherian and Artinian ring `R` whose indecomposable
representatives have Artinian endomorphism rings (`mod Λ` for a
finite-dimensional algebra `Λ` is the case of the manuscript).

* (4.3) The image closure `icl(S) = qcl(S) ∩ scl(S)` on sets of
  representatives (`iClosure`).
* **Theorem 4.11.** `icl` is a finitary convex geometry
  (`iClosure_isFinitary`, `iClosure_isClosed_empty`,
  `iClosure_isAntiExchange`) whose closed sets correspond to the image-closed
  subcategories (`isImageClosed_iff_isClosed_indOf`, `imageClosedOrderIso`).
* **Definition 4.12.** Splitting projective and splitting injective objects of
  a subcategory (`IsSplittingProjective`, `IsSplittingInjective`).
* **Proposition 4.13** (`not_mem_qClosure_sdiff_iff`,
  `not_mem_sClosure_sdiff_iff`, `extremePoints_iff_isImageClosed`,
  `extremePoints_iff_splitting`).
* **Corollary 4.14.** Meets and joins of image-closed subcategories
  (`isGLB_iInf`, `isLUB_join`); the unique minimal generating set of a finite
  image-closed subcategory (`iClosure_splitting_eq`, `splitting_subset`); covers
  add exactly one indecomposable (`exists_sdiff_eq_singleton_of_covby`,
  `ncard_of_covby`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Set

namespace PretorsionImageClosed.IndecomposableSkeleton

universe u v w

variable {R : Type u} [Ring R] [IsNoetherianRing R] {ι : Type v}
  (σ : IndecomposableSkeleton.{u, v, w} R ι)

attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

/-! ### The image closure (4.3) -/

/-- `icl(S) = qcl(S) ∩ scl(S)`. -/
def iSet (S : Set ι) : Set ι := σ.qSet S ∩ σ.sSet S

/-- The image closure (4.3) as a closure operator. -/
def iClosure : SetClosure ι where
  toFun := σ.iSet
  monotone' _ _ h := inter_subset_inter (qSet_monotone σ h) (sSet_monotone σ h)
  le_closure' S := subset_inter (subset_qSet σ S) (subset_sSet σ S)
  idempotent' S := by
    apply Subset.antisymm
    · refine subset_inter ?_ ?_
      · exact inter_subset_left.trans
          ((qSet_monotone σ inter_subset_left).trans (qSet_idempotent σ S).le)
      · exact inter_subset_right.trans
          ((sSet_monotone σ inter_subset_right).trans (sSet_idempotent σ S).le)
    · exact subset_inter (subset_qSet σ _) (subset_sSet σ _)

theorem iClosure_apply (S : Set ι) : σ.iClosure S = σ.qClosure S ∩ σ.sClosure S := rfl

theorem mem_iClosure_iff (S : Set ι) (i : ι) :
    i ∈ σ.iClosure S ↔
      Statement.Gen (σ.addOf S) (σ.obj i) ∧ Statement.Cogen (σ.addOf S) (σ.obj i) :=
  and_congr (σ.mem_qSet_iff S i) (σ.mem_sSet_iff S i)

/-! ### Theorem 4.11 -/

/-- Theorem 4.11: `icl` is finitary. -/
theorem iClosure_isFinitary : σ.iClosure.IsFinitary := by
  intro S j hj
  obtain ⟨T₁, hT₁, hT₁S, h₁⟩ := qSet_finite_witness σ hj.1
  obtain ⟨T₂, hT₂, hT₂S, h₂⟩ := sSet_finite_witness σ hj.2
  exact ⟨T₁ ∪ T₂, hT₁.union hT₂, union_subset hT₁S hT₂S,
    qSet_monotone σ subset_union_left h₁, sSet_monotone σ subset_union_right h₂⟩

/-- Theorem 4.11: `icl(∅) = ∅`. -/
theorem iClosure_isClosed_empty : σ.iClosure.IsClosed ∅ := by
  rw [ClosureOperator.isClosed_iff]
  show σ.qSet ∅ ∩ σ.sSet ∅ = ∅
  rw [qSet_empty, empty_inter]

/-- Theorem 4.11: anti-exchange for `icl` follows from anti-exchange for `qcl` and `scl`. -/
theorem iClosure_isAntiExchange (hq : σ.qClosure.IsAntiExchange)
    (hs : σ.sClosure.IsAntiExchange) : σ.iClosure.IsAntiExchange := by
  intro C x y hC hxC hyC hxy hx hy
  have hCeq : σ.qSet C ∩ σ.sSet C = C := hC.closure_eq
  -- one of the two closures already excludes `x`
  have key : ∀ (c : SetClosure ι), c.IsAntiExchange → x ∉ c C →
      x ∈ c (insert y C) → y ∈ c (insert x C) → False := by
    intro c hc hxc hxy' hyx'
    by_cases hyc : y ∈ c C
    · apply hxc
      have : insert y C ⊆ c C := insert_subset hyc (c.le_closure C)
      exact ((c.monotone this).trans (c.idempotent C).le) hxy'
    · refine hc (c.isClosed_closure C) hxc hyc hxy ?_ ?_
      · exact c.monotone (insert_subset_insert (c.le_closure C)) hxy'
      · exact c.monotone (insert_subset_insert (c.le_closure C)) hyx'
  have hx' : x ∉ σ.qSet C ∩ σ.sSet C := by rw [hCeq]; exact hxC
  rcases not_and_or.1 hx' with hxq | hxs
  · exact key σ.qClosure hq hxq hx.1 hy.1
  · exact key σ.sClosure hs hxs hx.2 hy.2

variable [IsArtinianRing R]

omit [IsArtinianRing R] in
theorem gen_of_retract {Z : Statement.Subcategory (FGModuleCat.{w} R)}
    {X Y : FGModuleCat.{w} R} (h : Retract Y X) (hX : Statement.Gen Z X) : Statement.Gen Z Y := by
  obtain ⟨N, hN, p, hp⟩ := hX
  exact ⟨N, hN, p ≫ h.r, epi_comp _ _⟩

omit [IsArtinianRing R] in
theorem cogen_of_retract {Z : Statement.Subcategory (FGModuleCat.{w} R)}
    {X Y : FGModuleCat.{w} R} (h : Retract Y X) (hX : Statement.Cogen Z X) :
    Statement.Cogen Z Y := by
  obtain ⟨N, hN, i, hi⟩ := hX
  exact ⟨N, hN, h.i ≫ i, mono_comp _ _⟩

/-- Theorem 4.11: a subcategory is image-closed iff its set of indecomposable representatives
is `icl`-closed. -/
theorem isImageClosed_iff_isClosed_indOf (Z : Statement.Subcategory (FGModuleCat.{w} R)) :
    Z.IsImageClosed ↔ σ.iClosure.IsClosed (σ.indOf Z) := by
  rw [Statement.isImageClosed_iff_eq_gen_inf_cogen, ClosureOperator.isClosed_iff_closure_le]
  constructor
  · intro h i hi
    rw [mem_iClosure_iff, addOf_indOf] at hi
    show Z.prop (σ.obj i)
    rw [h]
    exact hi
  · intro h
    apply le_antisymm (Statement.le_gen_inf_cogen Z)
    intro X hX
    rw [σ.prop_iff_inAdd_indOf Z X]
    obtain ⟨n, a, ⟨e⟩⟩ := σ.decomposes X
    refine ⟨{ index := FintypeCat.of (Fin n), label := a, mem := (fun t => ?_), iso := e }⟩
    let rt : Retract (σ.obj (a t)) X :=
      { i := biproduct.ι (fun j : Fin n ↦ σ.obj (a j)) t ≫ e.inv
        r := e.hom ≫ biproduct.π (fun j : Fin n ↦ σ.obj (a j)) t
        retract := by simp }
    apply h
    rw [mem_iClosure_iff, addOf_indOf]
    exact ⟨gen_of_retract rt hX.1, cogen_of_retract rt hX.2⟩

theorem isImageClosed_addOf_iff (S : Set ι) :
    (σ.addOf S).IsImageClosed ↔ σ.iClosure.IsClosed S := by
  rw [isImageClosed_iff_isClosed_indOf, indOf_addOf]

omit [IsArtinianRing R] in
theorem indOf_subset_iff {Z Z' : Statement.Subcategory (FGModuleCat.{w} R)} :
    σ.indOf Z ⊆ σ.indOf Z' ↔ Z ≤ Z' := by
  constructor
  · intro h X hX
    rw [σ.prop_iff_inAdd_indOf] at hX ⊢
    exact inAdd_mono σ h hX
  · intro h i hi
    exact h _ hi

/-- Theorem 4.11: `C ↦ ind C` identifies the image-closed subcategories with the `icl`-closed
sets of representatives. -/
def imageClosedOrderIso :
    {Z : Statement.Subcategory (FGModuleCat.{w} R) // Z.IsImageClosed} ≃o σ.iClosure.Closeds where
  toFun Z := ⟨σ.indOf Z.1, (σ.isImageClosed_iff_isClosed_indOf Z.1).1 Z.2⟩
  invFun C := ⟨σ.addOf C.1, (σ.isImageClosed_addOf_iff C.1).2 C.2⟩
  left_inv Z := Subtype.ext (σ.addOf_indOf Z.1)
  right_inv C := Subtype.ext (σ.indOf_addOf C.1)
  map_rel_iff' := σ.indOf_subset_iff

/-! ### Definition 4.12 and Proposition 4.13 -/

/-- Definition 4.12: `X` is splitting projective in `Z` if every epimorphism `N ⟶ X` with
`N ∈ Z` splits. -/
def IsSplittingProjective (Z : Statement.Subcategory (FGModuleCat.{w} R)) (X : FGModuleCat.{w} R) :
    Prop :=
  ∀ {N : FGModuleCat.{w} R} (p : N ⟶ X), Z.prop N → Epi p → IsSplitEpi p

/-- Definition 4.12: `X` is splitting injective in `Z` if every monomorphism `X ⟶ N` with
`N ∈ Z` splits. -/
def IsSplittingInjective (Z : Statement.Subcategory (FGModuleCat.{w} R)) (X : FGModuleCat.{w} R) :
    Prop :=
  ∀ {N : FGModuleCat.{w} R} (i : X ⟶ N), Z.prop N → Mono i → IsSplitMono i

omit [IsArtinianRing R] in
theorem isRelativeSplitProjective_iff (Z : Statement.Subcategory (FGModuleCat.{w} R)) (x : ι) :
    σ.IsRelativeSplitProjective (σ.indOf Z) x ↔ IsSplittingProjective Z (σ.obj x) := by
  constructor
  · intro h N p hN hp
    have hN' := (σ.prop_iff_inAdd_indOf Z N).1 hN
    obtain ⟨P⟩ := hN'
    have hs := h {
      index := P.index
      label := P.label
      mem := P.mem
      map := P.iso.inv ≫ p
      epi := epi_comp _ _ }
    obtain ⟨⟨s, hs⟩⟩ := hs
    exact ⟨⟨s ≫ P.iso.inv, by rw [Category.assoc]; exact hs⟩⟩
  · intro h P
    letI : Fintype P.index := FintypeCat.fintype
    exact h P.map (Z.prop_biproduct _ fun t => P.mem t) P.epi

omit [IsArtinianRing R] in
theorem isRelativeSplitInjective_iff (Z : Statement.Subcategory (FGModuleCat.{w} R)) (x : ι) :
    σ.IsRelativeSplitInjective (σ.indOf Z) x ↔ IsSplittingInjective Z (σ.obj x) := by
  constructor
  · intro h N i hN hi
    have hN' := (σ.prop_iff_inAdd_indOf Z N).1 hN
    obtain ⟨P⟩ := hN'
    obtain ⟨s⟩ := h {
      index := P.index
      label := P.label
      mem := P.mem
      map := i ≫ P.iso.hom
      mono := mono_comp _ _ }
    exact ⟨⟨P.iso.hom ≫ s.retraction, by rw [← Category.assoc]; exact s.id⟩⟩
  · intro h P
    letI : Fintype P.index := FintypeCat.fintype
    exact (h P.map (Z.prop_biproduct _ fun t => P.mem t) P.mono).exists_splitMono.some
      |> Nonempty.intro

variable [∀ i : ι, IsArtinianRing (Module.End R (σ.obj i))]

omit [IsArtinianRing R] in
/-- **Proposition 4.13(1).** -/
theorem not_mem_qClosure_sdiff_iff (Z : Statement.Subcategory (FGModuleCat.{w} R)) (x : ι) :
    x ∉ σ.qClosure (σ.indOf Z \ {x}) ↔ IsSplittingProjective Z (σ.obj x) :=
  (σ.not_mem_qClosure_sdiff_iff_isRelativeSplitProjective _ x).trans
    (σ.isRelativeSplitProjective_iff Z x)

omit [IsArtinianRing R] in
/-- **Proposition 4.13(2).** -/
theorem not_mem_sClosure_sdiff_iff (Z : Statement.Subcategory (FGModuleCat.{w} R)) (x : ι) :
    x ∉ σ.sClosure (σ.indOf Z \ {x}) ↔ IsSplittingInjective Z (σ.obj x) :=
  (σ.not_mem_sClosure_diff_iff_relativeSplitInjective _ x).trans
    (σ.isRelativeSplitInjective_iff Z x)

omit [∀ i : ι, IsArtinianRing (Module.End R (σ.obj i))] in
/-- **Proposition 4.13**, (3) ⇔ (4). -/
theorem extremePoints_iff_isImageClosed {Z : Statement.Subcategory (FGModuleCat.{w} R)}
    (hZ : Z.IsImageClosed) {x : ι} (hx : x ∈ σ.indOf Z) :
    x ∈ σ.iClosure.extremePoints (σ.indOf Z) ↔ (σ.addOf (σ.indOf Z \ {x})).IsImageClosed := by
  rw [SetClosure.mem_extremePoints_iff_isClosed_sdiff_singleton
    ((σ.isImageClosed_iff_isClosed_indOf Z).1 hZ) hx, isImageClosed_addOf_iff]

omit [IsArtinianRing R] in
/-- **Proposition 4.13**, (3) ⇔ (5). -/
theorem extremePoints_iff_splitting {Z : Statement.Subcategory (FGModuleCat.{w} R)} {x : ι}
    (hx : x ∈ σ.indOf Z) :
    x ∈ σ.iClosure.extremePoints (σ.indOf Z) ↔
      IsSplittingProjective Z (σ.obj x) ∨ IsSplittingInjective Z (σ.obj x) := by
  rw [SetClosure.mem_extremePoints, and_iff_right hx, iClosure_apply, mem_inter_iff, not_and_or,
    σ.not_mem_qClosure_sdiff_iff, σ.not_mem_sClosure_sdiff_iff]

/-! ### Corollary 4.14 -/

omit [IsArtinianRing R] [∀ i : ι, IsArtinianRing (Module.End R (σ.obj i))] in
/-- Corollary 4.14(1), meets: the intersection of image-closed subcategories is their meet. -/
theorem isGLB_iInf (s : Set {Z : Statement.Subcategory (FGModuleCat.{w} R) // Z.IsImageClosed}) :
    IsGLB s ⟨Statement.Subcategory.iInf (fun Z : s => Z.1.1),
      Statement.Subcategory.IsImageClosed.iInf fun Z => Z.1.2⟩ := by
  refine ⟨fun Z hZ X hX => (Statement.Subcategory.iInf_prop_iff _ X).1 hX ⟨Z, hZ⟩,
    fun W hW X hX => ?_⟩
  exact (Statement.Subcategory.iInf_prop_iff _ X).2 fun Z => hW Z.2 X hX

omit [∀ i : ι, IsArtinianRing (Module.End R (σ.obj i))] in
/-- Corollary 4.14(1), joins: the join of image-closed subcategories is
`icl(add ⋃ Zᵢ)`. -/
theorem isLUB_join (s : Set {Z : Statement.Subcategory (FGModuleCat.{w} R) // Z.IsImageClosed}) :
    IsLUB s ⟨σ.addOf (σ.iClosure (⋃ Z ∈ s, σ.indOf Z.1)),
      (σ.isImageClosed_addOf_iff _).2 (σ.iClosure.isClosed_closure _)⟩ := by
  refine ⟨fun Z hZ X hX => ?_, fun W hW X hX => ?_⟩
  · rw [σ.prop_iff_inAdd_indOf] at hX
    refine inAdd_mono σ ?_ hX
    exact (subset_biUnion_of_mem (u := fun Z : {Z : Statement.Subcategory (FGModuleCat.{w} R) //
      Z.IsImageClosed} => σ.indOf Z.1) hZ).trans (σ.iClosure.le_closure _)
  · have hle : σ.iClosure (⋃ Z ∈ s, σ.indOf Z.1) ⊆ σ.indOf W.1 := by
      apply ((σ.isImageClosed_iff_isClosed_indOf W.1).1 W.2).closure_le_iff.2
      exact iUnion₂_subset fun Z hZ => σ.indOf_subset_iff.2 (hW hZ)
    rw [σ.prop_iff_inAdd_indOf W.1]
    exact inAdd_mono σ hle hX

omit [IsArtinianRing R] in
/-- The splitting projectives and injectives of `Z`: `P_Z ∪ I_Z`. -/
theorem splitting_eq_extremePoints (Z : Statement.Subcategory (FGModuleCat.{w} R)) :
    {x ∈ σ.indOf Z | IsSplittingProjective Z (σ.obj x) ∨ IsSplittingInjective Z (σ.obj x)} =
      σ.iClosure.extremePoints (σ.indOf Z) := by
  ext x
  constructor
  · rintro ⟨hx, h⟩
    exact (σ.extremePoints_iff_splitting hx).2 h
  · intro h
    exact ⟨h.1, (σ.extremePoints_iff_splitting h.1).1 h⟩

/-- **Corollary 4.14(2)**: an image-closed subcategory with finitely many indecomposables is the
image closure of its splitting projectives and injectives. -/
theorem iClosure_splitting_eq {Z : Statement.Subcategory (FGModuleCat.{w} R)}
    (hZ : Z.IsImageClosed) (hfin : (σ.indOf Z).Finite) :
    σ.iClosure
      {x ∈ σ.indOf Z | IsSplittingProjective Z (σ.obj x) ∨ IsSplittingInjective Z (σ.obj x)} =
      σ.indOf Z := by
  have hC := (σ.isImageClosed_iff_isClosed_indOf Z).1 hZ
  have hcompact : IsCompactElement (⟨σ.indOf Z, hC⟩ : σ.iClosure.Closeds) := by
    have := SetClosure.finiteClosure_isCompactElement (σ.iClosure_isFinitary) hfin
    have heq : σ.iClosure.toCloseds (σ.indOf Z) = ⟨σ.indOf Z, hC⟩ := Subtype.ext hC.closure_eq
    rwa [heq] at this
  have h := SetClosure.compact_extremePoints_basis σ.iClosure_isFinitary
    (σ.iClosure_isAntiExchange (σ.qClosure_isAntiExchange) (σ.sClosure_isAntiExchange)) hcompact
  rw [splitting_eq_extremePoints]
  exact h.2.1

omit [IsArtinianRing R] in
/-- **Corollary 4.14(2)**: every generating set of `ind Z` contains the splitting projectives and
injectives of `Z`. -/
theorem splitting_subset {Z : Statement.Subcategory (FGModuleCat.{w} R)} {S : Set ι}
    (hS : σ.iClosure S = σ.indOf Z) :
    {x ∈ σ.indOf Z | IsSplittingProjective Z (σ.obj x) ∨ IsSplittingInjective Z (σ.obj x)} ⊆ S := by
  rw [splitting_eq_extremePoints]
  exact SetClosure.extremePoints_subset_of_closure_eq hS

/-- **Corollary 4.14(3)**: if `Z'` is covered by `Z` among image-closed subcategories, exactly one
indecomposable lies in `Z` but not in `Z'`. -/
theorem exists_sdiff_eq_singleton_of_covby
    {Z Z' : {Z : Statement.Subcategory (FGModuleCat.{w} R) // Z.IsImageClosed}}
    (h : Z' ⋖ Z) : ∃ x, σ.indOf Z.1 \ σ.indOf Z'.1 = {x} := by
  have hlt : σ.indOf Z'.1 ⊂ σ.indOf Z.1 := by
    have := (σ.imageClosedOrderIso).lt_iff_lt.2 h.lt
    exact this
  obtain ⟨x, hxZ, hxZ'⟩ := exists_of_ssubset hlt
  have hC : σ.iClosure.IsClosed (σ.indOf Z'.1) :=
    (σ.isImageClosed_iff_isClosed_indOf Z'.1).1 Z'.2
  have hD : σ.iClosure.IsClosed (σ.indOf Z.1) :=
    (σ.isImageClosed_iff_isClosed_indOf Z.1).1 Z.2
  -- adjoining any new representative recovers `Z`
  have hfill : ∀ y ∈ σ.indOf Z.1 \ σ.indOf Z'.1,
      σ.iClosure (insert y (σ.indOf Z'.1)) = σ.indOf Z.1 := by
    rintro y ⟨hyZ, hyZ'⟩
    let W : {Z : Statement.Subcategory (FGModuleCat.{w} R) // Z.IsImageClosed} :=
      (σ.imageClosedOrderIso).symm ⟨σ.iClosure (insert y (σ.indOf Z'.1)), σ.iClosure.isClosed_closure _⟩
    have hW : σ.indOf W.1 = σ.iClosure (insert y (σ.indOf Z'.1)) := σ.indOf_addOf _
    have hle : W ≤ Z := by
      rw [← (σ.imageClosedOrderIso).le_iff_le]
      show σ.indOf W.1 ⊆ σ.indOf Z.1
      rw [hW]
      exact hD.closure_le_iff.2 (insert_subset hyZ hlt.subset)
    have hge : Z' < W := by
      rw [← (σ.imageClosedOrderIso).lt_iff_lt]
      show σ.indOf Z'.1 ⊂ σ.indOf W.1
      rw [hW]
      refine ssubset_of_subset_of_ne ((subset_insert _ _).trans (σ.iClosure.le_closure _)) ?_
      intro heq
      apply hyZ'
      rw [heq]
      exact σ.iClosure.le_closure _ (mem_insert _ _)
    have hWZ : W = Z := by
      by_contra hne
      exact h.2 hge (lt_of_le_of_ne hle hne)
    rw [← hW, hWZ]
  refine ⟨x, ?_⟩
  apply Subset.antisymm
  · intro y hy
    by_contra hyx
    have hae := σ.iClosure_isAntiExchange (σ.qClosure_isAntiExchange) (σ.sClosure_isAntiExchange)
    refine hae hC hy.2 hxZ' (fun hyx' => hyx (mem_singleton_iff.2 hyx')) ?_ ?_
    · rw [hfill x ⟨hxZ, hxZ'⟩]
      exact hy.1
    · rw [hfill y hy]
      exact hxZ
  · rintro y rfl
    exact ⟨hxZ, hxZ'⟩

/-- **Corollary 4.14(3)**: along a cover, the number of indecomposables grows by one; so for a
representation-finite algebra the lattice of image-closed subcategories is graded by size. -/
theorem ncard_of_covby
    {Z Z' : {Z : Statement.Subcategory (FGModuleCat.{w} R) // Z.IsImageClosed}}
    (h : Z' ⋖ Z) (hfin : (σ.indOf Z.1).Finite) :
    (σ.indOf Z.1).ncard = (σ.indOf Z'.1).ncard + 1 := by
  obtain ⟨x, hx⟩ := σ.exists_sdiff_eq_singleton_of_covby h
  have hsub : σ.indOf Z'.1 ⊆ σ.indOf Z.1 := σ.indOf_subset_iff.2 h.le
  have hxZ' : x ∉ σ.indOf Z'.1 := by
    have : x ∈ σ.indOf Z.1 \ σ.indOf Z'.1 := by rw [hx]; exact mem_singleton x
    exact this.2
  have heq : σ.indOf Z.1 = insert x (σ.indOf Z'.1) := by
    rw [← union_sdiff_cancel hsub, hx, union_singleton]
  rw [heq, ncard_insert_of_notMem hxZ' (hfin.subset hsub)]

end PretorsionImageClosed.IndecomposableSkeleton
