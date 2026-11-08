module

public import PretorsionImageClosed.Subcategories.Basic
public import PretorsionImageClosed.Length.Basic
public import PretorsionImageClosed.Subobjects.Preimage
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Trace and reject

For a subcategory `T` and an object `X` of an abelian category with a length
function, the *trace* `t_T(X)` is the largest subobject of `X` lying in `T`,
and for a subcategory `F` the *reject* `r_F(X)` is the smallest subobject `K`
of `X` with `X/K` in `F` (Definition 2.7 and Proposition 2.10 of the
manuscript). The manuscript defines the trace as the sum of the images of all
morphisms from objects of `T` and the reject as the intersection of the
kernels of all morphisms to objects of `F`; `trace_le_iff` and `le_reject_iff`
show that these descriptions agree with ours when `T` is quotient-closed and
`F` is subobject-closed. The finiteness of Lemma 2.9 enters through the length
function, which provides maximal and minimal subobjects.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PretorsionImageClosed

open CategoryTheory Limits Statement ZeroObject

variable {C : Type*} [Category C] [Abelian C]

/-! ### Sums of subobjects -/

/-- The sum `S + S'` of two subobjects of `X`: the image of `S ⊞ S' ⟶ X`. -/
def sumSubobject {X : C} (S S' : Subobject X) : Subobject X :=
  imageSubobject (biprod.desc S.arrow S'.arrow)

theorem le_sumSubobject_left {X : C} (S S' : Subobject X) : S ≤ sumSubobject S S' :=
  Subobject.le_of_factors (by
    rw [← biprod.inl_desc S.arrow S'.arrow]
    exact imageSubobject_factors_comp_self _ _)

theorem le_sumSubobject_right {X : C} (S S' : Subobject X) : S' ≤ sumSubobject S S' :=
  Subobject.le_of_factors (by
    rw [← biprod.inr_desc S.arrow S'.arrow]
    exact imageSubobject_factors_comp_self _ _)

namespace Statement.Subcategory

variable (T : Subcategory C) (X : C)

/-- The subobjects of `X` lying in `T`. -/
def subobjectsIn : Set (Subobject X) := {S | T.prop (S : C)}

theorem mem_subobjectsIn {S : Subobject X} : S ∈ T.subobjectsIn X ↔ T.prop (S : C) := Iff.rfl

theorem bot_mem_subobjectsIn : ⊥ ∈ T.subobjectsIn X :=
  T.prop_of_iso Subobject.botCoeIsoZero.symm T.prop_zero

theorem top_mem_subobjectsIn_iff : ⊤ ∈ T.subobjectsIn X ↔ T.prop X :=
  T.prop_iff_of_iso (asIso (⊤ : Subobject X).arrow)

theorem prop_sumSubobject (hT : T.IsQuotientClosed) {S S' : Subobject X} (hS : T.prop (S : C))
    (hS' : T.prop (S' : C)) : T.prop (sumSubobject S S' : C) :=
  T.prop_of_iso (imageSubobjectIso _).symm
    (hT (factorThruImage (biprod.desc S.arrow S'.arrow)) inferInstance (T.prop_biprod hS hS'))

/-! ### Quotients lying in a subcategory -/

variable (F : Subcategory C)

/-- The subobjects `K` of `X` with `X/K` in `F`. -/
def quotientsIn : Set (Subobject X) := {K | F.prop (cokernel K.arrow)}

theorem mem_quotientsIn {K : Subobject X} : K ∈ F.quotientsIn X ↔ F.prop (cokernel K.arrow) :=
  Iff.rfl

theorem top_mem_quotientsIn : ⊤ ∈ F.quotientsIn X :=
  F.prop_of_iso (cokernel.ofEpi (⊤ : Subobject X).arrow).symm F.prop_zero

theorem bot_mem_quotientsIn_iff : ⊥ ∈ F.quotientsIn X ↔ F.prop X := by
  change F.prop (cokernel (⊥ : Subobject X).arrow) ↔ F.prop X
  rw [Subobject.bot_arrow]
  exact F.prop_iff_of_iso cokernelZeroIsoTarget

/-- `X/(K ⊓ K')` embeds into `X/K ⊞ X/K'`, so the quotients lying in a
subobject-closed subcategory are closed under intersection. -/
theorem prop_cokernel_inf (hF : F.IsSubobjectClosed) {K K' : Subobject X}
    (hK : F.prop (cokernel K.arrow)) (hK' : F.prop (cokernel K'.arrow)) :
    F.prop (cokernel (K ⊓ K').arrow) := by
  let φ : X ⟶ cokernel K.arrow ⊞ cokernel K'.arrow :=
    biprod.lift (cokernel.π K.arrow) (cokernel.π K'.arrow)
  have hzero : (K ⊓ K').arrow ≫ φ = 0 := by
    apply biprod.hom_ext
    · rw [Category.assoc, biprod.lift_fst, zero_comp,
        ← Subobject.factorThru_arrow _ _ (Subobject.inf_arrow_factors_left K K'),
        Category.assoc, cokernel.condition, comp_zero]
    · rw [Category.assoc, biprod.lift_snd, zero_comp,
        ← Subobject.factorThru_arrow _ _ (Subobject.inf_arrow_factors_right K K'),
        Category.assoc, cokernel.condition, comp_zero]
  have hker : ∀ (L : Subobject X), kernelSubobject (cokernel.π L.arrow) = L := fun L => by
    rw [← (ShortComplex.exact_iff_image_eq_kernel _).1 (ShortComplex.exact_cokernel L.arrow)]
    change imageSubobject L.arrow = L
    rw [imageSubobject_mono, Subobject.mk_arrow]
  have hexact : (ShortComplex.mk (K ⊓ K').arrow φ hzero).Exact := by
    rw [ShortComplex.exact_iff_image_eq_kernel]
    change imageSubobject (K ⊓ K').arrow = kernelSubobject φ
    rw [imageSubobject_mono, Subobject.mk_arrow]
    apply le_antisymm
    · exact le_kernelSubobject _ _ hzero
    · apply le_inf
      · exact (le_kernelSubobject _ _ (by
          rw [← biprod.lift_fst (cokernel.π K.arrow) (cokernel.π K'.arrow), ← Category.assoc,
            kernelSubobject_arrow_comp, zero_comp])).trans_eq (hker K)
      · exact (le_kernelSubobject _ _ (by
          rw [← biprod.lift_snd (cokernel.π K.arrow) (cokernel.π K'.arrow), ← Category.assoc,
            kernelSubobject_arrow_comp, zero_comp])).trans_eq (hker K')
  have hmono := hexact.mono_cokernelDesc
  exact hF _ hmono (F.prop_biprod hK hK')

variable {F X} in
/-- The quotient `X/ker g` embeds into `Y`, so it lies in `F` whenever `Y` does. -/
theorem prop_cokernel_kernelSubobject (hF : F.IsSubobjectClosed) {Y : C} (g : X ⟶ Y)
    (hY : F.prop Y) : F.prop (cokernel (kernelSubobject g).arrow) := by
  have hexact : (ShortComplex.mk (kernelSubobject g).arrow g (kernelSubobject_arrow_comp g)).Exact := by
    rw [ShortComplex.exact_iff_image_eq_kernel]
    change imageSubobject (kernelSubobject g).arrow = kernelSubobject g
    rw [imageSubobject_mono, Subobject.mk_arrow]
  exact hF _ hexact.mono_cokernelDesc hY

/-! ### The trace -/

variable [HasLength C]


/-- The trace `t_T(X)`: a maximal subobject of `X` lying in `T`. When `T` is
quotient-closed it is the largest one (`le_trace`), and it is the sum of the
images of all morphisms from objects of `T` to `X` (`trace_le_iff`). -/
def trace : Subobject X :=
  Classical.choose
    (Subobject.exists_maximal_of_nonempty (T.subobjectsIn X) ⟨⊥, T.bot_mem_subobjectsIn X⟩)

theorem trace_spec :
    T.trace X ∈ T.subobjectsIn X ∧
      ∀ S ∈ T.subobjectsIn X, T.trace X ≤ S → T.trace X = S :=
  Classical.choose_spec
    (Subobject.exists_maximal_of_nonempty (T.subobjectsIn X) ⟨⊥, T.bot_mem_subobjectsIn X⟩)

theorem prop_trace : T.prop (T.trace X : C) := (T.trace_spec X).1

theorem trace_maximal {S : Subobject X} (hS : T.prop (S : C)) (h : T.trace X ≤ S) :
    T.trace X = S :=
  (T.trace_spec X).2 S hS h

variable {T X}

/-- Proposition 2.10(1): for quotient-closed `T`, the trace is the largest
subobject of `X` lying in `T`. -/
theorem le_trace (hT : T.IsQuotientClosed) {S : Subobject X} (hS : T.prop (S : C)) :
    S ≤ T.trace X := by
  have hmem : T.prop (sumSubobject (T.trace X) S : C) :=
    T.prop_sumSubobject X hT (T.prop_trace X) hS
  rw [T.trace_maximal X hmem (le_sumSubobject_left _ _)]
  exact le_sumSubobject_right _ _

/-- Proposition 2.10(3): `X ∈ T` iff `t_T(X) = X`. -/
theorem trace_eq_top_iff (hT : T.IsQuotientClosed) : T.trace X = ⊤ ↔ T.prop X :=
  ⟨fun h => (T.top_mem_subobjectsIn_iff X).1 (h ▸ T.prop_trace X),
   fun h => top_le_iff.1 (le_trace hT ((T.top_mem_subobjectsIn_iff X).2 h))⟩

/-- Every morphism from an object of `T` to `X` factors through the trace. -/
theorem trace_factors (hT : T.IsQuotientClosed) {Y : C} (f : Y ⟶ X) (hY : T.prop Y) :
    (T.trace X).Factors f := by
  have himg : T.prop (imageSubobject f : C) :=
    T.prop_of_iso (imageSubobjectIso f).symm (hT (factorThruImage f) inferInstance hY)
  exact Subobject.factors_of_le f (le_trace hT himg)
    ((Subobject.factors_iff _ _).2 ⟨factorThruImageSubobject f, imageSubobject_arrow_comp f⟩)

/-- Definition 2.7: the trace is the sum of the images of all morphisms from
objects of `T`, in the form: a subobject contains the trace iff every morphism
from an object of `T` factors through it. -/
theorem trace_le_iff (hT : T.IsQuotientClosed) {S : Subobject X} :
    T.trace X ≤ S ↔ ∀ {Y : C} (f : Y ⟶ X), T.prop Y → S.Factors f :=
  ⟨fun h _ f hY => Subobject.factors_of_le f h (trace_factors hT f hY),
   fun h => Subobject.le_of_factors (h _ (T.prop_trace X))⟩

/-- Proposition 2.10(5): the trace is monotone, in the form that the trace of a
subobject maps into the trace. -/
theorem trace_factors_comp_mono (hT : T.IsQuotientClosed) {W : C} (f : W ⟶ X) [Mono f] :
    (T.trace X).Factors ((T.trace W).arrow ≫ f) :=
  trace_factors hT _ (T.prop_trace W)

/-- The morphism `t(W) → t(X)` induced by `f : W → X` (functoriality of the
trace), for quotient-closed `T`. -/
def traceMap (hT : T.IsQuotientClosed) {W X : C} (f : W ⟶ X) :
    (T.trace W : C) ⟶ (T.trace X : C) :=
  (T.trace X).factorThru ((T.trace W).arrow ≫ f) (trace_factors hT _ (T.prop_trace W))

@[reassoc (attr := simp)]
theorem traceMap_arrow (hT : T.IsQuotientClosed) {W X : C} (f : W ⟶ X) :
    traceMap hT f ≫ (T.trace X).arrow = (T.trace W).arrow ≫ f :=
  Subobject.factorThru_arrow _ _ _

theorem traceMap_id (hT : T.IsQuotientClosed) (X : C) : traceMap hT (𝟙 X) = 𝟙 _ := by
  rw [← cancel_mono (T.trace X).arrow, traceMap_arrow, Category.comp_id, Category.id_comp]

theorem traceMap_comp (hT : T.IsQuotientClosed) {W X Y : C} (f : W ⟶ X) (g : X ⟶ Y) :
    traceMap hT (f ≫ g) = traceMap hT f ≫ traceMap hT g := by
  rw [← cancel_mono (T.trace Y).arrow, traceMap_arrow, Category.assoc, traceMap_arrow,
    traceMap_arrow_assoc]

/-- The trace of a retract is a retract of the trace. -/
def traceRetract (hT : T.IsQuotientClosed) {W X : C} (h : Retract W X) :
    Retract (T.trace W : C) (T.trace X : C) where
  i := traceMap hT h.i
  r := traceMap hT h.r
  retract := by rw [← traceMap_comp, h.retract, traceMap_id]

/-- Proposition 2.10(4): the trace of a direct sum is the direct sum of the
traces, as subobjects. -/
theorem trace_biprod (hT : T.IsQuotientClosed) (Y₁ Y₂ : C) :
    T.trace (Y₁ ⊞ Y₂) = Subobject.mk (biprod.map (T.trace Y₁).arrow (T.trace Y₂).arrow) := by
  apply le_antisymm
  · have h1 := trace_factors hT ((T.trace (Y₁ ⊞ Y₂)).arrow ≫ biprod.fst) (T.prop_trace _)
    have h2 := trace_factors hT ((T.trace (Y₁ ⊞ Y₂)).arrow ≫ biprod.snd) (T.prop_trace _)
    refine Subobject.le_mk_of_comm
      (biprod.lift ((T.trace Y₁).factorThru _ h1) ((T.trace Y₂).factorThru _ h2)) ?_
    apply biprod.hom_ext
    · rw [Category.assoc, biprod.map_fst, biprod.lift_fst_assoc, Subobject.factorThru_arrow]
    · rw [Category.assoc, biprod.map_snd, biprod.lift_snd_assoc, Subobject.factorThru_arrow]
  · exact le_trace hT (T.prop_of_iso (Subobject.underlyingIso _).symm
      (T.prop_biprod (T.prop_trace Y₁) (T.prop_trace Y₂)))

/-- Proposition 2.10(4): `t(Y₁ ⊞ Y₂) ≅ t(Y₁) ⊞ t(Y₂)`. -/
def traceBiprodIso (hT : T.IsQuotientClosed) (Y₁ Y₂ : C) :
    (T.trace (Y₁ ⊞ Y₂) : C) ≅ (T.trace Y₁ : C) ⊞ (T.trace Y₂ : C) :=
  (Subobject.isoOfEq _ _ (trace_biprod hT Y₁ Y₂)).trans (Subobject.underlyingIso _)

/-! ### The reject -/

variable (X)

/-- The reject `r_F(X)`: a minimal subobject `K` of `X` with `X/K` in `F`. When
`F` is subobject-closed it is the smallest one (`reject_le`), and it is the
intersection of the kernels of all morphisms from `X` to objects of `F`
(`le_reject_iff`). -/
def reject : Subobject X :=
  Classical.choose
    (Subobject.exists_minimal_of_nonempty (F.quotientsIn X) ⟨⊤, F.top_mem_quotientsIn X⟩)

theorem reject_spec :
    F.reject X ∈ F.quotientsIn X ∧
      ∀ K ∈ F.quotientsIn X, K ≤ F.reject X → K = F.reject X :=
  Classical.choose_spec
    (Subobject.exists_minimal_of_nonempty (F.quotientsIn X) ⟨⊤, F.top_mem_quotientsIn X⟩)

theorem prop_cokernel_reject : F.prop (cokernel (F.reject X).arrow) := (F.reject_spec X).1

theorem reject_minimal {K : Subobject X} (hK : F.prop (cokernel K.arrow)) (h : K ≤ F.reject X) :
    K = F.reject X :=
  (F.reject_spec X).2 K hK h

variable {F X}

/-- Proposition 2.10(2): for subobject-closed `F`, the reject is the smallest
subobject `K` with `X/K` in `F`. -/
theorem reject_le (hF : F.IsSubobjectClosed) {K : Subobject X} (hK : F.prop (cokernel K.arrow)) :
    F.reject X ≤ K := by
  have hmem := F.prop_cokernel_inf X hF hK (F.prop_cokernel_reject X)
  rw [← F.reject_minimal X hmem inf_le_right]
  exact inf_le_left

/-- Proposition 2.10(3): `X ∈ F` iff `r_F(X) = 0`. -/
theorem reject_eq_bot_iff (hF : F.IsSubobjectClosed) : F.reject X = ⊥ ↔ F.prop X :=
  ⟨fun h => (F.bot_mem_quotientsIn_iff X).1 (h ▸ F.prop_cokernel_reject X),
   fun h => le_bot_iff.1 (reject_le hF ((F.bot_mem_quotientsIn_iff X).2 h))⟩

/-- The reject is contained in the kernel of every morphism to an object of `F`. -/
theorem reject_le_kernelSubobject (hF : F.IsSubobjectClosed) {Y : C} (g : X ⟶ Y) (hY : F.prop Y) :
    F.reject X ≤ kernelSubobject g :=
  reject_le hF (prop_cokernel_kernelSubobject hF g hY)

theorem reject_arrow_comp_eq_zero (hF : F.IsSubobjectClosed) {Y : C} (g : X ⟶ Y) (hY : F.prop Y) :
    (F.reject X).arrow ≫ g = 0 := by
  rw [← Subobject.ofLE_arrow (reject_le_kernelSubobject hF g hY), Category.assoc,
    kernelSubobject_arrow_comp, comp_zero]

/-- Definition 2.7: the reject is the intersection of the kernels of all
morphisms to objects of `F`, in the form: a subobject is contained in the
reject iff it is killed by every morphism to an object of `F`. -/
theorem le_reject_iff (hF : F.IsSubobjectClosed) {K : Subobject X} :
    K ≤ F.reject X ↔ ∀ {Y : C} (g : X ⟶ Y), F.prop Y → K.arrow ≫ g = 0 := by
  constructor
  · intro h Y g hY
    rw [← Subobject.ofLE_arrow h, Category.assoc, reject_arrow_comp_eq_zero hF g hY, comp_zero]
  · intro h
    have := h (cokernel.π (F.reject X).arrow) (F.prop_cokernel_reject X)
    have hle : K ≤ kernelSubobject (cokernel.π (F.reject X).arrow) := le_kernelSubobject _ _ this
    rwa [← (ShortComplex.exact_iff_image_eq_kernel _).1 (ShortComplex.exact_cokernel (F.reject X).arrow),
      imageSubobject_mono, Subobject.mk_arrow] at hle

end Statement.Subcategory

end PretorsionImageClosed

/-! ### Transport along isomorphisms -/

namespace PretorsionImageClosed.Statement.Subcategory

open CategoryTheory Limits

variable {C : Type*} [Category C] [Abelian C] [HasLength C] {T F : Subcategory C}

/-- The trace of an isomorphic object is the transported trace. -/
theorem trace_iso (hT : T.IsQuotientClosed) {X Y : C} (e : X ≅ Y) :
    T.trace Y = Subobject.mk ((T.trace X).arrow ≫ e.hom) := by
  apply le_antisymm
  · have hS : T.prop (Subobject.mk ((T.trace Y).arrow ≫ e.inv) : C) :=
      T.prop_of_iso (Subobject.underlyingIso _).symm (T.prop_trace Y)
    have hle := le_trace hT hS
    refine Subobject.le_mk_of_comm
      ((Subobject.underlyingIso ((T.trace Y).arrow ≫ e.inv)).inv ≫ Subobject.ofLE _ _ hle) ?_
    rw [Category.assoc, ← Category.assoc (Subobject.ofLE _ _ hle), Subobject.ofLE_arrow,
      ← Category.assoc, Subobject.underlyingIso_arrow, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  · exact le_trace hT (T.prop_of_iso (Subobject.underlyingIso _).symm (T.prop_trace X))

/-- The reject of an isomorphic object is the transported reject. -/
theorem reject_iso (hF : F.IsSubobjectClosed) {X Y : C} (e : X ≅ Y) :
    F.reject Y = Subobject.mk ((F.reject X).arrow ≫ e.hom) := by
  apply le_antisymm
  · apply reject_le hF
    refine F.prop_of_iso ?_ (F.prop_cokernel_reject X)
    exact (cokernelCompIsIso (F.reject X).arrow e.hom).symm ≪≫
      cokernelIsoOfEq (Subobject.underlyingIso_arrow _).symm ≪≫ cokernelEpiComp _ _
  · rw [le_reject_iff hF]
    intro W g hW
    rw [← cancel_epi (Subobject.underlyingIso ((F.reject X).arrow ≫ e.hom)).inv, comp_zero,
      ← Category.assoc, Subobject.underlyingIso_arrow, Category.assoc,
      reject_arrow_comp_eq_zero hF (e.hom ≫ g) hW]

/-! ### Proposition 2.10(4), second half, and Proposition 2.10(5) -/

/-- Proposition 2.10(4): the reject of a direct sum is the direct sum of the rejects. -/
theorem reject_biprod (hF : F.IsSubobjectClosed) (Y₁ Y₂ : C) :
    F.reject (Y₁ ⊞ Y₂) = Subobject.mk (biprod.map (F.reject Y₁).arrow (F.reject Y₂).arrow) := by
  apply le_antisymm
  · have hG : F.prop (cokernel (F.reject Y₁).arrow ⊞ cokernel (F.reject Y₂).arrow) :=
      F.prop_biprod (F.prop_cokernel_reject Y₁) (F.prop_cokernel_reject Y₂)
    refine (reject_le_kernelSubobject hF
      (biprod.map (cokernel.π (F.reject Y₁).arrow) (cokernel.π (F.reject Y₂).arrow)) hG).trans ?_
    have hk := kernelSubobject_arrow_comp
      (biprod.map (cokernel.π (F.reject Y₁).arrow) (cokernel.π (F.reject Y₂).arrow))
    have h₁ : (F.reject Y₁).Factors ((kernelSubobject
        (biprod.map (cokernel.π (F.reject Y₁).arrow) (cokernel.π (F.reject Y₂).arrow))).arrow ≫
          biprod.fst) := by
      apply Subobject.factors_of_comp_cokernel_π_eq_zero
      rw [Category.assoc, ← biprod.map_fst, ← Category.assoc, hk, zero_comp]
    have h₂ : (F.reject Y₂).Factors ((kernelSubobject
        (biprod.map (cokernel.π (F.reject Y₁).arrow) (cokernel.π (F.reject Y₂).arrow))).arrow ≫
          biprod.snd) := by
      apply Subobject.factors_of_comp_cokernel_π_eq_zero
      rw [Category.assoc, ← biprod.map_snd, ← Category.assoc, hk, zero_comp]
    refine Subobject.le_mk_of_comm (biprod.lift ((F.reject Y₁).factorThru _ h₁)
      ((F.reject Y₂).factorThru _ h₂)) ?_
    apply biprod.hom_ext <;> simp
  · rw [le_reject_iff hF]
    intro Y g hY
    rw [← Subobject.underlyingIso_hom_comp_eq_mk, Category.assoc]
    have : biprod.map (F.reject Y₁).arrow (F.reject Y₂).arrow ≫ g = 0 := by
      apply biprod.hom_ext'
      · rw [biprod.inl_map_assoc, reject_arrow_comp_eq_zero hF _ hY, comp_zero]
      · rw [biprod.inr_map_assoc, reject_arrow_comp_eq_zero hF _ hY, comp_zero]
    rw [this, comp_zero]

/-- Proposition 2.10(5): for a subobject `W ⊆ X`, `t(W) ⊆ t(X)`. -/
theorem push_trace_le (hT : T.IsQuotientClosed) {X : C} (W : Subobject X) :
    Subobject.push W (T.trace (W : C)) ≤ T.trace X :=
  le_trace hT (T.prop_of_iso (Subobject.underlyingIso _).symm (T.prop_trace _))

/-- Proposition 2.10(5): for a subobject `W ⊆ X`, `r(W) ⊆ r(X)`. -/
theorem push_reject_le (hF : F.IsSubobjectClosed) {X : C} (W : Subobject X) :
    Subobject.push W (F.reject (W : C)) ≤ F.reject X := by
  rw [le_reject_iff hF]
  intro Y g hY
  rw [Subobject.push_arrow, Category.assoc, Category.assoc,
    reject_arrow_comp_eq_zero hF (W.arrow ≫ g) hY, comp_zero]

end PretorsionImageClosed.Statement.Subcategory
