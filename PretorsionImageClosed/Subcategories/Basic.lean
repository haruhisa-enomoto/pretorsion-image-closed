module

public import PretorsionImageClosed.Statement
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Images

/-!
# Subcategories, closure conditions and trivial morphisms

Basic API for the notions fixed in `Statement.lean`: subcategories (object
properties closed under retracts, binary direct sums and zero objects),
quotient-closed and submodule-closed (here: subobject-closed) subcategories
(Definition 2.1), image-closed subcategories in an abelian category, the
observation (2.1) that `T ∩ F` is image-closed when `T` is quotient-closed and
`F` is subobject-closed, and the elementary behaviour of `Z`-trivial morphisms
(Definition 2.2).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PretorsionImageClosed

open CategoryTheory Limits Statement ZeroObject

/-! ### Trivial morphisms -/

namespace Statement

section Trivial

variable {C : Type*} [Category C] {Z : ObjectProperty C}

theorem IsTrivial.of_prop_src {X Y : C} (f : X ⟶ Y) (hX : Z X) : IsTrivial Z f :=
  ⟨X, hX, 𝟙 X, f, Category.id_comp f⟩

theorem IsTrivial.of_prop_tgt {X Y : C} (f : X ⟶ Y) (hY : Z Y) : IsTrivial Z f :=
  ⟨Y, hY, f, 𝟙 Y, Category.comp_id f⟩

theorem IsTrivial.comp_left {X Y W : C} {f : X ⟶ Y} (h : IsTrivial Z f) (g : W ⟶ X) :
    IsTrivial Z (g ≫ f) := by
  obtain ⟨V, hV, a, b, rfl⟩ := h
  exact ⟨V, hV, g ≫ a, b, by simp⟩

theorem IsTrivial.comp_right {X Y W : C} {f : X ⟶ Y} (h : IsTrivial Z f) (g : Y ⟶ W) :
    IsTrivial Z (f ≫ g) := by
  obtain ⟨V, hV, a, b, rfl⟩ := h
  exact ⟨V, hV, a, b ≫ g, by simp⟩

theorem IsTrivial.mono {Z' : ObjectProperty C} (hZ : Z ≤ Z') {X Y : C} {f : X ⟶ Y}
    (h : IsTrivial Z f) : IsTrivial Z' f := by
  obtain ⟨V, hV, a, b, rfl⟩ := h
  exact ⟨V, hZ V hV, a, b, rfl⟩

end Trivial

end Statement

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasBinaryBiproducts C]

namespace Statement.Subcategory

variable (Z : Subcategory C)

@[ext]
theorem ext {Z Z' : Subcategory C} (h : Z.prop = Z'.prop) : Z = Z' := by
  cases Z; cases Z'; cases h; rfl

theorem ext_iff' {Z Z' : Subcategory C} : Z = Z' ↔ ∀ X, Z.prop X ↔ Z'.prop X :=
  ⟨fun h X => by rw [h], fun h => ext (funext fun X => propext (h X))⟩

theorem prop_of_iso {X Y : C} (e : X ≅ Y) (hX : Z.prop X) : Z.prop Y :=
  Z.prop_of_retract (Retract.ofIso e.symm) hX

theorem prop_iff_of_iso {X Y : C} (e : X ≅ Y) : Z.prop X ↔ Z.prop Y :=
  ⟨Z.prop_of_iso e, Z.prop_of_iso e.symm⟩

instance : Z.prop.IsClosedUnderIsomorphisms where
  of_iso e hX := Z.prop_of_iso e hX

theorem prop_of_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] (hX : Z.prop X) : Z.prop Y :=
  Z.prop_of_iso (asIso f) hX

theorem prop_of_splitMono {X Y : C} (f : X ⟶ Y) [IsSplitMono f] (hY : Z.prop Y) : Z.prop X :=
  Z.prop_of_retract ⟨f, retraction f, IsSplitMono.id f⟩ hY

theorem prop_of_splitEpi {X Y : C} (f : X ⟶ Y) [IsSplitEpi f] (hX : Z.prop X) : Z.prop Y :=
  Z.prop_of_retract ⟨section_ f, f, IsSplitEpi.id f⟩ hX

theorem prop_biprod_left {X Y : C} (h : Z.prop (X ⊞ Y)) : Z.prop X :=
  Z.prop_of_retract ⟨biprod.inl, biprod.fst, biprod.inl_fst⟩ h

theorem prop_biprod_right {X Y : C} (h : Z.prop (X ⊞ Y)) : Z.prop Y :=
  Z.prop_of_retract ⟨biprod.inr, biprod.snd, biprod.inr_snd⟩ h

theorem prop_biprod_iff {X Y : C} : Z.prop (X ⊞ Y) ↔ Z.prop X ∧ Z.prop Y :=
  ⟨fun h => ⟨Z.prop_biprod_left h, Z.prop_biprod_right h⟩, fun h => Z.prop_biprod h.1 h.2⟩

theorem prop_zero [HasZeroObject C] : Z.prop 0 :=
  Z.prop_of_isZero (isZero_zero C)

/-! ### The order and lattice operations -/

instance : PartialOrder (Subcategory C) where
  le Z Z' := Z.prop ≤ Z'.prop
  le_refl _ := le_rfl
  le_trans _ _ _ h h' := h.trans h'
  le_antisymm _ _ h h' := ext (le_antisymm h h')

theorem le_def {Z Z' : Subcategory C} : Z ≤ Z' ↔ Z.prop ≤ Z'.prop := Iff.rfl

theorem le_iff {Z Z' : Subcategory C} : Z ≤ Z' ↔ ∀ X, Z.prop X → Z'.prop X := Iff.rfl

/-- The whole category. -/
instance : Top (Subcategory C) where
  top := { prop := ⊤
           prop_of_retract := fun _ _ => trivial
           prop_biprod := fun _ _ => trivial
           prop_of_isZero := fun _ => trivial }

@[simp] theorem top_prop : (⊤ : Subcategory C).prop = ⊤ := rfl

theorem le_top (Z : Subcategory C) : Z ≤ ⊤ := fun _ _ => trivial

/-- The zero subcategory, consisting of the zero objects. -/
instance : Bot (Subcategory C) where
  bot := { prop := fun X => IsZero X
           prop_of_retract := fun {X Y} h hY => by
             rw [IsZero.iff_id_eq_zero, ← h.retract, hY.eq_zero_of_tgt h.i, zero_comp]
           prop_biprod := fun {X Y} hX hY => by
             refine ⟨fun Z => ⟨⟨⟨0⟩, fun f => ?_⟩⟩, fun Z => ⟨⟨⟨0⟩, fun f => ?_⟩⟩⟩
             · apply biprod.hom_ext'
               · rw [hX.eq_zero_of_src (biprod.inl ≫ f), hX.eq_zero_of_src (biprod.inl ≫ _)]
               · rw [hY.eq_zero_of_src (biprod.inr ≫ f), hY.eq_zero_of_src (biprod.inr ≫ _)]
             · apply biprod.hom_ext
               · rw [hX.eq_zero_of_tgt (f ≫ biprod.fst), hX.eq_zero_of_tgt (_ ≫ biprod.fst)]
               · rw [hY.eq_zero_of_tgt (f ≫ biprod.snd), hY.eq_zero_of_tgt (_ ≫ biprod.snd)]
           prop_of_isZero := fun h => h }

@[simp] theorem bot_prop : (⊥ : Subcategory C).prop = fun X => IsZero X := rfl

theorem bot_le (Z : Subcategory C) : ⊥ ≤ Z := fun _ h => Z.prop_of_isZero h

/-- The intersection of two subcategories. -/
instance : Min (Subcategory C) where
  min Z Z' :=
    { prop := Z.prop ⊓ Z'.prop
      prop_of_retract := fun h hY => ⟨Z.prop_of_retract h hY.1, Z'.prop_of_retract h hY.2⟩
      prop_biprod := fun hX hY => ⟨Z.prop_biprod hX.1 hY.1, Z'.prop_biprod hX.2 hY.2⟩
      prop_of_isZero := fun h => ⟨Z.prop_of_isZero h, Z'.prop_of_isZero h⟩ }

@[simp] theorem inf_prop (Z Z' : Subcategory C) : (Z ⊓ Z').prop = Z.prop ⊓ Z'.prop := rfl

theorem inf_prop_iff (Z Z' : Subcategory C) (X : C) :
    (Z ⊓ Z').prop X ↔ Z.prop X ∧ Z'.prop X := Iff.rfl

/-- The intersection of a family of subcategories. -/
def iInf {ι : Sort*} (Z : ι → Subcategory C) : Subcategory C where
  prop := ⨅ i, (Z i).prop
  prop_of_retract h hY := by
    simp only [iInf_apply, iInf_Prop_eq] at hY ⊢
    exact fun i => (Z i).prop_of_retract h (hY i)
  prop_biprod hX hY := by
    simp only [iInf_apply, iInf_Prop_eq] at hX hY ⊢
    exact fun i => (Z i).prop_biprod (hX i) (hY i)
  prop_of_isZero h := by
    simp only [iInf_apply, iInf_Prop_eq]
    exact fun i => (Z i).prop_of_isZero h

@[simp] theorem iInf_prop {ι : Sort*} (Z : ι → Subcategory C) :
    (iInf Z).prop = ⨅ i, (Z i).prop := rfl

theorem iInf_prop_iff {ι : Sort*} (Z : ι → Subcategory C) (X : C) :
    (iInf Z).prop X ↔ ∀ i, (Z i).prop X := by
  simp [iInf_prop]

/-! ### Closure conditions -/

/-- `Z` is quotient-closed (Definition 2.1): closed under epimorphic images. -/
def IsQuotientClosed : Prop :=
  ∀ {X Y : C} (f : X ⟶ Y), Epi f → Z.prop X → Z.prop Y

/-- `Z` is submodule-closed (Definition 2.1): closed under subobjects. -/
def IsSubobjectClosed : Prop :=
  ∀ {X Y : C} (f : X ⟶ Y), Mono f → Z.prop Y → Z.prop X

theorem isQuotientClosed_top : (⊤ : Subcategory C).IsQuotientClosed := fun _ _ _ => trivial

theorem isSubobjectClosed_top : (⊤ : Subcategory C).IsSubobjectClosed := fun _ _ _ => trivial

theorem isQuotientClosed_bot : (⊥ : Subcategory C).IsQuotientClosed := by
  intro X Y f hf hX
  change IsZero Y
  rw [IsZero.iff_id_eq_zero, ← cancel_epi f, comp_zero, hX.eq_zero_of_src (f ≫ 𝟙 Y)]

theorem isSubobjectClosed_bot : (⊥ : Subcategory C).IsSubobjectClosed := by
  intro X Y f hf hY
  change IsZero X
  rw [IsZero.iff_id_eq_zero, ← cancel_mono f, zero_comp, hY.eq_zero_of_tgt (𝟙 X ≫ f)]

theorem IsQuotientClosed.inf {Z Z' : Subcategory C} (h : Z.IsQuotientClosed)
    (h' : Z'.IsQuotientClosed) : (Z ⊓ Z').IsQuotientClosed :=
  fun f hf hX => ⟨h f hf hX.1, h' f hf hX.2⟩

theorem IsSubobjectClosed.inf {Z Z' : Subcategory C} (h : Z.IsSubobjectClosed)
    (h' : Z'.IsSubobjectClosed) : (Z ⊓ Z').IsSubobjectClosed :=
  fun f hf hY => ⟨h f hf hY.1, h' f hf hY.2⟩

theorem IsQuotientClosed.iInf {ι : Sort*} {Z : ι → Subcategory C}
    (h : ∀ i, (Z i).IsQuotientClosed) : (Subcategory.iInf Z).IsQuotientClosed := by
  intro X Y f hf hX
  rw [iInf_prop_iff] at hX ⊢
  exact fun i => h i f hf (hX i)

theorem IsSubobjectClosed.iInf {ι : Sort*} {Z : ι → Subcategory C}
    (h : ∀ i, (Z i).IsSubobjectClosed) : (Subcategory.iInf Z).IsSubobjectClosed := by
  intro X Y f hf hY
  rw [iInf_prop_iff] at hY ⊢
  exact fun i => h i f hf (hY i)

end Statement.Subcategory

/-! ### Image-closed subcategories in an abelian category -/

section Abelian

variable {A : Type*} [Category A] [Abelian A]

namespace Statement.Subcategory

variable (Z : Subcategory A)

/-- `Z` is image-closed (Definition 2.1), in the form of `Statement.IsImageClosed`. -/
abbrev IsImageClosed : Prop := Statement.IsImageClosed Z.prop

theorem IsQuotientClosed.isImageClosed {Z : Subcategory A} (h : Z.IsQuotientClosed) :
    Z.IsImageClosed := fun f hX _ =>
  h (factorThruImage f) inferInstance hX

theorem IsSubobjectClosed.isImageClosed {Z : Subcategory A} (h : Z.IsSubobjectClosed) :
    Z.IsImageClosed := fun f _ hY =>
  h (image.ι f) inferInstance hY

/-- Equation (2.1): the intersection of a quotient-closed and a subobject-closed
subcategory is image-closed. -/
theorem IsImageClosed.inf_of_closed {T F : Subcategory A} (hT : T.IsQuotientClosed)
    (hF : F.IsSubobjectClosed) : (T ⊓ F).IsImageClosed := fun f hX hY =>
  ⟨hT.isImageClosed f hX.1 hY.1, hF.isImageClosed f hX.2 hY.2⟩

theorem IsImageClosed.inf {Z Z' : Subcategory A} (h : Z.IsImageClosed) (h' : Z'.IsImageClosed) :
    (Z ⊓ Z').IsImageClosed := fun f hX hY => ⟨h f hX.1 hY.1, h' f hX.2 hY.2⟩

theorem IsImageClosed.iInf {ι : Sort*} {Z : ι → Subcategory A} (h : ∀ i, (Z i).IsImageClosed) :
    (Subcategory.iInf Z).IsImageClosed := by
  intro X Y f hX hY
  rw [iInf_prop_iff] at hX hY ⊢
  exact fun i => h i f (hX i) (hY i)

theorem isImageClosed_top : (⊤ : Subcategory A).IsImageClosed := fun _ _ _ => trivial

theorem isImageClosed_bot : (⊥ : Subcategory A).IsImageClosed :=
  Subcategory.isQuotientClosed_bot.isImageClosed

end Statement.Subcategory

end Abelian

/-! ### Trivial morphisms and zero objects -/

namespace Statement

theorem isTrivial_zero [HasZeroObject C] (Zs : Subcategory C) {X Y : C} :
    IsTrivial Zs.prop (0 : X ⟶ Y) :=
  ⟨0, Zs.prop_zero, 0, 0, by simp⟩

theorem IsTrivial.of_isZero_src {X Y : C} (f : X ⟶ Y) (hX : IsZero X) (Zs : Subcategory C) :
    IsTrivial Zs.prop f :=
  IsTrivial.of_prop_src f (Zs.prop_of_isZero hX)

end Statement

end PretorsionImageClosed
