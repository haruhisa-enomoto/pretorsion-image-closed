module

public import PretorsionImageClosed.LinearQuiver.SummandReduction
public import PretorsionImageClosed.Realizations.TheoremA

/-!
# Image-closed subcategories of the linear quiver (Theorem 5.5)

A subcategory `C` of the representations of `1 → 2 → ⋯ → n` is image-closed iff
its family of support intervals is intersection-closed: whenever `M_{a,b}` and
`M_{c,d}` lie in `C` and `[a, b] ∩ [c, d] ≠ ∅`, the interval
`M_{max a c, min b d}` lies in `C`.

The proof follows the manuscript. For the forward direction the canonical
morphism `M_{c,d} ⟶ M_{a,b}` has image `M_{c,b}` (Proposition 5.2). For the
converse, an interval summand `M_{a,b}` of the image of `f : X ⟶ Y` is a
quotient of `X` and a subobject of `Y`; by Lemma 5.3 and (5.1) it is a quotient
of an interval `M_{a,d}` of `C` with `b ≤ d` and a subobject of an interval
`M_{c,b}` of `C` with `c ≤ a`, so `M_{a,b} = M_{a,d} ∩ M_{c,b}` lies in `C`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PretorsionImageClosed

open CategoryTheory Limits Statement

namespace LinearQuiver

universe u

variable {k : Type u} [Field k] {n : ℕ}

/-- The support intervals of a subcategory are intersection-closed
(Definition 5.4). -/
def IntersectionClosed (C : Subcategory (Statement.LinRep k n)) : Prop :=
  ∀ a b c d : Fin n, a ≤ b → c ≤ d → C.prop (interval k a b) → C.prop (interval k c d) →
    max a c ≤ min b d → C.prop (interval k (max a c) (min b d))

/-- The underlying object of the suffix subobject `M_{c,b}` of `M_{a,b}`. -/
theorem prop_interval_of_prop_suffix (C : Subcategory (Statement.LinRep k n)) {a c b : Fin n}
    (hac : a ≤ c) (h : C.prop (suffix (k := k) a b c hac : Statement.LinRep k n)) :
    C.prop (interval k c b) :=
  C.prop_of_iso (Subobject.underlyingIso _) h

/-- Theorem 5.5, (⇒). -/
theorem intersectionClosed_of_isImageClosed (C : Subcategory (Statement.LinRep k n))
    (hC : C.IsImageClosed) : IntersectionClosed C := by
  intro a b c d hab hcd ha hc hmin
  -- by symmetry, assume `a ≤ c`
  wlog hac : a ≤ c generalizing a b c d
  · have := this c d a b hcd hab hc ha (by rwa [max_comm, min_comm]) (le_of_not_ge hac)
    rwa [max_comm, min_comm] at this
  rw [max_eq_right hac]
  rcases le_total d b with hdb | hbd
  · rw [min_eq_right hdb]
    exact hc
  · rw [min_eq_left hbd]
    -- the image of the canonical morphism `M_{c,d} ⟶ M_{a,b}` is `M_{c,b}`
    have himg := Statement.IsImageClosed.prop_imageSubobject hC (canonicalHom (k := k) hac hbd) hc ha
    rw [imageSubobject_canonicalHom] at himg
    exact prop_interval_of_prop_suffix C hac himg

/-- An interval quotient of an object of `C` is a quotient of an interval of `C`
with the same left endpoint and a larger right endpoint. -/
theorem exists_interval_of_epi (C : Subcategory (Statement.LinRep k n)) {a b : Fin n} (hab : a ≤ b)
    {X : Statement.LinRep k n} (hX : C.prop X) (p : X ⟶ interval k a b) [Epi p] :
    ∃ d : Fin n, b ≤ d ∧ C.prop (interval k a d) := by
  induction intervalSum X with
  | zero hz =>
    exfalso
    exact not_isZero_interval hab (hz.of_epi p)
  | @step X X' c e hce h' e' ih =>
    have hX' : C.prop X' := C.prop_biprod_right (C.prop_of_iso e' hX)
    have hM : C.prop (interval k c e) := C.prop_biprod_left (C.prop_of_iso e' hX)
    -- `e'.inv ≫ p : M_{c,e} ⊞ X' ⟶ M_{a,b}` is an epimorphism, a `biprod.desc`
    have hepi : Epi (biprod.desc (biprod.inl ≫ e'.inv ≫ p) (biprod.inr ≫ e'.inv ≫ p)) := by
      have : biprod.desc (biprod.inl ≫ e'.inv ≫ p) (biprod.inr ≫ e'.inv ≫ p) = e'.inv ≫ p := by
        apply biprod.hom_ext' <;> simp
      rw [this]
      exact epi_comp _ _
    rcases epi_or_epi_of_epi_biprod_desc
        ((biprod.inl : interval k c e ⟶ interval k c e ⊞ X') ≫ e'.inv ≫ p)
        ((biprod.inr : X' ⟶ interval k c e ⊞ X') ≫ e'.inv ≫ p) with hf | hg
    · obtain ⟨rfl, hbe⟩ := eq_and_le_of_epi hab
        ((biprod.inl : interval k c e ⟶ interval k c e ⊞ X') ≫ e'.inv ≫ p)
      exact ⟨e, hbe, hM⟩
    · exact ih hX' ((biprod.inr : X' ⟶ interval k c e ⊞ X') ≫ e'.inv ≫ p)

/-- An interval subobject of an object of `C` is a subobject of an interval of `C`
with the same right endpoint and a smaller left endpoint. -/
theorem exists_interval_of_mono (C : Subcategory (Statement.LinRep k n)) {a b : Fin n} (hab : a ≤ b)
    {Y : Statement.LinRep k n} (hY : C.prop Y) (i : interval k a b ⟶ Y) [Mono i] :
    ∃ c : Fin n, c ≤ a ∧ C.prop (interval k c b) := by
  induction intervalSum Y with
  | zero hz =>
    exfalso
    exact not_isZero_interval hab (IsZero.of_mono i hz)
  | @step Y Y' c e hce h' e' ih =>
    have hY' : C.prop Y' := C.prop_biprod_right (C.prop_of_iso e' hY)
    have hM : C.prop (interval k c e) := C.prop_biprod_left (C.prop_of_iso e' hY)
    have hmono : Mono (biprod.lift (i ≫ e'.hom ≫ biprod.fst) (i ≫ e'.hom ≫ biprod.snd)) := by
      have : biprod.lift (i ≫ e'.hom ≫ biprod.fst) (i ≫ e'.hom ≫ biprod.snd) = i ≫ e'.hom := by
        apply biprod.hom_ext <;> simp
      rw [this]
      exact mono_comp _ _
    rcases mono_or_mono_of_mono_biprod_lift
        (i ≫ e'.hom ≫ (biprod.fst : interval k c e ⊞ Y' ⟶ interval k c e))
        (i ≫ e'.hom ≫ (biprod.snd : interval k c e ⊞ Y' ⟶ Y')) with hf | hg
    · obtain ⟨rfl, hca⟩ := eq_and_le_of_mono hab
        (i ≫ e'.hom ≫ (biprod.fst : interval k c e ⊞ Y' ⟶ interval k c e))
      exact ⟨c, hca, hM⟩
    · exact ih hY' (i ≫ e'.hom ≫ (biprod.snd : interval k c e ⊞ Y' ⟶ Y'))

/-- Theorem 5.5, (⇐). -/
theorem isImageClosed_of_intersectionClosed (C : Subcategory (Statement.LinRep k n))
    (hC : IntersectionClosed C) : C.IsImageClosed := by
  rw [Statement.isImageClosed_iff_forall_imageSubobject]
  intro X Y f hX hY
  -- a summand `Z` of the image which is a quotient of `X` and a subobject of `Y` lies in `C`
  suffices h : ∀ Z : Statement.LinRep k n, IntervalSum Z →
      (∃ p : X ⟶ Z, Epi p) → (∃ i : Z ⟶ Y, Mono i) → C.prop Z from
    h _ (intervalSum _) ⟨factorThruImageSubobject f, inferInstance⟩
      ⟨(imageSubobject f).arrow, inferInstance⟩
  intro Z hZ
  induction hZ with
  | zero hz =>
    intro _ _
    exact C.prop_of_isZero hz
  | @step Z Z' a b hab h' e ih =>
    rintro ⟨p, hp⟩ ⟨i, hi⟩
    refine C.prop_of_iso e.symm (C.prop_biprod ?_ (ih ⟨p ≫ e.hom ≫ biprod.snd, epi_comp _ _⟩
      ⟨biprod.inr ≫ e.inv ≫ i, mono_comp _ _⟩))
    -- the interval summand `M_{a,b}`
    obtain ⟨d, hbd, hd⟩ := exists_interval_of_epi C hab hX (p ≫ e.hom ≫ biprod.fst)
    obtain ⟨c, hca, hc⟩ := exists_interval_of_mono C hab hY (biprod.inl ≫ e.inv ≫ i)
    have := hC a d c b (hab.trans hbd) (hca.trans hab) hd hc (by
      rw [max_eq_left hca, min_eq_right hbd]; exact hab)
    rwa [max_eq_left hca, min_eq_right hbd] at this

/-- **Theorem 5.5.** A subcategory of `mod Λ_n` is image-closed iff its family of
support intervals is intersection-closed. -/
theorem isImageClosed_iff_intersectionClosed (C : Subcategory (Statement.LinRep k n)) :
    C.IsImageClosed ↔ IntersectionClosed C :=
  ⟨intersectionClosed_of_isImageClosed C, isImageClosed_of_intersectionClosed C⟩

end LinearQuiver

end PretorsionImageClosed
