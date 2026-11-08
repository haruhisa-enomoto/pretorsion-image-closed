module

public import PretorsionImageClosed.LinearQuiver.Indecomposables
public import PretorsionImageClosed.Subcategories.Trace

/-!
# Subobjects of interval representations

Equation (5.1) and Lemma 5.3 of the manuscript.

* The nonzero subobjects of `M_{a,d}` are the suffixes `M_{ℓ,d}`, `a ≤ ℓ ≤ d`,
  embedded by `intervalIncl` (`suffix`); every subobject is `⊥` or a suffix
  (`eq_bot_or_eq_suffix`), and suffixes are totally ordered.
* Lemma 5.3: if an interval is a quotient of a direct sum `Y₁ ⊞ Y₂`, it is a
  quotient of `Y₁` or of `Y₂` (`epi_or_epi_of_epi_biprod_desc`), and dually for
  subobjects (`mono_or_mono_of_mono_biprod_lift`).

The key input is that there is no monomorphism `M_{c,d} ⊞ M_{c',d} ⟶ M_{a,d}`:
a nonzero vector in the kernel is exhibited at the vertex `d`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PretorsionImageClosed

open CategoryTheory Limits Statement

namespace LinearQuiver

universe u

variable {k : Type u} [Field k] {n : ℕ}

/-! ### Scalar endomorphisms -/

/-- Multiplication by the scalar `r` on an interval representation. -/
def scalarHom (a d : Fin n) (r : k) : interval k a d ⟶ interval k a d where
  app i := ConcreteCategory.ofHom (r • (LinearMap.id : intervalSpace k a d i →ₗ[k] intervalSpace k a d i))
  naturality {i j} f := by
    apply FGModuleCat.hom_ext
    refine LinearMap.ext fun (x : intervalSpace k a d i) => ?_
    change r • inclusionOrZero k _ _ x = inclusionOrZero k _ _ (r • x)
    rw [map_smul]

theorem coord_scalarHom (a d : Fin n) (r : k) (i : Fin n) :
    coord (scalarHom a d r) i = r * coord (𝟙 (interval k a d)) i := by
  rw [coord_id]
  unfold coord
  change ((r • unit k a d i : intervalSpace k a d i) : k) = _
  rw [Submodule.coe_smul, unit_val, smul_eq_mul]

theorem scalarHom_comp_scalarHom (a d : Fin n) (r s : k) :
    scalarHom a d r ≫ scalarHom a d s = scalarHom a d (r * s) := by
  apply hom_ext_coord
  intro i
  rw [coord_comp, coord_scalarHom, coord_scalarHom, coord_scalarHom, coord_id]
  split_ifs <;> ring

theorem scalarHom_one (a d : Fin n) : scalarHom a d (1 : k) = 𝟙 _ := by
  apply hom_ext_coord
  intro i
  rw [coord_scalarHom, one_mul]

/-- Multiplication by a nonzero scalar is an isomorphism. -/
def scalarIso (a d : Fin n) {r : k} (hr : r ≠ 0) : interval k a d ≅ interval k a d where
  hom := scalarHom a d r
  inv := scalarHom a d r⁻¹
  hom_inv_id := by rw [scalarHom_comp_scalarHom, mul_inv_cancel₀ hr, scalarHom_one]
  inv_hom_id := by rw [scalarHom_comp_scalarHom, inv_mul_cancel₀ hr, scalarHom_one]

/-- Proposition 5.2: a morphism `M_{c,d} ⟶ M_{a,b}` is a scalar times the
canonical morphism. -/
theorem eq_scalarHom_comp_canonicalHom {c d a b : Fin n} (η : interval k c d ⟶ interval k a b)
    (hac : a ≤ c) (hbd : b ≤ d) :
    η = scalarHom c d (coord η c) ≫ canonicalHom hac hbd := by
  apply hom_ext_coord
  intro i
  rw [coord_comp, coord_scalarHom, coord_eq_coord_mul_canonical η hac hbd i, coord_canonicalHom,
    coord_id]
  by_cases hi : c ≤ i ∧ i ≤ b
  · rw [if_pos hi, if_pos ⟨hi.1, hi.2.trans hbd⟩]
    ring
  · rw [if_neg hi, mul_zero, mul_zero]

/-! ### Suffix subobjects -/

theorem coord_intervalIncl {a ℓ d : Fin n} (h : a ≤ ℓ) (i : Fin n) :
    coord (intervalIncl k d h) i = if ℓ ≤ i ∧ i ≤ d then 1 else 0 := by
  unfold coord
  change ((inclusionOrZero k (intervalSpace k ℓ d i) (intervalSpace k a d i) (unit k ℓ d i) :
    intervalSpace k a d i) : k) = _
  rw [coe_inclusionOrZero_left k h, unit_val]

theorem intervalIncl_comp {a ℓ ℓ' d : Fin n} (h : a ≤ ℓ) (h' : ℓ ≤ ℓ') :
    intervalIncl k d h' ≫ intervalIncl k d h = intervalIncl k d (h.trans h') := by
  apply hom_ext_coord
  intro i
  rw [coord_comp, coord_intervalIncl, coord_intervalIncl, coord_intervalIncl]
  by_cases hi : ℓ' ≤ i ∧ i ≤ d
  · rw [if_pos hi, if_pos ⟨h'.trans hi.1, hi.2⟩, one_mul]
  · rw [if_neg hi, zero_mul]

theorem isZero_interval_of_lt {ℓ d : Fin n} (h : d < ℓ) : IsZero (interval k ℓ d) :=
  Functor.isZero _ fun i => isZero_interval_obj_of_not_mem k fun hi => (h.trans_le hi.1).not_ge hi.2

/-- The suffix `M_{ℓ,d}` of `M_{a,d}` as a subobject. -/
def suffix (a d ℓ : Fin n) (h : a ≤ ℓ) : Subobject (interval k a d) :=
  Subobject.mk (intervalIncl k d h)

theorem suffix_eq_bot_of_lt {a d ℓ : Fin n} (h : a ≤ ℓ) (hℓ : d < ℓ) : suffix (k := k) a d ℓ h = ⊥ := by
  rw [suffix, Subobject.mk_eq_bot_iff_zero]
  exact (isZero_interval_of_lt hℓ).eq_zero_of_src _

theorem suffix_self (a d : Fin n) : suffix (k := k) a d a le_rfl = ⊤ := by
  rw [suffix]
  have : intervalIncl k d (le_refl a) = 𝟙 _ := hom_ext_coord fun i => by
    rw [coord_intervalIncl, coord_id]
  have h2 : IsIso (intervalIncl k d (le_refl a)) := by rw [this]; infer_instance
  exact Subobject.mk_eq_top_of_isIso _

theorem suffix_le_suffix {a d ℓ ℓ' : Fin n} (h : a ≤ ℓ) (h' : ℓ ≤ ℓ') :
    suffix (k := k) a d ℓ' (h.trans h') ≤ suffix a d ℓ h :=
  Subobject.mk_le_mk_of_comm (intervalIncl k d h') (intervalIncl_comp h h')

/-- Subobjects of an interval are totally ordered: any two suffixes are comparable. -/
theorem suffix_le_or_le {a d ℓ ℓ' : Fin n} (h : a ≤ ℓ) (h' : a ≤ ℓ') :
    suffix (k := k) a d ℓ h ≤ suffix (k := k) a d ℓ' h' ∨
      suffix (k := k) a d ℓ' h' ≤ suffix (k := k) a d ℓ h := by
  rcases le_total ℓ' ℓ with hle | hle
  · exact Or.inl (suffix_le_suffix h' hle)
  · exact Or.inr (suffix_le_suffix h hle)

theorem scalarHom_zero (a d : Fin n) : scalarHom a d (0 : k) = 0 :=
  hom_ext_coord fun i => by rw [coord_scalarHom, zero_mul, coord_zero (k := k) a d a d i]

/-- A morphism `M_{c,d} ⟶ M_{a,d}` (with `a ≤ c ≤ d`) vanishing at the vertex `d`
is zero. -/
theorem eq_zero_of_coord_last_eq_zero {a c d : Fin n} (hac : a ≤ c) (hcd : c ≤ d)
    (f : interval k c d ⟶ interval k a d) (h : coord f d = 0) : f = 0 := by
  have hc : coord f c = 0 := by
    have := coord_eq_coord_mul_canonical f hac le_rfl d
    rw [coord_canonicalHom, if_pos ⟨hcd, le_rfl⟩, mul_one] at this
    rw [← this, h]
  rw [eq_scalarHom_comp_canonicalHom f hac le_rfl, hc, scalarHom_zero, zero_comp]

/-- There is no monomorphism from a direct sum of two intervals ending at `d`
into `M_{a,d}`: the kernel at the vertex `d` is nonzero. -/
theorem not_mono_biprod_desc {a c c' d : Fin n} (hac : a ≤ c) (hac' : a ≤ c') (hcd : c ≤ d)
    (hcd' : c' ≤ d) (f : interval k c d ⟶ interval k a d) (g : interval k c' d ⟶ interval k a d) :
    ¬ Mono (biprod.desc f g) := by
  intro hmono
  have hinj := (FGModuleCat.mono_iff_injective ((biprod.desc f g).app d)).1
    ((NatTrans.mono_iff_mono_app _).1 hmono d)
  -- component identities at the vertex `d`
  have hinl_desc : ∀ y, ((biprod.desc f g).app d).hom.hom
      (((biprod.inl : interval k c d ⟶ interval k c d ⊞ interval k c' d).app d).hom.hom y) =
      (f.app d).hom.hom y := fun y => by
    change ((biprod.inl ≫ biprod.desc f g).app d).hom.hom y = _
    rw [biprod.inl_desc]
  have hinr_desc : ∀ y, ((biprod.desc f g).app d).hom.hom
      (((biprod.inr : interval k c' d ⟶ interval k c d ⊞ interval k c' d).app d).hom.hom y) =
      (g.app d).hom.hom y := fun y => by
    change ((biprod.inr ≫ biprod.desc f g).app d).hom.hom y = _
    rw [biprod.inr_desc]
  have hinl_fst : ∀ y, ((biprod.fst : interval k c d ⊞ interval k c' d ⟶ interval k c d).app d).hom.hom
      (((biprod.inl : interval k c d ⟶ interval k c d ⊞ interval k c' d).app d).hom.hom y) = y :=
    fun y => by
      change ((biprod.inl ≫ biprod.fst : interval k c d ⟶ interval k c d).app d).hom.hom y = y
      rw [biprod.inl_fst]
      rfl
  have hinr_fst : ∀ y, ((biprod.fst : interval k c d ⊞ interval k c' d ⟶ interval k c d).app d).hom.hom
      (((biprod.inr : interval k c' d ⟶ interval k c d ⊞ interval k c' d).app d).hom.hom y) = 0 :=
    fun y => by
      change ((biprod.inr ≫ biprod.fst : interval k c' d ⟶ interval k c d).app d).hom.hom y = 0
      rw [biprod.inr_fst]
      rfl
  -- the vector `(coord g d) • u - (coord f d) • u'` at the vertex `d` is in the kernel
  set x : (interval k c d ⊞ interval k c' d).obj d :=
    ((biprod.inl : interval k c d ⟶ _).app d).hom.hom ((coord g d) • unit k c d d) -
      ((biprod.inr : interval k c' d ⟶ _).app d).hom.hom ((coord f d) • unit k c' d d) with hx
  have hfx : ((biprod.desc f g).app d).hom.hom x = 0 := by
    rw [hx, map_sub, hinl_desc, hinr_desc, sub_eq_zero]
    apply Subtype.ext
    rw [app_val, app_val, Submodule.coe_smul, Submodule.coe_smul, unit_val_of_mem k ⟨hcd, le_rfl⟩,
      unit_val_of_mem k ⟨hcd', le_rfl⟩, smul_eq_mul, smul_eq_mul, mul_one, mul_one, mul_comm]
  have hx0 : x = 0 := hinj (by rw [hfx, map_zero])
  -- hence `coord g d = 0`
  have hg : coord g d = 0 := by
    have := congrArg (fun y => (((biprod.fst : interval k c d ⊞ interval k c' d ⟶ interval k c d).app d).hom.hom y : intervalSpace k c d d).1) hx0
    simp only [hx, map_sub, hinl_fst, hinr_fst, sub_zero, map_zero] at this
    rw [Submodule.coe_smul, unit_val_of_mem k ⟨hcd, le_rfl⟩, smul_eq_mul, mul_one] at this
    exact this
  -- so `g = 0`; then `f` is a mono `M_{c,d} ⟶ M_{a,d}` restricted from `desc`, fine, but the
  -- same argument with `snd` gives `coord f d = 0` and `f = 0`
  have hinl_snd : ∀ y, ((biprod.snd : interval k c d ⊞ interval k c' d ⟶ interval k c' d).app d).hom.hom
      (((biprod.inl : interval k c d ⟶ interval k c d ⊞ interval k c' d).app d).hom.hom y) = 0 :=
    fun y => by
      change ((biprod.inl ≫ biprod.snd : interval k c d ⟶ interval k c' d).app d).hom.hom y = 0
      rw [biprod.inl_snd]
      rfl
  have hinr_snd : ∀ y, ((biprod.snd : interval k c d ⊞ interval k c' d ⟶ interval k c' d).app d).hom.hom
      (((biprod.inr : interval k c' d ⟶ interval k c d ⊞ interval k c' d).app d).hom.hom y) = y :=
    fun y => by
      change ((biprod.inr ≫ biprod.snd : interval k c' d ⟶ interval k c' d).app d).hom.hom y = y
      rw [biprod.inr_snd]
      rfl
  have hf : coord f d = 0 := by
    have := congrArg (fun y => (((biprod.snd : interval k c d ⊞ interval k c' d ⟶ interval k c' d).app d).hom.hom y : intervalSpace k c' d d).1) hx0
    simp only [hx, map_sub, hinl_snd, hinr_snd, zero_sub, map_zero, Submodule.coe_neg,
      Submodule.coe_zero, neg_eq_zero, Submodule.coe_smul, smul_eq_mul] at this
    rwa [unit_val_of_mem k ⟨hcd', le_rfl⟩, mul_one] at this
  have hf0 : f = 0 := eq_zero_of_coord_last_eq_zero hac hcd f hf
  have hg0 : g = 0 := eq_zero_of_coord_last_eq_zero hac' hcd' g hg
  -- a monomorphism that is zero has zero source
  have hdesc0 : biprod.desc f g = 0 := by
    rw [hf0, hg0]
    apply biprod.hom_ext' <;> simp
  rw [hdesc0] at hmono
  have hz : IsZero (interval k c d ⊞ interval k c' d) := by
    rw [IsZero.iff_id_eq_zero, ← cancel_mono (0 : interval k c d ⊞ interval k c' d ⟶ interval k a d),
      zero_comp, comp_zero]
  exact not_isZero_interval hcd
    (IsZero.of_mono (biprod.inl : interval k c d ⟶ interval k c d ⊞ interval k c' d) hz)

/-! ### Classification of the subobjects of an interval -/

theorem canonicalHom_le_rfl_eq_intervalIncl {a c d : Fin n} (hac : a ≤ c) :
    canonicalHom (k := k) hac (le_refl d) = intervalIncl k d hac :=
  hom_ext_coord fun i => by rw [coord_canonicalHom, coord_intervalIncl]

/-- A monomorphism `M_{c,d} ⟶ M_{a,d}` (with `a ≤ c ≤ d`) defines the suffix
subobject `M_{c,d}`. -/
theorem mk_eq_suffix_of_mono {a c d : Fin n} (hac : a ≤ c) (hcd : c ≤ d)
    (η : interval k c d ⟶ interval k a d) [Mono η] : Subobject.mk η = suffix a d c hac := by
  have hne : coord η c ≠ 0 := by
    intro h0
    have hzero : η = 0 := by
      rw [eq_scalarHom_comp_canonicalHom η hac le_rfl, h0, scalarHom_zero, zero_comp]
    have hm : Mono (0 : interval k c d ⟶ interval k a d) := by
      rw [← hzero]
      infer_instance
    have hz : IsZero (interval k c d) := by
      rw [IsZero.iff_id_eq_zero, ← cancel_mono (0 : interval k c d ⟶ interval k a d), zero_comp,
        comp_zero]
    exact not_isZero_interval hcd hz
  rw [suffix]
  apply Subobject.mk_eq_mk_of_comm _ _ (scalarIso c d hne)
  rw [← canonicalHom_le_rfl_eq_intervalIncl hac]
  exact (eq_scalarHom_comp_canonicalHom η hac le_rfl).symm

/-- Every subobject of `M_{a,d}` is zero or a suffix `M_{ℓ,d}` with `a ≤ ℓ ≤ d` (5.1). -/
theorem eq_bot_or_eq_suffix {a d : Fin n} (K : Subobject (interval k a d)) :
    K = ⊥ ∨ ∃ (ℓ : Fin n) (hal : a ≤ ℓ), ℓ ≤ d ∧ K = suffix a d ℓ hal := by
  rcases intervalSum (K : Statement.LinRep k n) with hz | @⟨_, K', c, e, hce, h', e'⟩
  · left
    rw [← Subobject.mk_arrow K, Subobject.mk_eq_bot_iff_zero]
    exact hz.eq_zero_of_src _
  · right
    -- the first summand embeds into `M_{a,d}`
    set ι : interval k c e ⟶ interval k a d := biprod.inl ≫ e'.inv ≫ K.arrow with hι
    haveI : Mono ι := mono_comp _ _
    obtain ⟨rfl, hac⟩ := eq_and_le_of_mono hce ι
    -- the other summand is zero
    have hK'z : IsZero K' := by
      by_contra hK'nz
      rcases h' with hz' | @⟨_, K'', c', d', hcd', -, e''⟩
      · exact hK'nz hz'
      · set ι' : interval k c' d' ⟶ interval k a e :=
          biprod.inl ≫ e''.inv ≫ biprod.inr ≫ e'.inv ≫ K.arrow with hι'
        haveI : Mono ι' := mono_comp _ _
        obtain ⟨rfl, hac'⟩ := eq_and_le_of_mono hcd' ι'
        -- the two intervals together embed, contradiction
        have hdesc : biprod.desc ι ι' =
            (biprod.map (𝟙 _) (biprod.inl ≫ e''.inv)) ≫ e'.inv ≫ K.arrow := by
          apply biprod.hom_ext' <;> simp [hι, hι']
        have hm : Mono (biprod.desc ι ι') := by
          rw [hdesc]
          haveI : Mono (biprod.inl ≫ e''.inv : interval k c' d' ⟶ K') := mono_comp _ _
          haveI : Mono (biprod.map (𝟙 (interval k c d')) (biprod.inl ≫ e''.inv) :
              interval k c d' ⊞ interval k c' d' ⟶ interval k c d' ⊞ K') := by infer_instance
          exact mono_comp _ _
        exact not_mono_biprod_desc hac hac' hce hcd' ι ι' hm
    -- so `K ≅ M_{c,e}`
    refine ⟨c, hac, hce, ?_⟩
    set e₂ : (K : Statement.LinRep k n) ≅ interval k c e := e' ≪≫ (isoBiprodZero hK'z).symm with he₂
    have hcomm' : e₂.inv ≫ K.arrow = ι := by
      rw [hι, he₂]
      simp [isoBiprodZero]
    have hcomm : e₂.hom ≫ ι = K.arrow := ((Iso.inv_comp_eq _).1 hcomm').symm
    rw [← Subobject.mk_arrow K, ← mk_eq_suffix_of_mono hac hce ι]
    exact Subobject.mk_eq_mk_of_comm _ _ e₂ hcomm

end LinearQuiver

end PretorsionImageClosed
