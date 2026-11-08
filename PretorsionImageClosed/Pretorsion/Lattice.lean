module

public import PretorsionImageClosed.Pretorsion.Partners
public import PretorsionImageClosed.Pretorsion.Duality

/-!
# The lattice of pretorsion theories

Theorem 3.6 of the manuscript: in an abelian category with a length function,
the pretorsion theories form a complete lattice for the order (2.2). The meet
of a family is `(⋂ Tᵢ, ⋂ {F : (⋂ Tᵢ, F) is a pretorsion theory, F ⊇ Fᵢ})`
(3.2), by Propositions 3.2 and 3.5; the join (3.3) follows by duality
(Remark 2.6). The least element is `(0, mod)` and the greatest `(mod, 0)`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PretorsionImageClosed.Statement

open CategoryTheory Limits Subcategory

variable {C : Type*} [Category C] [Abelian C]

/-- The order (2.2) on pretorsion theories. -/
instance : PartialOrder (PretorsionTheory C) where
  le := PretorsionTheory.LE
  le_refl _ := ⟨le_rfl, le_rfl⟩
  le_trans _ _ _ h h' := ⟨h.1.trans h'.1, h'.2.trans h.2⟩
  le_antisymm _ _ h h' := PretorsionTheory.ext (Subcategory.ext (le_antisymm h.1 h'.1))
    (Subcategory.ext (le_antisymm h'.2 h.2))

theorem PretorsionTheory.le_iff {P Q : PretorsionTheory C} : P ≤ Q ↔ P.LE Q := Iff.rfl

variable [HasLength C]

namespace PretorsionTheory

/-- The first component of the meet: `⋂ Tᵢ`. -/
def meetT (S : Set (PretorsionTheory C)) : Subcategory C := Subcategory.iInf (fun P : S => P.1.T)

/-- The second components `F ⊇ Fᵢ` with `(⋂ Tᵢ, F)` a pretorsion theory. -/
def MeetPartners (S : Set (PretorsionTheory C)) : Type _ :=
  {F : Subcategory C // IsPretorsionTheory (meetT S).prop F.prop ∧ ∀ P ∈ S, P.F ≤ F}

/-- The meet (3.2) of a set of pretorsion theories. -/
def meet (S : Set (PretorsionTheory C)) : PretorsionTheory C :=
  ⟨meetT S, Subcategory.iInf (fun F : MeetPartners S => F.1),
    isPretorsionTheory_iInf (IsQuotientClosed.iInf fun P : S => P.1.isPretorsionTheory.isQuotientClosed)
      (fun F => F.2.1)⟩

theorem isGLB_meet (S : Set (PretorsionTheory C)) : IsGLB S (meet S) := by
  refine ⟨fun P hP => ⟨fun X hX => (iInf_prop_iff _ X).1 hX ⟨P, hP⟩, fun X hX => ?_⟩,
    fun Q hQ => ⟨fun X hX => ?_, fun X hX => ?_⟩⟩
  · rw [show (meet S).F = Subcategory.iInf (fun F : MeetPartners S => F.1) from rfl, iInf_prop_iff]
    exact fun F => F.2.2 P hP X hX
  · show (meetT S).prop X
    rw [meetT, iInf_prop_iff]
    exact fun P => (hQ P.2).1 X hX
  · have hQF : IsPretorsionTheory (meetT S).prop Q.F.prop :=
      isPretorsionTheory_iInf_left (T := fun P : S => P.1.T) (F := fun P : S => P.1.F)
        (fun P => P.1.isPretorsionTheory) Q.isPretorsionTheory (fun P => (hQ P.2).1)
        (fun P => (hQ P.2).2)
    exact (iInf_prop_iff _ X).1 hX ⟨Q.F, hQF, fun P hP => (hQ hP).2⟩

instance : InfSet (PretorsionTheory C) := ⟨meet⟩

/-- **Theorem 3.6.** The pretorsion theories form a complete lattice. -/
instance : _root_.CompleteLattice (PretorsionTheory C) := completeLatticeOfInf _ isGLB_meet

/-! ### The join, by duality -/

/-- The join (3.3), computed as the meet in the opposite category. -/
def join (S : Set (PretorsionTheory C)) : PretorsionTheory C := (meet (PretorsionTheory.op '' S)).unop

theorem isLUB_join (S : Set (PretorsionTheory C)) : IsLUB S (join S) := by
  refine ⟨fun P hP => ?_, fun Q hQ => ?_⟩
  · rw [le_iff, ← op_LE_op_iff, join, op_unop]
    exact (isGLB_meet _).1 ⟨P, hP, rfl⟩
  · rw [le_iff, ← op_LE_op_iff, join, op_unop]
    refine (isGLB_meet _).2 ?_
    rintro _ ⟨P, hP, rfl⟩
    exact op_LE_op_iff.2 (hQ hP)

theorem sSup_eq_join (S : Set (PretorsionTheory C)) : sSup S = join S :=
  (isLUB_sSup S).unique (isLUB_join S)

/-! ### The formulas (3.2) and (3.3) -/

theorem sInf_eq (S : Set (PretorsionTheory C)) : sInf S = meet S := rfl

theorem meet_F (S : Set (PretorsionTheory C)) :
    (meet S).F = Subcategory.iInf (fun F : MeetPartners S => F.1) := rfl

theorem join_T (S : Set (PretorsionTheory C)) : (join S).T = (meet (PretorsionTheory.op '' S)).F.unop :=
  rfl

theorem join_F (S : Set (PretorsionTheory C)) : (join S).F = (meetT (PretorsionTheory.op '' S)).unop :=
  rfl

theorem meetT_prop (S : Set (PretorsionTheory C)) : (meetT S).prop = ⨅ P ∈ S, P.T.prop := by
  funext X
  apply propext
  rw [meetT, iInf_prop_iff]
  simp only [iInf_apply, iInf_Prop_eq]
  exact ⟨fun h P hP => h ⟨P, hP⟩, fun h P => h P.1 P.2⟩

theorem sInf_T_prop (S : Set (PretorsionTheory C)) : (sInf S).T.prop = ⨅ P ∈ S, P.T.prop := by
  rw [sInf_eq]
  exact meetT_prop S

theorem sInf_F_prop (S : Set (PretorsionTheory C)) :
    (sInf S).F.prop = ⨅ (F : Subcategory C)
      (_ : IsPretorsionTheory (⨅ P ∈ S, P.T.prop) F.prop ∧ ∀ P ∈ S, P.F.prop ≤ F.prop), F.prop := by
  rw [sInf_eq, ← meetT_prop]
  funext X
  apply propext
  show (Subcategory.iInf (fun F : MeetPartners S => F.1)).prop X ↔ _
  rw [iInf_prop_iff]
  simp only [iInf_apply, iInf_Prop_eq]
  exact ⟨fun h F hF => h ⟨F, hF⟩, fun h F => h F.1 F.2⟩

theorem meetT_op_image (S : Set (PretorsionTheory C)) :
    (meetT (PretorsionTheory.op '' S)).prop = (⨅ P ∈ S, P.F.prop).op := by
  funext X
  apply propext
  rw [meetT, iInf_prop_iff]
  simp only [ObjectProperty.op_iff, iInf_apply, iInf_Prop_eq]
  constructor
  · intro h P hP
    exact h ⟨P.op, P, hP, rfl⟩
  · rintro h ⟨_, P, hP, rfl⟩
    exact h P hP

theorem sSup_T_prop (S : Set (PretorsionTheory C)) :
    (sSup S).T.prop = ⨅ (T : Subcategory C)
      (_ : IsPretorsionTheory T.prop (⨅ P ∈ S, P.F.prop) ∧ ∀ P ∈ S, P.T.prop ≤ T.prop), T.prop := by
  rw [sSup_eq_join, join_T, meet_F]
  funext X
  apply propext
  rw [Subcategory.unop_prop, ObjectProperty.unop_iff, iInf_prop_iff]
  simp only [iInf_apply, iInf_Prop_eq]
  constructor
  · intro h T hT
    refine h ⟨T.op, ?_, ?_⟩
    · rw [meetT_op_image]
      exact hT.1.op
    · rintro _ ⟨P, hP, rfl⟩
      exact Subcategory.op_le_op_iff.2 (hT.2 P hP)
  · rintro h ⟨G, hG1, hG2⟩
    refine h G.unop ⟨?_, fun P hP => ?_⟩
    · rw [meetT_op_image] at hG1
      exact hG1.unop
    · have := hG2 P.op ⟨P, hP, rfl⟩
      rw [← Subcategory.op_unop G] at this
      exact Subcategory.op_le_op_iff.1 this

theorem sSup_F_prop (S : Set (PretorsionTheory C)) : (sSup S).F.prop = ⨅ P ∈ S, P.F.prop := by
  rw [sSup_eq_join, join_F, Subcategory.unop_prop, meetT_op_image]
  rfl

/-! ### The least and greatest elements -/

/-- `(0, mod)`. -/
def botPT : PretorsionTheory C := ⟨⊥, ⊤, isPretorsionTheory_top_right isQuotientClosed_bot⟩

/-- `(mod, 0)`. -/
def topPT : PretorsionTheory C := ⟨⊤, ⊥, isPretorsionTheory_top_left isSubobjectClosed_bot⟩

theorem bot_eq : (⊥ : PretorsionTheory C) = botPT :=
  le_antisymm bot_le (le_iff.2
    ⟨fun X hX => (⊥ : PretorsionTheory C).T.prop_of_isZero hX, fun _ _ => trivial⟩)

theorem top_eq : (⊤ : PretorsionTheory C) = topPT :=
  le_antisymm (le_iff.2
    ⟨fun _ _ => trivial, fun X hX => (⊤ : PretorsionTheory C).F.prop_of_isZero hX⟩) le_top

end PretorsionTheory

end PretorsionImageClosed.Statement
