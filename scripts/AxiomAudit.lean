module

public import PretorsionImageClosed
public import Solution

/-! Axiom report for the main theorems and their intermediate forms.
Run with `lake env lean scripts/AxiomAudit.lean`, or `python3 scripts/audit_axioms.py`. -/

@[expose] public section

#print axioms PretorsionImageClosed.theoremA
#print axioms PretorsionImageClosed.completeLattice
#print axioms PretorsionImageClosed.gandhiPretorsion
#print axioms PretorsionImageClosed.gandhiImageClosed
#print axioms PretorsionImageClosed.theoremBPretorsion
#print axioms PretorsionImageClosed.theoremBImageClosed
#print axioms PretorsionImageClosed.Statement.isPretorsionTheory_iff_traceRejectCondition
#print axioms PretorsionImageClosed.Statement.isPretorsionTheory_iInf
#print axioms PretorsionImageClosed.Statement.isPretorsionTheory_iInf_left
#print axioms PretorsionImageClosed.Statement.PretorsionTheory.sInf_middle
#print axioms PretorsionImageClosed.Statement.PretorsionTheory.sSup_middle
#print axioms PretorsionImageClosed.Statement.isTorsionPair_iff
#print axioms PretorsionImageClosed.Statement.realization_bounds
#print axioms PretorsionImageClosed.LinearQuiver.isImageClosed_iff_intersectionClosed
#print axioms PretorsionImageClosed.LinearQuiver.isPretorsionTheory_iff_criterion
#print axioms PretorsionImageClosed.LinearQuiver.cpSum_eq
#print axioms PretorsionImageClosed.LinearQuiver.xSum_eq
#print axioms PretorsionImageClosed.Challenge.theoremA
#print axioms PretorsionImageClosed.Challenge.completeLattice
#print axioms PretorsionImageClosed.Challenge.gandhiPretorsion
#print axioms PretorsionImageClosed.Challenge.gandhiImageClosed
#print axioms PretorsionImageClosed.Challenge.theoremBPretorsion
#print axioms PretorsionImageClosed.Challenge.theoremBImageClosed
