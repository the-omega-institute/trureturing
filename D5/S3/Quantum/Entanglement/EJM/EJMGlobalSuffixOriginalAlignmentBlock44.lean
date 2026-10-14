/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixOriginalAlignmentBlock44
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixOriginalAlignmentBlock44
   mirror-E: none(waiver:actual-original-suffix-helper)
   anchors: []
   utility: none
   digest: Checked finite simulation transports full frontier subtrees to the original DAG, preserving actual caches and partial events. -/

/- Prepared exact suffix alignment; compilation is still required. Every
cache, partial event, symmetry and gap is the original actual expression.
This is not acceptance of the complete original global certificate. -/

import D5.S3.Quantum.Entanglement.EJM.EJMGlobalDAGData
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock44
import D5.S0.Certificates.FiniteCachedSymmetryDAGSimulation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 65536
set_option linter.style.longLine false

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixOriginalAlignmentBlock44
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (check)
open D5.S0.Certificates.FiniteCachedSymmetryDAGSimulation
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale)

private def Related6 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) : Prop :=
  (fuel = 6 ∧ left = 6 ∧ right = 971)

private theorem alignment6 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) (related : Related6 (fuel + 1) left right) :
    StepRelated (Related6 fuel) (pilotNodes (fuel + 1) left)
      (EJMGlobalDAGData.nodes (fuel + 1) right) := by
  rcases related with ⟨hf, hl, hr⟩
  have amount : fuel = 5 := by omega
  subst fuel left right
  change StepRelated (Related6 5) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 48 10)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 48 10))
  exact .symmetry _

theorem originalReceipt6 :
    check EJMGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
      scale 6 971 cache6 partial6 = true := by
  exact checked_simulation pilotNodes EJMGlobalDAGData.nodes step lower
    EJMGlobalScoreSymmetry.dominates scale Related6 alignment6
    6 6 971 cache6 partial6 (by unfold Related6; decide +kernel)
    EJMGlobalSuffixProbeBlock44.receipt6

#print axioms originalReceipt6

private def Related4 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) : Prop :=
  (fuel = 7 ∧ left = 4 ∧ right = 970)

private theorem alignment4 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) (related : Related4 (fuel + 1) left right) :
    StepRelated (Related4 fuel) (pilotNodes (fuel + 1) left)
      (EJMGlobalDAGData.nodes (fuel + 1) right) := by
  rcases related with ⟨hf, hl, hr⟩
  have amount : fuel = 6 := by omega
  subst fuel left right
  change StepRelated (Related4 6) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 48 9)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 48 9))
  exact .symmetry _

theorem originalReceipt4 :
    check EJMGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
      scale 7 970 cache4 partial4 = true := by
  exact checked_simulation pilotNodes EJMGlobalDAGData.nodes step lower
    EJMGlobalScoreSymmetry.dominates scale Related4 alignment4
    7 4 970 cache4 partial4 (by unfold Related4; decide +kernel)
    EJMGlobalSuffixProbeBlock44.receipt4

#print axioms originalReceipt4

private def Related2 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) : Prop :=
  (fuel = 8 ∧ left = 2 ∧ right = 969)

private theorem alignment2 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) (related : Related2 (fuel + 1) left right) :
    StepRelated (Related2 fuel) (pilotNodes (fuel + 1) left)
      (EJMGlobalDAGData.nodes (fuel + 1) right) := by
  rcases related with ⟨hf, hl, hr⟩
  have amount : fuel = 7 := by omega
  subst fuel left right
  change StepRelated (Related2 7) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 48 8)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 48 8))
  exact .symmetry _

theorem originalReceipt2 :
    check EJMGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
      scale 8 969 cache2 partial2 = true := by
  exact checked_simulation pilotNodes EJMGlobalDAGData.nodes step lower
    EJMGlobalScoreSymmetry.dominates scale Related2 alignment2
    8 2 969 cache2 partial2 (by unfold Related2; decide +kernel)
    EJMGlobalSuffixProbeBlock44.receipt2

#print axioms originalReceipt2

private def Related1 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) : Prop :=
  (fuel = 8 ∧ left = 1 ∧ right = 969)

private theorem alignment1 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) (related : Related1 (fuel + 1) left right) :
    StepRelated (Related1 fuel) (pilotNodes (fuel + 1) left)
      (EJMGlobalDAGData.nodes (fuel + 1) right) := by
  rcases related with ⟨hf, hl, hr⟩
  have amount : fuel = 7 := by omega
  subst fuel left right
  change StepRelated (Related1 7) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 48 8)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 48 8))
  exact .symmetry _

theorem originalReceipt1 :
    check EJMGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
      scale 8 969 cache1 partial1 = true := by
  exact checked_simulation pilotNodes EJMGlobalDAGData.nodes step lower
    EJMGlobalScoreSymmetry.dominates scale Related1 alignment1
    8 1 969 cache1 partial1 (by unfold Related1; decide +kernel)
    EJMGlobalSuffixProbeBlock44.receipt1

#print axioms originalReceipt1

end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixOriginalAlignmentBlock44
