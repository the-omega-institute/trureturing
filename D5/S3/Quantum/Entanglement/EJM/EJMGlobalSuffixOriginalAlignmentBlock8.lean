/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixOriginalAlignmentBlock8
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixOriginalAlignmentBlock8
   mirror-E: none(waiver:actual-original-suffix-helper)
   anchors: []
   utility: none
   digest: Checked finite simulation transports full frontier subtrees to the original DAG, preserving actual caches and partial events. -/

/- Prepared exact suffix alignment; compilation is still required. Every
cache, partial event, symmetry and gap is the original actual expression.
This is not acceptance of the complete original global certificate. -/

import D5.S3.Quantum.Entanglement.EJM.EJMGlobalDAGData
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock8
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock0
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock1
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock8
import D5.S0.Certificates.FiniteCachedSymmetryDAGSimulation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 65536
set_option linter.style.longLine false

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixOriginalAlignmentBlock8
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (check)
open D5.S0.Certificates.FiniteCachedSymmetryDAGSimulation
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale)

private def Related1665 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) : Prop :=
  (fuel = 4 ∧ left = 1665 ∧ right = 108887) ∨
  (fuel = 3 ∧ left = 1666 ∧ right = 494) ∨
  (fuel = 3 ∧ left = 1667 ∧ right = 494) ∨
  (fuel = 3 ∧ left = 1668 ∧ right = 494) ∨
  (fuel = 3 ∧ left = 1669 ∧ right = 108886) ∨
  (fuel = 2 ∧ left = 1670 ∧ right = 495) ∨
  (fuel = 2 ∧ left = 1671 ∧ right = 495) ∨
  (fuel = 2 ∧ left = 1672 ∧ right = 92336) ∨
  (fuel = 1 ∧ left = 1673 ∧ right = 496) ∨
  (fuel = 1 ∧ left = 1674 ∧ right = 496) ∨
  (fuel = 1 ∧ left = 1675 ∧ right = 496) ∨
  (fuel = 1 ∧ left = 1676 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 1677 ∧ right = 92278) ∨
  (fuel = 1 ∧ left = 1678 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 1679 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 1680 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 1681 ∧ right = 0)

private theorem alignment1665 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) (related : Related1665 (fuel + 1) left right) :
    StepRelated (Related1665 fuel) (pilotNodes (fuel + 1) left)
      (EJMGlobalDAGData.nodes (fuel + 1) right) := by
  rcases related with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 3 := by omega
    subst fuel left right
    have leftShape : pilotNodes 4 1665 = .split (17 : Fin 20) ![1666,1667,1668,1669] := by
      change (.split (17 : Fin 20)
        (fun a => ⟨(3671065532747857 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock8.shape_4_108887]
    apply StepRelated.split
    intro a
    fin_cases a
    · exact Or.inr (Or.inl (⟨rfl, rfl, rfl⟩))
    · exact Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩)))))
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    change StepRelated (Related1665 2) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    change StepRelated (Related1665 2) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    change StepRelated (Related1665 2) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    have leftShape : pilotNodes 3 1669 = .split (18 : Fin 20) ![1670,1671,1672,1677] := by
      change (.split (18 : Fin 20)
        (fun a => ⟨(3688659866800338 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock8.shape_3_108886]
    apply StepRelated.split
    intro a
    fin_cases a
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩)))))))))))))
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related1665 1) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 14)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 14))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related1665 1) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 14)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 14))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 1672 = .split (19 : Fin 20) ![1673,1674,1675,1676] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3686462454550835 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_92336]
    apply StepRelated.split
    intro a
    fin_cases a
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩)))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩)))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩))))))))))))
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1665 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1665 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1665 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1665 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 1677 = .split (19 : Fin 20) ![1678,1679,1680,1681] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3697460255838675 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock0.shape_2_92278]
    apply StepRelated.split
    intro a
    fin_cases a
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩)))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩))))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨rfl, rfl, rfl⟩))))))))))))))))
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1665 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1665 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1665 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1665 0) .bound .bound
    exact .bound

theorem originalReceipt1665 :
    check EJMGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 108887 cache1665 partial1665 = true := by
  exact checked_simulation pilotNodes EJMGlobalDAGData.nodes step lower
    EJMGlobalScoreSymmetry.dominates scale Related1665 alignment1665
    4 1665 108887 cache1665 partial1665 (Or.inl (⟨rfl, rfl, rfl⟩))
    EJMGlobalSuffixProbeBlock8.receipt1665

#print axioms originalReceipt1665

private def Related1664 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) : Prop :=
  (fuel = 4 ∧ left = 1664 ∧ right = 493)

private theorem alignment1664 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) (related : Related1664 (fuel + 1) left right) :
    StepRelated (Related1664 fuel) (pilotNodes (fuel + 1) left)
      (EJMGlobalDAGData.nodes (fuel + 1) right) := by
  rcases related with ⟨hf, hl, hr⟩
  have amount : fuel = 3 := by omega
  subst fuel left right
  change StepRelated (Related1664 3) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12))
  exact .symmetry _

theorem originalReceipt1664 :
    check EJMGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 493 cache1664 partial1664 = true := by
  exact checked_simulation pilotNodes EJMGlobalDAGData.nodes step lower
    EJMGlobalScoreSymmetry.dominates scale Related1664 alignment1664
    4 1664 493 cache1664 partial1664 (⟨rfl, rfl, rfl⟩)
    EJMGlobalSuffixProbeBlock8.receipt1664

#print axioms originalReceipt1664

private def Related1663 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) : Prop :=
  (fuel = 4 ∧ left = 1663 ∧ right = 493)

private theorem alignment1663 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) (related : Related1663 (fuel + 1) left right) :
    StepRelated (Related1663 fuel) (pilotNodes (fuel + 1) left)
      (EJMGlobalDAGData.nodes (fuel + 1) right) := by
  rcases related with ⟨hf, hl, hr⟩
  have amount : fuel = 3 := by omega
  subst fuel left right
  change StepRelated (Related1663 3) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12))
  exact .symmetry _

theorem originalReceipt1663 :
    check EJMGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 493 cache1663 partial1663 = true := by
  exact checked_simulation pilotNodes EJMGlobalDAGData.nodes step lower
    EJMGlobalScoreSymmetry.dominates scale Related1663 alignment1663
    4 1663 493 cache1663 partial1663 (⟨rfl, rfl, rfl⟩)
    EJMGlobalSuffixProbeBlock8.receipt1663

#print axioms originalReceipt1663

private def Related1661 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) : Prop :=
  (fuel = 5 ∧ left = 1661 ∧ right = 2894)

private theorem alignment1661 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) (related : Related1661 (fuel + 1) left right) :
    StepRelated (Related1661 fuel) (pilotNodes (fuel + 1) left)
      (EJMGlobalDAGData.nodes (fuel + 1) right) := by
  rcases related with ⟨hf, hl, hr⟩
  have amount : fuel = 4 := by omega
  subst fuel left right
  change StepRelated (Related1661 4) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 13))
  exact .symmetry _

theorem originalReceipt1661 :
    check EJMGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 2894 cache1661 partial1661 = true := by
  exact checked_simulation pilotNodes EJMGlobalDAGData.nodes step lower
    EJMGlobalScoreSymmetry.dominates scale Related1661 alignment1661
    5 1661 2894 cache1661 partial1661 (⟨rfl, rfl, rfl⟩)
    EJMGlobalSuffixProbeBlock8.receipt1661

#print axioms originalReceipt1661

private def Related1660 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) : Prop :=
  (fuel = 5 ∧ left = 1660 ∧ right = 2894)

private theorem alignment1660 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) (related : Related1660 (fuel + 1) left right) :
    StepRelated (Related1660 fuel) (pilotNodes (fuel + 1) left)
      (EJMGlobalDAGData.nodes (fuel + 1) right) := by
  rcases related with ⟨hf, hl, hr⟩
  have amount : fuel = 4 := by omega
  subst fuel left right
  change StepRelated (Related1660 4) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 13))
  exact .symmetry _

theorem originalReceipt1660 :
    check EJMGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 2894 cache1660 partial1660 = true := by
  exact checked_simulation pilotNodes EJMGlobalDAGData.nodes step lower
    EJMGlobalScoreSymmetry.dominates scale Related1660 alignment1660
    5 1660 2894 cache1660 partial1660 (⟨rfl, rfl, rfl⟩)
    EJMGlobalSuffixProbeBlock8.receipt1660

#print axioms originalReceipt1660

private def Related1659 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) : Prop :=
  (fuel = 5 ∧ left = 1659 ∧ right = 2894)

private theorem alignment1659 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) (related : Related1659 (fuel + 1) left right) :
    StepRelated (Related1659 fuel) (pilotNodes (fuel + 1) left)
      (EJMGlobalDAGData.nodes (fuel + 1) right) := by
  rcases related with ⟨hf, hl, hr⟩
  have amount : fuel = 4 := by omega
  subst fuel left right
  change StepRelated (Related1659 4) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 13))
  exact .symmetry _

theorem originalReceipt1659 :
    check EJMGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 2894 cache1659 partial1659 = true := by
  exact checked_simulation pilotNodes EJMGlobalDAGData.nodes step lower
    EJMGlobalScoreSymmetry.dominates scale Related1659 alignment1659
    5 1659 2894 cache1659 partial1659 (⟨rfl, rfl, rfl⟩)
    EJMGlobalSuffixProbeBlock8.receipt1659

#print axioms originalReceipt1659

end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixOriginalAlignmentBlock8
