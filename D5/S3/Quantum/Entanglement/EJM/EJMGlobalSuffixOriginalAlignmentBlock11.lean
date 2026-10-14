/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixOriginalAlignmentBlock11
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixOriginalAlignmentBlock11
   mirror-E: none(waiver:actual-original-suffix-helper)
   anchors: []
   utility: none
   digest: Checked finite simulation transports full frontier subtrees to the original DAG, preserving actual caches and partial events. -/

/- Prepared exact suffix alignment; compilation is still required. Every
cache, partial event, symmetry and gap is the original actual expression.
This is not acceptance of the complete original global certificate. -/

import D5.S3.Quantum.Entanglement.EJM.EJMGlobalDAGData
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock11
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock0
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock1
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock7
import D5.S0.Certificates.FiniteCachedSymmetryDAGSimulation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 65536
set_option linter.style.longLine false

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixOriginalAlignmentBlock11
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (check)
open D5.S0.Certificates.FiniteCachedSymmetryDAGSimulation
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale)

private def Related1515 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) : Prop :=
  (fuel = 4 ∧ left = 1515 ∧ right = 113747) ∨
  (fuel = 3 ∧ left = 1516 ∧ right = 494) ∨
  (fuel = 3 ∧ left = 1517 ∧ right = 494) ∨
  (fuel = 3 ∧ left = 1518 ∧ right = 494) ∨
  (fuel = 3 ∧ left = 1519 ∧ right = 113746) ∨
  (fuel = 2 ∧ left = 1520 ∧ right = 92336) ∨
  (fuel = 1 ∧ left = 1521 ∧ right = 496) ∨
  (fuel = 1 ∧ left = 1522 ∧ right = 496) ∨
  (fuel = 1 ∧ left = 1523 ∧ right = 496) ∨
  (fuel = 1 ∧ left = 1524 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 1525 ∧ right = 92278) ∨
  (fuel = 1 ∧ left = 1526 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 1527 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 1528 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 1529 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 1530 ∧ right = 92278) ∨
  (fuel = 1 ∧ left = 1531 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 1532 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 1533 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 1534 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 1535 ∧ right = 92278) ∨
  (fuel = 1 ∧ left = 1536 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 1537 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 1538 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 1539 ∧ right = 0)

private theorem alignment1515 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) (related : Related1515 (fuel + 1) left right) :
    StepRelated (Related1515 fuel) (pilotNodes (fuel + 1) left)
      (EJMGlobalDAGData.nodes (fuel + 1) right) := by
  rcases related with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 3 := by omega
    subst fuel left right
    have leftShape : pilotNodes 4 1515 = .split (17 : Fin 20) ![1516,1517,1518,1519] := by
      change (.split (17 : Fin 20)
        (fun a => ⟨(3341131494112657 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock7.shape_4_113747]
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
    change StepRelated (Related1515 2) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    change StepRelated (Related1515 2) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    change StepRelated (Related1515 2) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    have leftShape : pilotNodes 3 1519 = .split (18 : Fin 20) ![1520,1525,1530,1535] := by
      change (.split (18 : Fin 20)
        (fun a => ⟨(3376322309701138 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock7.shape_3_113746]
    apply StepRelated.split
    intro a
    fin_cases a
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩)))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩))))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩)))))))))))))))))))))
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 1520 = .split (19 : Fin 20) ![1521,1522,1523,1524] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3352129295400499 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_92336]
    apply StepRelated.split
    intro a
    fin_cases a
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩)))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩))))))))))
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1515 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1515 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1515 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1515 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 1525 = .split (19 : Fin 20) ![1526,1527,1528,1529] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3363127096688339 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock0.shape_2_92278]
    apply StepRelated.split
    intro a
    fin_cases a
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩)))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩)))))))))))))))
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1515 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1515 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1515 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1515 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 1530 = .split (19 : Fin 20) ![1531,1532,1533,1534] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3374124897976179 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock0.shape_2_92278]
    apply StepRelated.split
    intro a
    fin_cases a
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩)))))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩))))))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩)))))))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩))))))))))))))))))))
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1515 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1515 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1515 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1515 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 1535 = .split (19 : Fin 20) ![1536,1537,1538,1539] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3385122699264019 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock0.shape_2_92278]
    apply StepRelated.split
    intro a
    fin_cases a
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩))))))))))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩)))))))))))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩))))))))))))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨rfl, rfl, rfl⟩))))))))))))))))))))))))
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1515 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1515 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1515 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1515 0) .bound .bound
    exact .bound

theorem originalReceipt1515 :
    check EJMGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 113747 cache1515 partial1515 = true := by
  exact checked_simulation pilotNodes EJMGlobalDAGData.nodes step lower
    EJMGlobalScoreSymmetry.dominates scale Related1515 alignment1515
    4 1515 113747 cache1515 partial1515 (Or.inl (⟨rfl, rfl, rfl⟩))
    EJMGlobalSuffixProbeBlock11.receipt1515

#print axioms originalReceipt1515

private def Related1514 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) : Prop :=
  (fuel = 4 ∧ left = 1514 ∧ right = 493)

private theorem alignment1514 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) (related : Related1514 (fuel + 1) left right) :
    StepRelated (Related1514 fuel) (pilotNodes (fuel + 1) left)
      (EJMGlobalDAGData.nodes (fuel + 1) right) := by
  rcases related with ⟨hf, hl, hr⟩
  have amount : fuel = 3 := by omega
  subst fuel left right
  change StepRelated (Related1514 3) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12))
  exact .symmetry _

theorem originalReceipt1514 :
    check EJMGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 493 cache1514 partial1514 = true := by
  exact checked_simulation pilotNodes EJMGlobalDAGData.nodes step lower
    EJMGlobalScoreSymmetry.dominates scale Related1514 alignment1514
    4 1514 493 cache1514 partial1514 (⟨rfl, rfl, rfl⟩)
    EJMGlobalSuffixProbeBlock11.receipt1514

#print axioms originalReceipt1514

private def Related1513 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) : Prop :=
  (fuel = 4 ∧ left = 1513 ∧ right = 493)

private theorem alignment1513 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) (related : Related1513 (fuel + 1) left right) :
    StepRelated (Related1513 fuel) (pilotNodes (fuel + 1) left)
      (EJMGlobalDAGData.nodes (fuel + 1) right) := by
  rcases related with ⟨hf, hl, hr⟩
  have amount : fuel = 3 := by omega
  subst fuel left right
  change StepRelated (Related1513 3) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12))
  exact .symmetry _

theorem originalReceipt1513 :
    check EJMGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 493 cache1513 partial1513 = true := by
  exact checked_simulation pilotNodes EJMGlobalDAGData.nodes step lower
    EJMGlobalScoreSymmetry.dominates scale Related1513 alignment1513
    4 1513 493 cache1513 partial1513 (⟨rfl, rfl, rfl⟩)
    EJMGlobalSuffixProbeBlock11.receipt1513

#print axioms originalReceipt1513

private def Related1511 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) : Prop :=
  (fuel = 5 ∧ left = 1511 ∧ right = 2894)

private theorem alignment1511 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) (related : Related1511 (fuel + 1) left right) :
    StepRelated (Related1511 fuel) (pilotNodes (fuel + 1) left)
      (EJMGlobalDAGData.nodes (fuel + 1) right) := by
  rcases related with ⟨hf, hl, hr⟩
  have amount : fuel = 4 := by omega
  subst fuel left right
  change StepRelated (Related1511 4) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 13))
  exact .symmetry _

theorem originalReceipt1511 :
    check EJMGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 2894 cache1511 partial1511 = true := by
  exact checked_simulation pilotNodes EJMGlobalDAGData.nodes step lower
    EJMGlobalScoreSymmetry.dominates scale Related1511 alignment1511
    5 1511 2894 cache1511 partial1511 (⟨rfl, rfl, rfl⟩)
    EJMGlobalSuffixProbeBlock11.receipt1511

#print axioms originalReceipt1511

private def Related1510 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) : Prop :=
  (fuel = 5 ∧ left = 1510 ∧ right = 2894)

private theorem alignment1510 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) (related : Related1510 (fuel + 1) left right) :
    StepRelated (Related1510 fuel) (pilotNodes (fuel + 1) left)
      (EJMGlobalDAGData.nodes (fuel + 1) right) := by
  rcases related with ⟨hf, hl, hr⟩
  have amount : fuel = 4 := by omega
  subst fuel left right
  change StepRelated (Related1510 4) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 13))
  exact .symmetry _

theorem originalReceipt1510 :
    check EJMGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 2894 cache1510 partial1510 = true := by
  exact checked_simulation pilotNodes EJMGlobalDAGData.nodes step lower
    EJMGlobalScoreSymmetry.dominates scale Related1510 alignment1510
    5 1510 2894 cache1510 partial1510 (⟨rfl, rfl, rfl⟩)
    EJMGlobalSuffixProbeBlock11.receipt1510

#print axioms originalReceipt1510

private def Related1509 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) : Prop :=
  (fuel = 5 ∧ left = 1509 ∧ right = 2894)

private theorem alignment1509 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) (related : Related1509 (fuel + 1) left right) :
    StepRelated (Related1509 fuel) (pilotNodes (fuel + 1) left)
      (EJMGlobalDAGData.nodes (fuel + 1) right) := by
  rcases related with ⟨hf, hl, hr⟩
  have amount : fuel = 4 := by omega
  subst fuel left right
  change StepRelated (Related1509 4) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 13))
  exact .symmetry _

theorem originalReceipt1509 :
    check EJMGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 2894 cache1509 partial1509 = true := by
  exact checked_simulation pilotNodes EJMGlobalDAGData.nodes step lower
    EJMGlobalScoreSymmetry.dominates scale Related1509 alignment1509
    5 1509 2894 cache1509 partial1509 (⟨rfl, rfl, rfl⟩)
    EJMGlobalSuffixProbeBlock11.receipt1509

#print axioms originalReceipt1509

end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixOriginalAlignmentBlock11
