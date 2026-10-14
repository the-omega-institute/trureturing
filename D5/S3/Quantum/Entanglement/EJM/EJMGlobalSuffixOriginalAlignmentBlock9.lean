/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixOriginalAlignmentBlock9
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixOriginalAlignmentBlock9
   mirror-E: none(waiver:actual-original-suffix-helper)
   anchors: []
   utility: none
   digest: Checked finite simulation transports full frontier subtrees to the original DAG, preserving actual caches and partial events. -/

/- Prepared exact suffix alignment; compilation is still required. Every
cache, partial event, symmetry and gap is the original actual expression.
This is not acceptance of the complete original global certificate. -/

import D5.S3.Quantum.Entanglement.EJM.EJMGlobalDAGData
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock9
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock0
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock1
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock5
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock7
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock8
import D5.S0.Certificates.FiniteCachedSymmetryDAGSimulation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 65536
set_option linter.style.longLine false

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixOriginalAlignmentBlock9
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (check)
open D5.S0.Certificates.FiniteCachedSymmetryDAGSimulation
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale)

private def Related1597 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) : Prop :=
  (fuel = 6 ∧ left = 1597 ∧ right = 161496) ∨
  (fuel = 5 ∧ left = 1598 ∧ right = 2894) ∨
  (fuel = 5 ∧ left = 1599 ∧ right = 2894) ∨
  (fuel = 5 ∧ left = 1600 ∧ right = 2894) ∨
  (fuel = 5 ∧ left = 1601 ∧ right = 161495) ∨
  (fuel = 4 ∧ left = 1602 ∧ right = 493) ∨
  (fuel = 4 ∧ left = 1603 ∧ right = 493) ∨
  (fuel = 4 ∧ left = 1604 ∧ right = 110014) ∨
  (fuel = 3 ∧ left = 1605 ∧ right = 494) ∨
  (fuel = 3 ∧ left = 1606 ∧ right = 494) ∨
  (fuel = 3 ∧ left = 1607 ∧ right = 494) ∨
  (fuel = 3 ∧ left = 1608 ∧ right = 110013) ∨
  (fuel = 2 ∧ left = 1609 ∧ right = 495) ∨
  (fuel = 2 ∧ left = 1610 ∧ right = 92336) ∨
  (fuel = 1 ∧ left = 1611 ∧ right = 496) ∨
  (fuel = 1 ∧ left = 1612 ∧ right = 496) ∨
  (fuel = 1 ∧ left = 1613 ∧ right = 496) ∨
  (fuel = 1 ∧ left = 1614 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 1615 ∧ right = 92278) ∨
  (fuel = 1 ∧ left = 1616 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 1617 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 1618 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 1619 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 1620 ∧ right = 92278) ∨
  (fuel = 1 ∧ left = 1621 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 1622 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 1623 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 1624 ∧ right = 0) ∨
  (fuel = 4 ∧ left = 1625 ∧ right = 161494) ∨
  (fuel = 3 ∧ left = 1626 ∧ right = 1950) ∨
  (fuel = 3 ∧ left = 1627 ∧ right = 101532) ∨
  (fuel = 2 ∧ left = 1628 ∧ right = 1951) ∨
  (fuel = 2 ∧ left = 1629 ∧ right = 101524) ∨
  (fuel = 1 ∧ left = 1630 ∧ right = 1952) ∨
  (fuel = 1 ∧ left = 1631 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 1632 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 1633 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 1634 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 1635 ∧ right = 0) ∨
  (fuel = 3 ∧ left = 1636 ∧ right = 105972) ∨
  (fuel = 2 ∧ left = 1637 ∧ right = 92170) ∨
  (fuel = 1 ∧ left = 1638 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 1639 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 1640 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 1641 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 1642 ∧ right = 92170) ∨
  (fuel = 1 ∧ left = 1643 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 1644 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 1645 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 1646 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 1647 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 1648 ∧ right = 0) ∨
  (fuel = 3 ∧ left = 1649 ∧ right = 105970) ∨
  (fuel = 2 ∧ left = 1650 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 1651 ∧ right = 92278) ∨
  (fuel = 1 ∧ left = 1652 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 1653 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 1654 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 1655 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 1656 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 1657 ∧ right = 0)

private theorem alignment1597 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) (related : Related1597 (fuel + 1) left right) :
    StepRelated (Related1597 fuel) (pilotNodes (fuel + 1) left)
      (EJMGlobalDAGData.nodes (fuel + 1) right) := by
  rcases related with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 5 := by omega
    subst fuel left right
    have leftShape : pilotNodes 6 1597 = .split (15 : Fin 20) ![1598,1599,1600,1601] := by
      change (.split (15 : Fin 20)
        (fun a => ⟨(3521495435233231 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (15 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock7.shape_6_161496]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1597 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 4 := by omega
    subst fuel left right
    change StepRelated (Related1597 4) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 4 := by omega
    subst fuel left right
    change StepRelated (Related1597 4) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 4 := by omega
    subst fuel left right
    change StepRelated (Related1597 4) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 4 := by omega
    subst fuel left right
    have leftShape : pilotNodes 5 1601 = .split (16 : Fin 20) ![1602,1603,1604,1625] := by
      change (.split (16 : Fin 20)
        (fun a => ⟨(3574274141374544 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (16 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock8.shape_5_161495]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1597 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 3 := by omega
    subst fuel left right
    change StepRelated (Related1597 3) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 3 := by omega
    subst fuel left right
    change StepRelated (Related1597 3) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 3 := by omega
    subst fuel left right
    have leftShape : pilotNodes 4 1604 = .split (17 : Fin 20) ![1605,1606,1607,1608] := by
      change (.split (17 : Fin 20)
        (fun a => ⟨(3536892357036209 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock8.shape_4_110014]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1597 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    change StepRelated (Related1597 2) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    change StepRelated (Related1597 2) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    change StepRelated (Related1597 2) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    have leftShape : pilotNodes 3 1608 = .split (18 : Fin 20) ![1609,1610,1615,1620] := by
      change (.split (18 : Fin 20)
        (fun a => ⟨(3563284931594546 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock8.shape_3_110013]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1597 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related1597 1) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 14)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 14))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 1610 = .split (19 : Fin 20) ![1611,1612,1613,1614] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3550089718581619 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_92336]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1597 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1597 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1597 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1597 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1597 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 1615 = .split (19 : Fin 20) ![1616,1617,1618,1619] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3561087519869459 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock0.shape_2_92278]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1597 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1597 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1597 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1597 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1597 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 1620 = .split (19 : Fin 20) ![1621,1622,1623,1624] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3572085321157299 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock0.shape_2_92278]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1597 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1597 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1597 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1597 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1597 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 3 := by omega
    subst fuel left right
    have leftShape : pilotNodes 4 1625 = .split (17 : Fin 20) ![1626,1627,1636,1649] := by
      change (.split (17 : Fin 20)
        (fun a => ⟨(3627067882523473 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock8.shape_4_161494]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1597 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    change StepRelated (Related1597 2) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 97 9)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 97 9))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    have leftShape : pilotNodes 3 1627 = .split (18 : Fin 20) ![1628,1629,1634,1635] := by
      change (.split (18 : Fin 20)
        (fun a => ⟨(3596280483466130 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock5.shape_3_101532]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1597 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related1597 1) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 97 10)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 97 10))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 1629 = .split (19 : Fin 20) ![1630,1631,1632,1633] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3591881363475411 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock0.shape_2_101524]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1597 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1597 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 97 11)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 97 11))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1597 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1597 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1597 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related1597 1) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related1597 1) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    have leftShape : pilotNodes 3 1636 = .split (18 : Fin 20) ![1637,1642,1647,1648] := by
      change (.split (18 : Fin 20)
        (fun a => ⟨(3624874766814386 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock8.shape_3_105972]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1597 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 1637 = .split (19 : Fin 20) ![1638,1639,1640,1641] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3609477845535955 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock0.shape_2_92170]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1597 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1597 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1597 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1597 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1597 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 1642 = .split (19 : Fin 20) ![1643,1644,1645,1646] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3620475646823795 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock0.shape_2_92170]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1597 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1597 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1597 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1597 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1597 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related1597 1) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related1597 1) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    have leftShape : pilotNodes 3 1649 = .split (18 : Fin 20) ![1650,1651,1656,1657] := by
      change (.split (18 : Fin 20)
        (fun a => ⟨(3644670809132626 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock8.shape_3_105970]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1597 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related1597 1) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 1651 = .split (19 : Fin 20) ![1652,1653,1654,1655] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3640271689141907 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock0.shape_2_92278]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1597 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1597 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1597 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1597 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1597 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related1597 1) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related1597 1) .bound .bound
    exact .bound

theorem originalReceipt1597 :
    check EJMGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
      scale 6 161496 cache1597 partial1597 = true := by
  exact checked_simulation pilotNodes EJMGlobalDAGData.nodes step lower
    EJMGlobalScoreSymmetry.dominates scale Related1597 alignment1597
    6 1597 161496 cache1597 partial1597 (by unfold Related1597; decide +kernel)
    EJMGlobalSuffixProbeBlock9.receipt1597

#print axioms originalReceipt1597

end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixOriginalAlignmentBlock9
