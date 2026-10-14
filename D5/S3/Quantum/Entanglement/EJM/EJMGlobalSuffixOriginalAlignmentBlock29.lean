/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixOriginalAlignmentBlock29
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixOriginalAlignmentBlock29
   mirror-E: none(waiver:actual-original-suffix-helper)
   anchors: []
   utility: none
   digest: Checked finite simulation transports full frontier subtrees to the original DAG, preserving actual caches and partial events. -/

/- Prepared exact suffix alignment; compilation is still required. Every
cache, partial event, symmetry and gap is the original actual expression.
This is not acceptance of the complete original global certificate. -/

import D5.S3.Quantum.Entanglement.EJM.EJMGlobalDAGData
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock29
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock0
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock1
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock3
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock4
import D5.S0.Certificates.FiniteCachedSymmetryDAGSimulation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 65536
set_option linter.style.longLine false

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixOriginalAlignmentBlock29
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (check)
open D5.S0.Certificates.FiniteCachedSymmetryDAGSimulation
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale)

private def Related744 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) : Prop :=
  (fuel = 4 ∧ left = 744 ∧ right = 161455) ∨
  (fuel = 3 ∧ left = 745 ∧ right = 1950) ∨
  (fuel = 3 ∧ left = 746 ∧ right = 113680) ∨
  (fuel = 2 ∧ left = 747 ∧ right = 1951) ∨
  (fuel = 2 ∧ left = 748 ∧ right = 101524) ∨
  (fuel = 1 ∧ left = 749 ∧ right = 1952) ∨
  (fuel = 1 ∧ left = 750 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 751 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 752 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 753 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 754 ∧ right = 113505) ∨
  (fuel = 1 ∧ left = 755 ∧ right = 4830) ∨
  (fuel = 1 ∧ left = 756 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 757 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 758 ∧ right = 0) ∨
  (fuel = 3 ∧ left = 759 ∧ right = 113713) ∨
  (fuel = 2 ∧ left = 760 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 761 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 762 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 763 ∧ right = 113505) ∨
  (fuel = 1 ∧ left = 764 ∧ right = 4830) ∨
  (fuel = 1 ∧ left = 765 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 766 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 767 ∧ right = 0) ∨
  (fuel = 3 ∧ left = 768 ∧ right = 113542) ∨
  (fuel = 2 ∧ left = 769 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 770 ∧ right = 113505) ∨
  (fuel = 1 ∧ left = 771 ∧ right = 4830) ∨
  (fuel = 1 ∧ left = 772 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 773 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 774 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 775 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 776 ∧ right = 113505) ∨
  (fuel = 1 ∧ left = 777 ∧ right = 4830) ∨
  (fuel = 1 ∧ left = 778 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 779 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 780 ∧ right = 0)

private theorem alignment744 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) (related : Related744 (fuel + 1) left right) :
    StepRelated (Related744 fuel) (pilotNodes (fuel + 1) left)
      (EJMGlobalDAGData.nodes (fuel + 1) right) := by
  rcases related with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 3 := by omega
    subst fuel left right
    have leftShape : pilotNodes 4 744 = .split (17 : Fin 20) ![745,746,759,768] := by
      change (.split (17 : Fin 20)
        (fun a => ⟨(1689257443089713 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock4.shape_4_161455]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related744 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    change StepRelated (Related744 2) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 97 9)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 97 9))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    have leftShape : pilotNodes 3 746 = .split (18 : Fin 20) ![747,748,753,754] := by
      change (.split (18 : Fin 20)
        (fun a => ⟨(1658467896548722 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_3_113680]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related744 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related744 1) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 97 10)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 97 10))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 748 = .split (19 : Fin 20) ![749,750,751,752] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1654068776558003 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock0.shape_2_101524]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related744 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related744 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 97 11)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 97 11))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related744 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related744 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related744 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related744 1) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 754 = .split (19 : Fin 20) ![755,756,757,758] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1667266138103411 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_113505]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related744 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related744 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related744 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related744 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related744 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    have leftShape : pilotNodes 3 759 = .split (18 : Fin 20) ![760,761,762,763] := by
      change (.split (18 : Fin 20)
        (fun a => ⟨(1678263939391250 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock4.shape_3_113713]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related744 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related744 1) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related744 1) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related744 1) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 763 = .split (19 : Fin 20) ![764,765,766,767] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1687062180421523 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_113505]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related744 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related744 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related744 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related744 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related744 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    have leftShape : pilotNodes 3 768 = .split (18 : Fin 20) ![769,770,775,776] := by
      change (.split (18 : Fin 20)
        (fun a => ⟨(1706858222215218 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock3.shape_3_113542]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related744 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related744 1) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 770 = .split (19 : Fin 20) ![771,772,773,774] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1702459102224499 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_113505]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related744 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related744 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related744 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related744 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related744 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related744 1) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 776 = .split (19 : Fin 20) ![777,778,779,780] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1715656463769907 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_113505]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related744 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related744 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related744 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related744 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related744 0) .bound .bound
    exact .bound

theorem originalReceipt744 :
    check EJMGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 161455 cache744 partial744 = true := by
  exact checked_simulation pilotNodes EJMGlobalDAGData.nodes step lower
    EJMGlobalScoreSymmetry.dominates scale Related744 alignment744
    4 744 161455 cache744 partial744 (by unfold Related744; decide +kernel)
    EJMGlobalSuffixProbeBlock29.receipt744

#print axioms originalReceipt744

end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixOriginalAlignmentBlock29
