/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixOriginalAlignmentBlock34
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixOriginalAlignmentBlock34
   mirror-E: none(waiver:actual-original-suffix-helper)
   anchors: []
   utility: none
   digest: Checked finite simulation transports full frontier subtrees to the original DAG, preserving actual caches and partial events. -/

/- Prepared exact suffix alignment; compilation is still required. Every
cache, partial event, symmetry and gap is the original actual expression.
This is not acceptance of the complete original global certificate. -/

import D5.S3.Quantum.Entanglement.EJM.EJMGlobalDAGData
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock34
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock0
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock1
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock2
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock3
import D5.S0.Certificates.FiniteCachedSymmetryDAGSimulation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 65536
set_option linter.style.longLine false

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixOriginalAlignmentBlock34
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (check)
open D5.S0.Certificates.FiniteCachedSymmetryDAGSimulation
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale)

private def Related487 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) : Prop :=
  (fuel = 4 ∧ left = 487 ∧ right = 161445) ∨
  (fuel = 3 ∧ left = 488 ∧ right = 1950) ∨
  (fuel = 3 ∧ left = 489 ∧ right = 113693) ∨
  (fuel = 2 ∧ left = 490 ∧ right = 1951) ∨
  (fuel = 2 ∧ left = 491 ∧ right = 101524) ∨
  (fuel = 1 ∧ left = 492 ∧ right = 1952) ∨
  (fuel = 1 ∧ left = 493 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 494 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 495 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 496 ∧ right = 113505) ∨
  (fuel = 1 ∧ left = 497 ∧ right = 4830) ∨
  (fuel = 1 ∧ left = 498 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 499 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 500 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 501 ∧ right = 113505) ∨
  (fuel = 1 ∧ left = 502 ∧ right = 4830) ∨
  (fuel = 1 ∧ left = 503 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 504 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 505 ∧ right = 0) ∨
  (fuel = 3 ∧ left = 506 ∧ right = 92176) ∨
  (fuel = 2 ∧ left = 507 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 508 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 509 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 510 ∧ right = 0) ∨
  (fuel = 3 ∧ left = 511 ∧ right = 114004) ∨
  (fuel = 2 ∧ left = 512 ∧ right = 113681) ∨
  (fuel = 1 ∧ left = 513 ∧ right = 4830) ∨
  (fuel = 1 ∧ left = 514 ∧ right = 4831) ∨
  (fuel = 1 ∧ left = 515 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 516 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 517 ∧ right = 113505) ∨
  (fuel = 1 ∧ left = 518 ∧ right = 4830) ∨
  (fuel = 1 ∧ left = 519 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 520 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 521 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 522 ∧ right = 113505) ∨
  (fuel = 1 ∧ left = 523 ∧ right = 4830) ∨
  (fuel = 1 ∧ left = 524 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 525 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 526 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 527 ∧ right = 0)

private theorem alignment487 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) (related : Related487 (fuel + 1) left right) :
    StepRelated (Related487 fuel) (pilotNodes (fuel + 1) left)
      (EJMGlobalDAGData.nodes (fuel + 1) right) := by
  rcases related with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 3 := by omega
    subst fuel left right
    have leftShape : pilotNodes 4 487 = .split (17 : Fin 20) ![488,489,506,511] := by
      change (.split (17 : Fin 20)
        (fun a => ⟨(1123972604378385 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock3.shape_4_161445]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related487 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    change StepRelated (Related487 2) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 97 9)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 97 9))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    have leftShape : pilotNodes 3 489 = .split (18 : Fin 20) ![490,491,496,501] := by
      change (.split (18 : Fin 20)
        (fun a => ⟨(1101977003375954 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock2.shape_3_113693]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related487 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related487 1) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 97 10)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 97 10))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 491 = .split (19 : Fin 20) ![492,493,494,495] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1088781790363027 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock0.shape_2_101524]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related487 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related487 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 97 11)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 97 11))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related487 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related487 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related487 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 496 = .split (19 : Fin 20) ![497,498,499,500] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1099779591650867 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_113505]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related487 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related487 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related487 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related487 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related487 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 501 = .split (19 : Fin 20) ![502,503,504,505] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1110777392938707 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_113505]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related487 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related487 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related487 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related487 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related487 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    have leftShape : pilotNodes 3 506 = .split (18 : Fin 20) ![507,508,509,510] := by
      change (.split (18 : Fin 20)
        (fun a => ⟨(1121775194226546 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock2.shape_3_92176]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related487 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related487 1) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related487 1) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related487 1) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related487 1) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    have leftShape : pilotNodes 3 511 = .split (18 : Fin 20) ![512,517,522,527] := by
      change (.split (18 : Fin 20)
        (fun a => ⟨(1159165570072594 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock3.shape_3_114004]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related487 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 512 = .split (19 : Fin 20) ![513,514,515,516] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1134972555771955 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_113681]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related487 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related487 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related487 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 10)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 10))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related487 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related487 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 517 = .split (19 : Fin 20) ![518,519,520,521] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1145970357059795 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_113505]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related487 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related487 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related487 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related487 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related487 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 522 = .split (19 : Fin 20) ![523,524,525,526] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1156968158347635 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_113505]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related487 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related487 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related487 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related487 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related487 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related487 1) .bound .bound
    exact .bound

theorem originalReceipt487 :
    check EJMGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 161445 cache487 partial487 = true := by
  exact checked_simulation pilotNodes EJMGlobalDAGData.nodes step lower
    EJMGlobalScoreSymmetry.dominates scale Related487 alignment487
    4 487 161445 cache487 partial487 (by unfold Related487; decide +kernel)
    EJMGlobalSuffixProbeBlock34.receipt487

#print axioms originalReceipt487

end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixOriginalAlignmentBlock34
