/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixOriginalAlignmentBlock35
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixOriginalAlignmentBlock35
   mirror-E: none(waiver:actual-original-suffix-helper)
   anchors: []
   utility: none
   digest: Checked finite simulation transports full frontier subtrees to the original DAG, preserving actual caches and partial events. -/

/- Prepared exact suffix alignment; compilation is still required. Every
cache, partial event, symmetry and gap is the original actual expression.
This is not acceptance of the complete original global certificate. -/

import D5.S3.Quantum.Entanglement.EJM.EJMGlobalDAGData
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock35
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock1
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock2
import D5.S0.Certificates.FiniteCachedSymmetryDAGSimulation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 65536
set_option linter.style.longLine false

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixOriginalAlignmentBlock35
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (check)
open D5.S0.Certificates.FiniteCachedSymmetryDAGSimulation
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale)

private def Related450 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) : Prop :=
  (fuel = 4 ∧ left = 450 ∧ right = 161444) ∨
  (fuel = 3 ∧ left = 451 ∧ right = 494) ∨
  (fuel = 3 ∧ left = 452 ∧ right = 94923) ∨
  (fuel = 2 ∧ left = 453 ∧ right = 495) ∨
  (fuel = 2 ∧ left = 454 ∧ right = 495) ∨
  (fuel = 2 ∧ left = 455 ∧ right = 92212) ∨
  (fuel = 1 ∧ left = 456 ∧ right = 496) ∨
  (fuel = 1 ∧ left = 457 ∧ right = 496) ∨
  (fuel = 1 ∧ left = 458 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 459 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 460 ∧ right = 92282) ∨
  (fuel = 1 ∧ left = 461 ∧ right = 3374) ∨
  (fuel = 1 ∧ left = 462 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 463 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 464 ∧ right = 0) ∨
  (fuel = 3 ∧ left = 465 ∧ right = 92176) ∨
  (fuel = 2 ∧ left = 466 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 467 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 468 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 469 ∧ right = 0) ∨
  (fuel = 3 ∧ left = 470 ∧ right = 94097) ∨
  (fuel = 2 ∧ left = 471 ∧ right = 92399) ∨
  (fuel = 1 ∧ left = 472 ∧ right = 3374) ∨
  (fuel = 1 ∧ left = 473 ∧ right = 3375) ∨
  (fuel = 1 ∧ left = 474 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 475 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 476 ∧ right = 92399) ∨
  (fuel = 1 ∧ left = 477 ∧ right = 3374) ∨
  (fuel = 1 ∧ left = 478 ∧ right = 3375) ∨
  (fuel = 1 ∧ left = 479 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 480 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 481 ∧ right = 92282) ∨
  (fuel = 1 ∧ left = 482 ∧ right = 3374) ∨
  (fuel = 1 ∧ left = 483 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 484 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 485 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 486 ∧ right = 0)

private theorem alignment450 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) (related : Related450 (fuel + 1) left right) :
    StepRelated (Related450 fuel) (pilotNodes (fuel + 1) left)
      (EJMGlobalDAGData.nodes (fuel + 1) right) := by
  rcases related with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 3 := by omega
    subst fuel left right
    have leftShape : pilotNodes 4 450 = .split (17 : Fin 20) ![451,452,465,470] := by
      change (.split (17 : Fin 20)
        (fun a => ⟨(1033790634342513 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock2.shape_4_161444]
    apply StepRelated.split
    intro a
    fin_cases a
    · exact Or.inr (Or.inl (⟨rfl, rfl, rfl⟩))
    · exact Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩))))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩)))))))))))))))))))))
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    change StepRelated (Related450 2) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    have leftShape : pilotNodes 3 452 = .split (18 : Fin 20) ![453,454,455,460] := by
      change (.split (18 : Fin 20)
        (fun a => ⟨(1011795033340082 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock2.shape_3_94923]
    apply StepRelated.split
    intro a
    fin_cases a
    · exact Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩)))))))))))
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related450 1) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 14)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 14))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related450 1) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 14)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 14))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 455 = .split (19 : Fin 20) ![456,457,458,459] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1009597621090579 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_92212]
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
    change StepRelated (Related450 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related450 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related450 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related450 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 460 = .split (19 : Fin 20) ![461,462,463,464] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1020595422378419 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_92282]
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
    change StepRelated (Related450 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related450 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related450 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related450 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    have leftShape : pilotNodes 3 465 = .split (18 : Fin 20) ![466,467,468,469] := by
      change (.split (18 : Fin 20)
        (fun a => ⟨(1031593223666258 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock2.shape_3_92176]
    apply StepRelated.split
    intro a
    fin_cases a
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩)))))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩))))))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩)))))))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩))))))))))))))))))))
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related450 1) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related450 1) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related450 1) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related450 1) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    have leftShape : pilotNodes 3 470 = .split (18 : Fin 20) ![471,476,481,486] := by
      change (.split (18 : Fin 20)
        (fun a => ⟨(1068983599512306 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock2.shape_3_94097]
    apply StepRelated.split
    intro a
    fin_cases a
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩))))))))))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩)))))))))))))))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩))))))))))))))))))))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨rfl, rfl, rfl⟩))))))))))))))))))))))))))))))))))))
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 471 = .split (19 : Fin 20) ![472,473,474,475] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1044790585211667 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_92399]
    apply StepRelated.split
    intro a
    fin_cases a
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩)))))))))))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩))))))))))))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩)))))))))))))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩))))))))))))))))))))))))))
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related450 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related450 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 14)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 14))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related450 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related450 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 476 = .split (19 : Fin 20) ![477,478,479,480] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1055788386499507 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_92399]
    apply StepRelated.split
    intro a
    fin_cases a
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩))))))))))))))))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩)))))))))))))))))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩))))))))))))))))))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩)))))))))))))))))))))))))))))))
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related450 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related450 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 14)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 14))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related450 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related450 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 481 = .split (19 : Fin 20) ![482,483,484,485] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1066786187787347 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_92282]
    apply StepRelated.split
    intro a
    fin_cases a
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩)))))))))))))))))))))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩))))))))))))))))))))))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩)))))))))))))))))))))))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩))))))))))))))))))))))))))))))))))))
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related450 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related450 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related450 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related450 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related450 1) .bound .bound
    exact .bound

theorem originalReceipt450 :
    check EJMGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 161444 cache450 partial450 = true := by
  exact checked_simulation pilotNodes EJMGlobalDAGData.nodes step lower
    EJMGlobalScoreSymmetry.dominates scale Related450 alignment450
    4 450 161444 cache450 partial450 (Or.inl (⟨rfl, rfl, rfl⟩))
    EJMGlobalSuffixProbeBlock35.receipt450

#print axioms originalReceipt450

private def Related449 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) : Prop :=
  (fuel = 4 ∧ left = 449 ∧ right = 493)

private theorem alignment449 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) (related : Related449 (fuel + 1) left right) :
    StepRelated (Related449 fuel) (pilotNodes (fuel + 1) left)
      (EJMGlobalDAGData.nodes (fuel + 1) right) := by
  rcases related with ⟨hf, hl, hr⟩
  have amount : fuel = 3 := by omega
  subst fuel left right
  change StepRelated (Related449 3) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12))
  exact .symmetry _

theorem originalReceipt449 :
    check EJMGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 493 cache449 partial449 = true := by
  exact checked_simulation pilotNodes EJMGlobalDAGData.nodes step lower
    EJMGlobalScoreSymmetry.dominates scale Related449 alignment449
    4 449 493 cache449 partial449 (⟨rfl, rfl, rfl⟩)
    EJMGlobalSuffixProbeBlock35.receipt449

#print axioms originalReceipt449

private def Related448 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) : Prop :=
  (fuel = 4 ∧ left = 448 ∧ right = 493)

private theorem alignment448 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) (related : Related448 (fuel + 1) left right) :
    StepRelated (Related448 fuel) (pilotNodes (fuel + 1) left)
      (EJMGlobalDAGData.nodes (fuel + 1) right) := by
  rcases related with ⟨hf, hl, hr⟩
  have amount : fuel = 3 := by omega
  subst fuel left right
  change StepRelated (Related448 3) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12))
  exact .symmetry _

theorem originalReceipt448 :
    check EJMGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 493 cache448 partial448 = true := by
  exact checked_simulation pilotNodes EJMGlobalDAGData.nodes step lower
    EJMGlobalScoreSymmetry.dominates scale Related448 alignment448
    4 448 493 cache448 partial448 (⟨rfl, rfl, rfl⟩)
    EJMGlobalSuffixProbeBlock35.receipt448

#print axioms originalReceipt448

end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixOriginalAlignmentBlock35
