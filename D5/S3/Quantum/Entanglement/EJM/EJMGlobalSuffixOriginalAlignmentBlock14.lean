/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixOriginalAlignmentBlock14
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixOriginalAlignmentBlock14
   mirror-E: none(waiver:actual-original-suffix-helper)
   anchors: []
   utility: none
   digest: Checked finite simulation transports full frontier subtrees to the original DAG, preserving actual caches and partial events. -/

/- Prepared exact suffix alignment; compilation is still required. Every
cache, partial event, symmetry and gap is the original actual expression.
This is not acceptance of the complete original global certificate. -/

import D5.S3.Quantum.Entanglement.EJM.EJMGlobalDAGData
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock14
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock0
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock1
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock4
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock5
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock7
import D5.S0.Certificates.FiniteCachedSymmetryDAGSimulation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 65536
set_option linter.style.longLine false

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixOriginalAlignmentBlock14
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (check)
open D5.S0.Certificates.FiniteCachedSymmetryDAGSimulation
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale)

private def Related1376 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) : Prop :=
  (fuel = 4 ∧ left = 1376 ∧ right = 161483) ∨
  (fuel = 3 ∧ left = 1377 ∧ right = 494) ∨
  (fuel = 3 ∧ left = 1378 ∧ right = 494) ∨
  (fuel = 3 ∧ left = 1379 ∧ right = 93293) ∨
  (fuel = 2 ∧ left = 1380 ∧ right = 495) ∨
  (fuel = 2 ∧ left = 1381 ∧ right = 495) ∨
  (fuel = 2 ∧ left = 1382 ∧ right = 495) ∨
  (fuel = 2 ∧ left = 1383 ∧ right = 92212) ∨
  (fuel = 1 ∧ left = 1384 ∧ right = 496) ∨
  (fuel = 1 ∧ left = 1385 ∧ right = 496) ∨
  (fuel = 1 ∧ left = 1386 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 1387 ∧ right = 0) ∨
  (fuel = 3 ∧ left = 1388 ∧ right = 105973) ∨
  (fuel = 2 ∧ left = 1389 ∧ right = 92278) ∨
  (fuel = 1 ∧ left = 1390 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 1391 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 1392 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 1393 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 1394 ∧ right = 92278) ∨
  (fuel = 1 ∧ left = 1395 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 1396 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 1397 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 1398 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 1399 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 1400 ∧ right = 0)

private theorem alignment1376 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) (related : Related1376 (fuel + 1) left right) :
    StepRelated (Related1376 fuel) (pilotNodes (fuel + 1) left)
      (EJMGlobalDAGData.nodes (fuel + 1) right) := by
  rcases related with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 3 := by omega
    subst fuel left right
    have leftShape : pilotNodes 4 1376 = .split (17 : Fin 20) ![1377,1378,1379,1388] := by
      change (.split (17 : Fin 20)
        (fun a => ⟨(3052984804355121 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock7.shape_4_161483]
    apply StepRelated.split
    intro a
    fin_cases a
    · exact Or.inr (Or.inl (⟨rfl, rfl, rfl⟩))
    · exact Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩)))))))))))))
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    change StepRelated (Related1376 2) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    change StepRelated (Related1376 2) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    have leftShape : pilotNodes 3 1379 = .split (18 : Fin 20) ![1380,1381,1382,1383] := by
      change (.split (18 : Fin 20)
        (fun a => ⟨(3041991299083410 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock4.shape_3_93293]
    apply StepRelated.split
    intro a
    fin_cases a
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩))))))))
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related1376 1) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 14)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 14))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related1376 1) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 14)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 14))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related1376 1) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 14)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 14))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 1383 = .split (19 : Fin 20) ![1384,1385,1386,1387] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3050789540113683 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_92212]
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
    change StepRelated (Related1376 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1376 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1376 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1376 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    have leftShape : pilotNodes 3 1388 = .split (18 : Fin 20) ![1389,1394,1399,1400] := by
      change (.split (18 : Fin 20)
        (fun a => ⟨(3079383822937522 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock5.shape_3_105973]
    apply StepRelated.split
    intro a
    fin_cases a
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩)))))))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩))))))))))))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨rfl, rfl, rfl⟩))))))))))))))))))))))))
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 1389 = .split (19 : Fin 20) ![1390,1391,1392,1393] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3063986901659091 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock0.shape_2_92278]
    apply StepRelated.split
    intro a
    fin_cases a
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩)))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩))))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩)))))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩))))))))))))))))))
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1376 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1376 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1376 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1376 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 1394 = .split (19 : Fin 20) ![1395,1396,1397,1398] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(3074984702946931 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock0.shape_2_92278]
    apply StepRelated.split
    intro a
    fin_cases a
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩))))))))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩)))))))))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩))))))))))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, rfl⟩)))))))))))))))))))))))
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1376 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1376 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1376 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1376 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related1376 1) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related1376 1) .bound .bound
    exact .bound

theorem originalReceipt1376 :
    check EJMGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 161483 cache1376 partial1376 = true := by
  exact checked_simulation pilotNodes EJMGlobalDAGData.nodes step lower
    EJMGlobalScoreSymmetry.dominates scale Related1376 alignment1376
    4 1376 161483 cache1376 partial1376 (Or.inl (⟨rfl, rfl, rfl⟩))
    EJMGlobalSuffixProbeBlock14.receipt1376

#print axioms originalReceipt1376

private def Related1375 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) : Prop :=
  (fuel = 4 ∧ left = 1375 ∧ right = 493)

private theorem alignment1375 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) (related : Related1375 (fuel + 1) left right) :
    StepRelated (Related1375 fuel) (pilotNodes (fuel + 1) left)
      (EJMGlobalDAGData.nodes (fuel + 1) right) := by
  rcases related with ⟨hf, hl, hr⟩
  have amount : fuel = 3 := by omega
  subst fuel left right
  change StepRelated (Related1375 3) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12))
  exact .symmetry _

theorem originalReceipt1375 :
    check EJMGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 493 cache1375 partial1375 = true := by
  exact checked_simulation pilotNodes EJMGlobalDAGData.nodes step lower
    EJMGlobalScoreSymmetry.dominates scale Related1375 alignment1375
    4 1375 493 cache1375 partial1375 (⟨rfl, rfl, rfl⟩)
    EJMGlobalSuffixProbeBlock14.receipt1375

#print axioms originalReceipt1375

private def Related1374 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) : Prop :=
  (fuel = 4 ∧ left = 1374 ∧ right = 493)

private theorem alignment1374 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) (related : Related1374 (fuel + 1) left right) :
    StepRelated (Related1374 fuel) (pilotNodes (fuel + 1) left)
      (EJMGlobalDAGData.nodes (fuel + 1) right) := by
  rcases related with ⟨hf, hl, hr⟩
  have amount : fuel = 3 := by omega
  subst fuel left right
  change StepRelated (Related1374 3) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12))
  exact .symmetry _

theorem originalReceipt1374 :
    check EJMGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 493 cache1374 partial1374 = true := by
  exact checked_simulation pilotNodes EJMGlobalDAGData.nodes step lower
    EJMGlobalScoreSymmetry.dominates scale Related1374 alignment1374
    4 1374 493 cache1374 partial1374 (⟨rfl, rfl, rfl⟩)
    EJMGlobalSuffixProbeBlock14.receipt1374

#print axioms originalReceipt1374

private def Related1372 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) : Prop :=
  (fuel = 5 ∧ left = 1372 ∧ right = 2894)

private theorem alignment1372 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) (related : Related1372 (fuel + 1) left right) :
    StepRelated (Related1372 fuel) (pilotNodes (fuel + 1) left)
      (EJMGlobalDAGData.nodes (fuel + 1) right) := by
  rcases related with ⟨hf, hl, hr⟩
  have amount : fuel = 4 := by omega
  subst fuel left right
  change StepRelated (Related1372 4) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 13))
  exact .symmetry _

theorem originalReceipt1372 :
    check EJMGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 2894 cache1372 partial1372 = true := by
  exact checked_simulation pilotNodes EJMGlobalDAGData.nodes step lower
    EJMGlobalScoreSymmetry.dominates scale Related1372 alignment1372
    5 1372 2894 cache1372 partial1372 (⟨rfl, rfl, rfl⟩)
    EJMGlobalSuffixProbeBlock14.receipt1372

#print axioms originalReceipt1372

private def Related1371 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) : Prop :=
  (fuel = 5 ∧ left = 1371 ∧ right = 2894)

private theorem alignment1371 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) (related : Related1371 (fuel + 1) left right) :
    StepRelated (Related1371 fuel) (pilotNodes (fuel + 1) left)
      (EJMGlobalDAGData.nodes (fuel + 1) right) := by
  rcases related with ⟨hf, hl, hr⟩
  have amount : fuel = 4 := by omega
  subst fuel left right
  change StepRelated (Related1371 4) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 13))
  exact .symmetry _

theorem originalReceipt1371 :
    check EJMGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 2894 cache1371 partial1371 = true := by
  exact checked_simulation pilotNodes EJMGlobalDAGData.nodes step lower
    EJMGlobalScoreSymmetry.dominates scale Related1371 alignment1371
    5 1371 2894 cache1371 partial1371 (⟨rfl, rfl, rfl⟩)
    EJMGlobalSuffixProbeBlock14.receipt1371

#print axioms originalReceipt1371

end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixOriginalAlignmentBlock14
