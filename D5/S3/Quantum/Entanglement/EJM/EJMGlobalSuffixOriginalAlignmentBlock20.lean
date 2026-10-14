/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixOriginalAlignmentBlock20
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixOriginalAlignmentBlock20
   mirror-E: none(waiver:actual-original-suffix-helper)
   anchors: []
   utility: none
   digest: Checked finite simulation transports full frontier subtrees to the original DAG, preserving actual caches and partial events. -/

/- Prepared exact suffix alignment; compilation is still required. Every
cache, partial event, symmetry and gap is the original actual expression.
This is not acceptance of the complete original global certificate. -/

import D5.S3.Quantum.Entanglement.EJM.EJMGlobalDAGData
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock20
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock1
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock5
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock6
import D5.S0.Certificates.FiniteCachedSymmetryDAGSimulation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 65536
set_option linter.style.longLine false

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixOriginalAlignmentBlock20
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (check)
open D5.S0.Certificates.FiniteCachedSymmetryDAGSimulation
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale)

private def Related1139 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) : Prop :=
  (fuel = 4 ∧ left = 1139 ∧ right = 161473) ∨
  (fuel = 3 ∧ left = 1140 ∧ right = 494) ∨
  (fuel = 3 ∧ left = 1141 ∧ right = 494) ∨
  (fuel = 3 ∧ left = 1142 ∧ right = 108856) ∨
  (fuel = 2 ∧ left = 1143 ∧ right = 495) ∨
  (fuel = 2 ∧ left = 1144 ∧ right = 92336) ∨
  (fuel = 1 ∧ left = 1145 ∧ right = 496) ∨
  (fuel = 1 ∧ left = 1146 ∧ right = 496) ∨
  (fuel = 1 ∧ left = 1147 ∧ right = 496) ∨
  (fuel = 1 ∧ left = 1148 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 1149 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 1150 ∧ right = 94133) ∨
  (fuel = 1 ∧ left = 1151 ∧ right = 3374) ∨
  (fuel = 1 ∧ left = 1152 ∧ right = 3374) ∨
  (fuel = 1 ∧ left = 1153 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 1154 ∧ right = 0) ∨
  (fuel = 3 ∧ left = 1155 ∧ right = 129088) ∨
  (fuel = 2 ∧ left = 1156 ∧ right = 94132) ∨
  (fuel = 1 ∧ left = 1157 ∧ right = 3374) ∨
  (fuel = 1 ∧ left = 1158 ∧ right = 3374) ∨
  (fuel = 1 ∧ left = 1159 ∧ right = 3375) ∨
  (fuel = 1 ∧ left = 1160 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 1161 ∧ right = 94133) ∨
  (fuel = 1 ∧ left = 1162 ∧ right = 3374) ∨
  (fuel = 1 ∧ left = 1163 ∧ right = 3374) ∨
  (fuel = 1 ∧ left = 1164 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 1165 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 1166 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 1167 ∧ right = 0)

private theorem alignment1139 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) (related : Related1139 (fuel + 1) left right) :
    StepRelated (Related1139 fuel) (pilotNodes (fuel + 1) left)
      (EJMGlobalDAGData.nodes (fuel + 1) right) := by
  rcases related with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 3 := by omega
    subst fuel left right
    have leftShape : pilotNodes 4 1139 = .split (17 : Fin 20) ![1140,1141,1142,1155] := by
      change (.split (17 : Fin 20)
        (fun a => ⟨(2540485116333713 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock6.shape_4_161473]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1139 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    change StepRelated (Related1139 2) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    change StepRelated (Related1139 2) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    have leftShape : pilotNodes 3 1142 = .split (18 : Fin 20) ![1143,1144,1149,1150] := by
      change (.split (18 : Fin 20)
        (fun a => ⟨(2529493758545650 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock6.shape_3_108856]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1139 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related1139 1) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 14)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 14))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 1144 = .split (19 : Fin 20) ![1145,1146,1147,1148] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2525094638554931 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_92336]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1139 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1139 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1139 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1139 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1139 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related1139 1) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 1150 = .split (19 : Fin 20) ![1151,1152,1153,1154] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2538292000100339 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock5.shape_2_94133]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1139 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1139 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1139 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1139 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1139 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    have leftShape : pilotNodes 3 1155 = .split (18 : Fin 20) ![1156,1161,1166,1167] := by
      change (.split (18 : Fin 20)
        (fun a => ⟨(2566886282924178 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock6.shape_3_129088]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1139 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 1156 = .split (19 : Fin 20) ![1157,1158,1159,1160] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2551489361645747 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock6.shape_2_94132]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1139 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1139 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1139 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1139 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 14)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 14))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1139 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 1161 = .split (19 : Fin 20) ![1162,1163,1164,1165] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2562487162933587 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock5.shape_2_94133]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1139 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1139 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1139 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1139 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1139 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related1139 1) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related1139 1) .bound .bound
    exact .bound

theorem originalReceipt1139 :
    check EJMGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 161473 cache1139 partial1139 = true := by
  exact checked_simulation pilotNodes EJMGlobalDAGData.nodes step lower
    EJMGlobalScoreSymmetry.dominates scale Related1139 alignment1139
    4 1139 161473 cache1139 partial1139 (by unfold Related1139; decide +kernel)
    EJMGlobalSuffixProbeBlock20.receipt1139

#print axioms originalReceipt1139

private def Related1138 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) : Prop :=
  (fuel = 4 ∧ left = 1138 ∧ right = 493)

private theorem alignment1138 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) (related : Related1138 (fuel + 1) left right) :
    StepRelated (Related1138 fuel) (pilotNodes (fuel + 1) left)
      (EJMGlobalDAGData.nodes (fuel + 1) right) := by
  rcases related with ⟨hf, hl, hr⟩
  have amount : fuel = 3 := by omega
  subst fuel left right
  change StepRelated (Related1138 3) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12))
  exact .symmetry _

theorem originalReceipt1138 :
    check EJMGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 493 cache1138 partial1138 = true := by
  exact checked_simulation pilotNodes EJMGlobalDAGData.nodes step lower
    EJMGlobalScoreSymmetry.dominates scale Related1138 alignment1138
    4 1138 493 cache1138 partial1138 (by unfold Related1138; decide +kernel)
    EJMGlobalSuffixProbeBlock20.receipt1138

#print axioms originalReceipt1138

private def Related1137 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) : Prop :=
  (fuel = 4 ∧ left = 1137 ∧ right = 493)

private theorem alignment1137 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) (related : Related1137 (fuel + 1) left right) :
    StepRelated (Related1137 fuel) (pilotNodes (fuel + 1) left)
      (EJMGlobalDAGData.nodes (fuel + 1) right) := by
  rcases related with ⟨hf, hl, hr⟩
  have amount : fuel = 3 := by omega
  subst fuel left right
  change StepRelated (Related1137 3) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12))
  exact .symmetry _

theorem originalReceipt1137 :
    check EJMGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 493 cache1137 partial1137 = true := by
  exact checked_simulation pilotNodes EJMGlobalDAGData.nodes step lower
    EJMGlobalScoreSymmetry.dominates scale Related1137 alignment1137
    4 1137 493 cache1137 partial1137 (by unfold Related1137; decide +kernel)
    EJMGlobalSuffixProbeBlock20.receipt1137

#print axioms originalReceipt1137

end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixOriginalAlignmentBlock20
