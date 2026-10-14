/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixOriginalAlignmentBlock21
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixOriginalAlignmentBlock21
   mirror-E: none(waiver:actual-original-suffix-helper)
   anchors: []
   utility: none
   digest: Checked finite simulation transports full frontier subtrees to the original DAG, preserving actual caches and partial events. -/

/- Prepared exact suffix alignment; compilation is still required. Every
cache, partial event, symmetry and gap is the original actual expression.
This is not acceptance of the complete original global certificate. -/

import D5.S3.Quantum.Entanglement.EJM.EJMGlobalDAGData
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock21
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock0
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock5
import D5.S0.Certificates.FiniteCachedSymmetryDAGSimulation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 65536
set_option linter.style.longLine false

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixOriginalAlignmentBlock21
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (check)
open D5.S0.Certificates.FiniteCachedSymmetryDAGSimulation
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale)

private def Related1091 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) : Prop :=
  (fuel = 4 ∧ left = 1091 ∧ right = 161471) ∨
  (fuel = 3 ∧ left = 1092 ∧ right = 1950) ∨
  (fuel = 3 ∧ left = 1093 ∧ right = 101532) ∨
  (fuel = 2 ∧ left = 1094 ∧ right = 1951) ∨
  (fuel = 2 ∧ left = 1095 ∧ right = 101524) ∨
  (fuel = 1 ∧ left = 1096 ∧ right = 1952) ∨
  (fuel = 1 ∧ left = 1097 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 1098 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 1099 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 1100 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 1101 ∧ right = 0) ∨
  (fuel = 3 ∧ left = 1102 ∧ right = 92277) ∨
  (fuel = 2 ∧ left = 1103 ∧ right = 92170) ∨
  (fuel = 1 ∧ left = 1104 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 1105 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 1106 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 1107 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 1108 ∧ right = 92170) ∨
  (fuel = 1 ∧ left = 1109 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 1110 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 1111 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 1112 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 1113 ∧ right = 92170) ∨
  (fuel = 1 ∧ left = 1114 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 1115 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 1116 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 1117 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 1118 ∧ right = 92170) ∨
  (fuel = 1 ∧ left = 1119 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 1120 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 1121 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 1122 ∧ right = 0) ∨
  (fuel = 3 ∧ left = 1123 ∧ right = 105973) ∨
  (fuel = 2 ∧ left = 1124 ∧ right = 92278) ∨
  (fuel = 1 ∧ left = 1125 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 1126 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 1127 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 1128 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 1129 ∧ right = 92278) ∨
  (fuel = 1 ∧ left = 1130 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 1131 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 1132 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 1133 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 1134 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 1135 ∧ right = 0)

private theorem alignment1091 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) (related : Related1091 (fuel + 1) left right) :
    StepRelated (Related1091 fuel) (pilotNodes (fuel + 1) left)
      (EJMGlobalDAGData.nodes (fuel + 1) right) := by
  rcases related with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 3 := by omega
    subst fuel left right
    have leftShape : pilotNodes 4 1091 = .split (17 : Fin 20) ![1092,1093,1102,1123] := by
      change (.split (17 : Fin 20)
        (fun a => ⟨(2470094891026577 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock5.shape_4_161471]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1091 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    change StepRelated (Related1091 2) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 97 9)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 97 9))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    have leftShape : pilotNodes 3 1093 = .split (18 : Fin 20) ![1094,1095,1100,1101] := by
      change (.split (18 : Fin 20)
        (fun a => ⟨(2421715305924818 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock5.shape_3_101532]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1091 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related1091 1) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 97 10)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 97 10))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 1095 = .split (19 : Fin 20) ![1096,1097,1098,1099] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2417316185934099 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock0.shape_2_101524]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1091 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1091 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 97 11)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 97 11))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1091 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1091 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1091 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related1091 1) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related1091 1) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    have leftShape : pilotNodes 3 1102 = .split (18 : Fin 20) ![1103,1108,1113,1118] := by
      change (.split (18 : Fin 20)
        (fun a => ⟨(2459105682295282 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock0.shape_3_92277]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1091 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 1103 = .split (19 : Fin 20) ![1104,1105,1106,1107] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2434912667994643 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock0.shape_2_92170]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1091 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1091 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1091 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1091 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1091 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 1108 = .split (19 : Fin 20) ![1109,1110,1111,1112] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2445910469282483 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock0.shape_2_92170]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1091 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1091 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1091 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1091 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1091 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 1113 = .split (19 : Fin 20) ![1114,1115,1116,1117] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2456908270570323 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock0.shape_2_92170]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1091 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1091 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1091 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1091 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1091 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 1118 = .split (19 : Fin 20) ![1119,1120,1121,1122] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2467906071858163 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock0.shape_2_92170]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1091 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1091 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1091 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1091 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1091 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    have leftShape : pilotNodes 3 1123 = .split (18 : Fin 20) ![1124,1129,1134,1135] := by
      change (.split (18 : Fin 20)
        (fun a => ⟨(2496500354682002 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock5.shape_3_105973]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1091 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 1124 = .split (19 : Fin 20) ![1125,1126,1127,1128] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2481103433403571 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock0.shape_2_92278]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1091 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1091 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1091 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1091 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1091 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 1129 = .split (19 : Fin 20) ![1130,1131,1132,1133] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2492101234691411 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock0.shape_2_92278]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1091 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1091 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1091 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1091 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1091 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related1091 1) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related1091 1) .bound .bound
    exact .bound

theorem originalReceipt1091 :
    check EJMGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 161471 cache1091 partial1091 = true := by
  exact checked_simulation pilotNodes EJMGlobalDAGData.nodes step lower
    EJMGlobalScoreSymmetry.dominates scale Related1091 alignment1091
    4 1091 161471 cache1091 partial1091 (by unfold Related1091; decide +kernel)
    EJMGlobalSuffixProbeBlock21.receipt1091

#print axioms originalReceipt1091

end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixOriginalAlignmentBlock21
