/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixAlignmentShapesBlock5
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixAlignmentShapesBlock5
   mirror-E: none(waiver:actual-original-suffix-helper)
   anchors: []
   utility: none
   digest: Shared exact split shapes from the original EJM DAG are kernel checked for actual suffix consumers. -/

/- Prepared exact suffix alignment; compilation is still required. Every
cache, partial event, symmetry and gap is the original actual expression.
This is not acceptance of the complete original global certificate. -/

import D5.S3.Quantum.Entanglement.EJM.EJMGlobalDAGData
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData
import D5.S0.Certificates.FiniteCachedSymmetryDAGSimulation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 65536
set_option linter.style.longLine false

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock5
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (check)
open D5.S0.Certificates.FiniteCachedSymmetryDAGSimulation
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale)

theorem shape_4_161462 : EJMGlobalDAGData.nodes 4 161462 =
    .split (17 : Fin 20) ![494,494,108675,94568] := by
  change (.split (17 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 69301 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (17 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_3_108675 : EJMGlobalDAGData.nodes 3 108675 =
    .split (18 : Fin 20) ![92212,92170,92170,92170] := by
  change (.split (18 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 16514 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (18 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_3_94568 : EJMGlobalDAGData.nodes 3 94568 =
    .split (18 : Fin 20) ![92278,92278,92278,0] := by
  change (.split (18 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 2407 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (18 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_4_161463 : EJMGlobalDAGData.nodes 4 161463 =
    .split (17 : Fin 20) ![1950,113748,92277,105973] := by
  change (.split (17 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 69302 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (17 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_3_105973 : EJMGlobalDAGData.nodes 3 105973 =
    .split (18 : Fin 20) ![92278,92278,0,0] := by
  change (.split (18 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 13812 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (18 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_5_161468 : EJMGlobalDAGData.nodes 5 161468 =
    .split (16 : Fin 20) ![493,493,161467,113698] := by
  change (.split (16 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 69307 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (16 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_4_161467 : EJMGlobalDAGData.nodes 4 161467 =
    .split (17 : Fin 20) ![494,494,161465,161466] := by
  change (.split (17 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 69306 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (17 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_3_161465 : EJMGlobalDAGData.nodes 3 161465 =
    .split (18 : Fin 20) ![92336,94133,94133,94133] := by
  change (.split (18 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 69304 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (18 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_2_94133 : EJMGlobalDAGData.nodes 2 94133 =
    .split (19 : Fin 20) ![3374,3374,0,0] := by
  change (.split (19 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 1972 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (19 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_3_161466 : EJMGlobalDAGData.nodes 3 161466 =
    .split (18 : Fin 20) ![94133,94133,94133,94133] := by
  change (.split (18 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 69305 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (18 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_6_161476 : EJMGlobalDAGData.nodes 6 161476 =
    .split (15 : Fin 20) ![2894,2894,161472,161475] := by
  change (.split (15 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 69315 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (15 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_5_161472 : EJMGlobalDAGData.nodes 5 161472 =
    .split (16 : Fin 20) ![493,493,161470,161471] := by
  change (.split (16 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 69311 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (16 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_4_161470 : EJMGlobalDAGData.nodes 4 161470 =
    .split (17 : Fin 20) ![494,494,92553,105973] := by
  change (.split (17 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 69309 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (17 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_3_92553 : EJMGlobalDAGData.nodes 3 92553 =
    .split (18 : Fin 20) ![495,0,0,0] := by
  change (.split (18 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 392 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (18 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_4_161471 : EJMGlobalDAGData.nodes 4 161471 =
    .split (17 : Fin 20) ![1950,101532,92277,105973] := by
  change (.split (17 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 69310 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (17 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_3_101532 : EJMGlobalDAGData.nodes 3 101532 =
    .split (18 : Fin 20) ![1951,101524,0,0] := by
  change (.split (18 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 9371 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (18 : Fin 20))
  funext a
  fin_cases a <;> rfl

end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock5
