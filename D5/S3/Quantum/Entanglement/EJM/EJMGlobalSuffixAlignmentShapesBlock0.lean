/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixAlignmentShapesBlock0
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixAlignmentShapesBlock0
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

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock0
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (check)
open D5.S0.Certificates.FiniteCachedSymmetryDAGSimulation
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale)

theorem shape_9_161540 : EJMGlobalDAGData.nodes 9 161540 =
    .split (12 : Fin 20) ![969,969,161502,161539] := by
  change (.split (12 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 69379 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (12 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_8_161502 : EJMGlobalDAGData.nodes 8 161502 =
    .split (13 : Fin 20) ![970,161461,161490,161501] := by
  change (.split (13 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 69341 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (13 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_7_161461 : EJMGlobalDAGData.nodes 7 161461 =
    .split (14 : Fin 20) ![971,161441,161450,161460] := by
  change (.split (14 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 69300 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (14 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_6_161441 : EJMGlobalDAGData.nodes 6 161441 =
    .split (15 : Fin 20) ![972,113676,161436,161440] := by
  change (.split (15 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 69280 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (15 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_5_113676 : EJMGlobalDAGData.nodes 5 113676 =
    .split (16 : Fin 20) ![493,493,107347,113675] := by
  change (.split (16 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 21515 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (16 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_4_107347 : EJMGlobalDAGData.nodes 4 107347 =
    .split (17 : Fin 20) ![494,106150,92277,92279] := by
  change (.split (17 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 15186 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (17 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_3_106150 : EJMGlobalDAGData.nodes 3 106150 =
    .split (18 : Fin 20) ![495,92568,92236,92236] := by
  change (.split (18 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 13989 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (18 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_2_92568 : EJMGlobalDAGData.nodes 2 92568 =
    .split (19 : Fin 20) ![496,0,0,0] := by
  change (.split (19 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 407 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (19 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_2_92236 : EJMGlobalDAGData.nodes 2 92236 =
    .split (19 : Fin 20) ![2898,0,0,0] := by
  change (.split (19 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 75 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (19 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_3_92277 : EJMGlobalDAGData.nodes 3 92277 =
    .split (18 : Fin 20) ![92170,92170,92170,92170] := by
  change (.split (18 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 116 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (18 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_2_92170 : EJMGlobalDAGData.nodes 2 92170 =
    .split (19 : Fin 20) ![2898,2898,0,0] := by
  change (.split (19 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 9 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (19 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_3_92279 : EJMGlobalDAGData.nodes 3 92279 =
    .split (18 : Fin 20) ![92278,92278,92278,92278] := by
  change (.split (18 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 118 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (18 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_2_92278 : EJMGlobalDAGData.nodes 2 92278 =
    .split (19 : Fin 20) ![2898,2898,2898,0] := by
  change (.split (19 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 117 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (19 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_4_113675 : EJMGlobalDAGData.nodes 4 113675 =
    .split (17 : Fin 20) ![1950,113674,92277,92279] := by
  change (.split (17 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 21514 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (17 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_3_113674 : EJMGlobalDAGData.nodes 3 113674 =
    .split (18 : Fin 20) ![1951,101524,92236,92236] := by
  change (.split (18 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 21513 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (18 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_2_101524 : EJMGlobalDAGData.nodes 2 101524 =
    .split (19 : Fin 20) ![1952,0,0,0] := by
  change (.split (19 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 9363 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (19 : Fin 20))
  funext a
  fin_cases a <;> rfl

end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock0
