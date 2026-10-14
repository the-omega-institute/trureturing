/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixAlignmentShapesBlock3
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixAlignmentShapesBlock3
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

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock3
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (check)
open D5.S0.Certificates.FiniteCachedSymmetryDAGSimulation
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale)

theorem shape_4_161445 : EJMGlobalDAGData.nodes 4 161445 =
    .split (17 : Fin 20) ![1950,113693,92176,114004] := by
  change (.split (17 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 69284 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (17 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_3_114004 : EJMGlobalDAGData.nodes 3 114004 =
    .split (18 : Fin 20) ![113681,113505,113505,0] := by
  change (.split (18 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 21843 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (18 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_5_161449 : EJMGlobalDAGData.nodes 5 161449 =
    .split (16 : Fin 20) ![493,493,161447,161448] := by
  change (.split (16 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 69288 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (16 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_4_161447 : EJMGlobalDAGData.nodes 4 161447 =
    .split (17 : Fin 20) ![494,94678,92176,113696] := by
  change (.split (17 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 69286 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (17 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_3_94678 : EJMGlobalDAGData.nodes 3 94678 =
    .split (18 : Fin 20) ![495,495,92336,92282] := by
  change (.split (18 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 2517 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (18 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_3_113696 : EJMGlobalDAGData.nodes 3 113696 =
    .split (18 : Fin 20) ![92399,92399,92282,92282] := by
  change (.split (18 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 21535 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (18 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_4_161448 : EJMGlobalDAGData.nodes 4 161448 =
    .split (17 : Fin 20) ![1950,113693,113542,113682] := by
  change (.split (17 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 69287 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (17 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_3_113542 : EJMGlobalDAGData.nodes 3 113542 =
    .split (18 : Fin 20) ![0,113505,0,113505] := by
  change (.split (18 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 21381 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (18 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_6_161460 : EJMGlobalDAGData.nodes 6 161460 =
    .split (15 : Fin 20) ![2894,161453,161456,161459] := by
  change (.split (15 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 69299 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (15 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_5_161453 : EJMGlobalDAGData.nodes 5 161453 =
    .split (16 : Fin 20) ![493,493,161451,161452] := by
  change (.split (16 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 69292 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (16 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_4_161451 : EJMGlobalDAGData.nodes 4 161451 =
    .split (17 : Fin 20) ![494,92687,106028,94666] := by
  change (.split (17 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 69290 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (17 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_3_92687 : EJMGlobalDAGData.nodes 3 92687 =
    .split (18 : Fin 20) ![495,495,495,0] := by
  change (.split (18 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 526 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (18 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_3_106028 : EJMGlobalDAGData.nodes 3 106028 =
    .split (18 : Fin 20) ![0,0,92170,0] := by
  change (.split (18 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 13867 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (18 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_3_94666 : EJMGlobalDAGData.nodes 3 94666 =
    .split (18 : Fin 20) ![0,92278,92278,0] := by
  change (.split (18 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 2505 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (18 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_4_161452 : EJMGlobalDAGData.nodes 4 161452 =
    .split (17 : Fin 20) ![1950,113748,92176,94683] := by
  change (.split (17 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 69291 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (17 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_3_113748 : EJMGlobalDAGData.nodes 3 113748 =
    .split (18 : Fin 20) ![1951,101524,0,92236] := by
  change (.split (18 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 21587 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (18 : Fin 20))
  funext a
  fin_cases a <;> rfl

end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock3
