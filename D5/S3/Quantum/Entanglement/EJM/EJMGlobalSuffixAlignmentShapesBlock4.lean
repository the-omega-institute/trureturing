/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixAlignmentShapesBlock4
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixAlignmentShapesBlock4
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

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock4
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (check)
open D5.S0.Certificates.FiniteCachedSymmetryDAGSimulation
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale)

theorem shape_3_94683 : EJMGlobalDAGData.nodes 3 94683 =
    .split (18 : Fin 20) ![0,0,92278,92278] := by
  change (.split (18 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 2522 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (18 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_5_161456 : EJMGlobalDAGData.nodes 5 161456 =
    .split (16 : Fin 20) ![493,493,161454,161455] := by
  change (.split (16 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 69295 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (16 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_4_161454 : EJMGlobalDAGData.nodes 4 161454 =
    .split (17 : Fin 20) ![494,93293,113770,113711] := by
  change (.split (17 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 69293 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (17 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_3_93293 : EJMGlobalDAGData.nodes 3 93293 =
    .split (18 : Fin 20) ![495,495,495,92212] := by
  change (.split (18 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 1132 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (18 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_3_113770 : EJMGlobalDAGData.nodes 3 113770 =
    .split (18 : Fin 20) ![92399,92399,0,92282] := by
  change (.split (18 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 21609 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (18 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_3_113711 : EJMGlobalDAGData.nodes 3 113711 =
    .split (18 : Fin 20) ![92399,92399,92399,92282] := by
  change (.split (18 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 21550 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (18 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_4_161455 : EJMGlobalDAGData.nodes 4 161455 =
    .split (17 : Fin 20) ![1950,113680,113713,113542] := by
  change (.split (17 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 69294 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (17 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_3_113713 : EJMGlobalDAGData.nodes 3 113713 =
    .split (18 : Fin 20) ![0,0,0,113505] := by
  change (.split (18 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 21552 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (18 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_5_161459 : EJMGlobalDAGData.nodes 5 161459 =
    .split (16 : Fin 20) ![493,493,161457,161458] := by
  change (.split (16 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 69298 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (16 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_4_161457 : EJMGlobalDAGData.nodes 4 161457 =
    .split (17 : Fin 20) ![494,94691,92176,113711] := by
  change (.split (17 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 69296 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (17 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_3_94691 : EJMGlobalDAGData.nodes 3 94691 =
    .split (18 : Fin 20) ![495,495,495,92336] := by
  change (.split (18 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 2530 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (18 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_4_161458 : EJMGlobalDAGData.nodes 4 161458 =
    .split (17 : Fin 20) ![1950,113693,92176,113877] := by
  change (.split (17 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 69297 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (17 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_3_113877 : EJMGlobalDAGData.nodes 3 113877 =
    .split (18 : Fin 20) ![113681,113505,0,0] := by
  change (.split (18 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 21716 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (18 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_7_161490 : EJMGlobalDAGData.nodes 7 161490 =
    .split (14 : Fin 20) ![161469,161476,161482,161489] := by
  change (.split (14 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 69329 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (14 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_6_161469 : EJMGlobalDAGData.nodes 6 161469 =
    .split (15 : Fin 20) ![2894,2894,161464,161468] := by
  change (.split (15 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 69308 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (15 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_5_161464 : EJMGlobalDAGData.nodes 5 161464 =
    .split (16 : Fin 20) ![493,493,161462,161463] := by
  change (.split (16 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 69303 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (16 : Fin 20))
  funext a
  fin_cases a <;> rfl

end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock4
