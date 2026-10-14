/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixAlignmentShapesBlock1
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixAlignmentShapesBlock1
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

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock1
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (check)
open D5.S0.Certificates.FiniteCachedSymmetryDAGSimulation
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale)

theorem shape_5_161436 : EJMGlobalDAGData.nodes 5 161436 =
    .split (16 : Fin 20) ![493,493,161434,161435] := by
  change (.split (16 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 69275 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (16 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_4_161434 : EJMGlobalDAGData.nodes 4 161434 =
    .split (17 : Fin 20) ![494,113677,108651,108651] := by
  change (.split (17 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 69273 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (17 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_3_113677 : EJMGlobalDAGData.nodes 3 113677 =
    .split (18 : Fin 20) ![495,92212,0,92282] := by
  change (.split (18 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 21516 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (18 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_2_92212 : EJMGlobalDAGData.nodes 2 92212 =
    .split (19 : Fin 20) ![496,496,0,0] := by
  change (.split (19 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 51 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (19 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_2_92282 : EJMGlobalDAGData.nodes 2 92282 =
    .split (19 : Fin 20) ![3374,0,0,0] := by
  change (.split (19 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 121 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (19 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_3_108651 : EJMGlobalDAGData.nodes 3 108651 =
    .split (18 : Fin 20) ![92399,92282,92282,92282] := by
  change (.split (18 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 16490 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (18 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_2_92399 : EJMGlobalDAGData.nodes 2 92399 =
    .split (19 : Fin 20) ![3374,3375,0,0] := by
  change (.split (19 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 238 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (19 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_4_161435 : EJMGlobalDAGData.nodes 4 161435 =
    .split (17 : Fin 20) ![1950,113680,113682,113682] := by
  change (.split (17 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 69274 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (17 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_3_113680 : EJMGlobalDAGData.nodes 3 113680 =
    .split (18 : Fin 20) ![1951,101524,0,113505] := by
  change (.split (18 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 21519 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (18 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_2_113505 : EJMGlobalDAGData.nodes 2 113505 =
    .split (19 : Fin 20) ![4830,0,0,0] := by
  change (.split (19 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 21344 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (19 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_3_113682 : EJMGlobalDAGData.nodes 3 113682 =
    .split (18 : Fin 20) ![113681,113505,113505,113505] := by
  change (.split (18 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 21521 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (18 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_2_113681 : EJMGlobalDAGData.nodes 2 113681 =
    .split (19 : Fin 20) ![4830,4831,0,0] := by
  change (.split (19 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 21520 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (19 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_5_161440 : EJMGlobalDAGData.nodes 5 161440 =
    .split (16 : Fin 20) ![493,493,161439,113698] := by
  change (.split (16 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 69279 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (16 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_4_161439 : EJMGlobalDAGData.nodes 4 161439 =
    .split (17 : Fin 20) ![494,161437,161438,108651] := by
  change (.split (17 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 69278 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (17 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_3_161437 : EJMGlobalDAGData.nodes 3 161437 =
    .split (18 : Fin 20) ![495,92336,92282,92282] := by
  change (.split (18 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 69276 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (18 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_2_92336 : EJMGlobalDAGData.nodes 2 92336 =
    .split (19 : Fin 20) ![496,496,496,0] := by
  change (.split (19 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 175 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (19 : Fin 20))
  funext a
  fin_cases a <;> rfl

end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock1
