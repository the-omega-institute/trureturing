/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixAlignmentShapesBlock12
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixAlignmentShapesBlock12
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

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock12
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (check)
open D5.S0.Certificates.FiniteCachedSymmetryDAGSimulation
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale)

theorem shape_3_95288 : EJMGlobalDAGData.nodes 3 95288 =
    .split (18 : Fin 20) ![495,495,92212,92170] := by
  change (.split (18 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 3127 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (18 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_5_161535 : EJMGlobalDAGData.nodes 5 161535 =
    .split (16 : Fin 20) ![493,493,493,161534] := by
  change (.split (16 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 69374 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (16 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_4_161534 : EJMGlobalDAGData.nodes 4 161534 =
    .split (17 : Fin 20) ![494,494,95301,129049] := by
  change (.split (17 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 69373 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (17 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_6_161537 : EJMGlobalDAGData.nodes 6 161537 =
    .split (15 : Fin 20) ![2894,2894,114048,100037] := by
  change (.split (15 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 69376 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (15 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_5_114048 : EJMGlobalDAGData.nodes 5 114048 =
    .split (16 : Fin 20) ![493,493,493,93294] := by
  change (.split (16 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 21887 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (16 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_4_93294 : EJMGlobalDAGData.nodes 4 93294 =
    .split (17 : Fin 20) ![494,494,93293,92176] := by
  change (.split (17 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 1133 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (17 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_5_100037 : EJMGlobalDAGData.nodes 5 100037 =
    .split (16 : Fin 20) ![493,493,493,100036] := by
  change (.split (16 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 7876 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (16 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_4_100036 : EJMGlobalDAGData.nodes 4 100036 =
    .split (17 : Fin 20) ![494,494,94691,92176] := by
  change (.split (17 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 7875 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (17 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_7_156431 : EJMGlobalDAGData.nodes 7 156431 =
    .split (14 : Fin 20) ![156430,107660,94964,94965] := by
  change (.split (14 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 64270 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (14 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_6_156430 : EJMGlobalDAGData.nodes 6 156430 =
    .split (15 : Fin 20) ![2894,2894,2894,156429] := by
  change (.split (15 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 64269 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (15 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_5_156429 : EJMGlobalDAGData.nodes 5 156429 =
    .split (16 : Fin 20) ![493,493,493,156294] := by
  change (.split (16 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 64268 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (16 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_4_156294 : EJMGlobalDAGData.nodes 4 156294 =
    .split (17 : Fin 20) ![494,494,494,156293] := by
  change (.split (17 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 64133 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (17 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_3_156293 : EJMGlobalDAGData.nodes 3 156293 =
    .split (18 : Fin 20) ![92336,92278,92278,0] := by
  change (.split (18 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 64132 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (18 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_6_107660 : EJMGlobalDAGData.nodes 6 107660 =
    .split (15 : Fin 20) ![2894,2894,2894,94546] := by
  change (.split (15 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 15499 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (15 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_5_94546 : EJMGlobalDAGData.nodes 5 94546 =
    .split (16 : Fin 20) ![493,493,493,93149] := by
  change (.split (16 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 2385 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (16 : Fin 20))
  funext a
  fin_cases a <;> rfl

theorem shape_4_93149 : EJMGlobalDAGData.nodes 4 93149 =
    .split (17 : Fin 20) ![494,494,494,92553] := by
  change (.split (17 : Fin 20)
    (fun a => ⟨(EJMGlobalDAGData.shapeWord 988 /
      2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
      Nat.mod_lt _ (by decide)⟩) :
      Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
  apply congrArg (Node.split (17 : Fin 20))
  funext a
  fin_cases a <;> rfl

end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock12
