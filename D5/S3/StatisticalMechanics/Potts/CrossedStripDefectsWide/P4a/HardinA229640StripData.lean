/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229640StripData
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229640StripData
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229640Strip.result; premises=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229640StripCertificate.finite_certificate
   digest: Exact two-defect extension of the four-row HDA transfer. -/

/-
admission_basis: open-problem-resolution (#31548; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229640Strip.result)
cl: proof_shape=bind-only; consumers=HardinA229640Strip.result
T: proof_shape=bind-only; consumers=HardinA229640Strip.result
initial: proof_shape=bind-only; consumers=HardinA229640Strip.result
terminal: proof_shape=bind-only; consumers=HardinA229640Strip.result
-/

import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P4a.HardinA229537StripData
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer
import Mathlib.Data.Matrix.Block

open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P4a.HardinA229640StripData
open D5.S3.Combinatorics.TraceAvoidingArrays
set_option backward.isDefEq.respectTransparency false

def cl (p : Fin 4 → Fin 3) (d : ℕ) : Fin 42 :=
  if d = 2 then (HardinA233177PairTransfer.cls (p 0,p 1,p 2,p 3)).castAdd 28
  else (HardinA229537StripData.cl p d).natAdd 14

def T : Matrix (Fin 42) (Fin 42) ℤ :=
  Matrix.reindex (finSumFinEquiv : Fin 14 ⊕ Fin 28 ≃ Fin 42)
    (finSumFinEquiv : Fin 14 ⊕ Fin 28 ≃ Fin 42)
    (Matrix.fromBlocks HardinA233177PairTransfer.Q
      (fun i : Fin 14 => Fin.append
        (HardinA229537StripData.T.submatrix (fun i : Fin 14 => i.castAdd 14)
          (fun j : Fin 14 => j.natAdd 14) i)
        ((![![0, 2, 0, 0, 2, 0, 0, 2, 0, 2, 4, 0, 2, 2],
    ![1, 1, 1, 1, 2, 1, 0, 1, 0, 2, 1, 1, 1, 1],
    ![0, 1, 2, 1, 2, 2, 1, 2, 1, 1, 0, 0, 1, 1],
    ![0, 1, 1, 1, 2, 1, 2, 1, 2, 1, 0, 1, 1, 2],
    ![1, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    ![0, 1, 2, 1, 1, 2, 1, 1, 1, 1, 0, 0, 2, 2],
    ![0, 0, 1, 2, 1, 1, 2, 1, 2, 0, 2, 1, 1, 1],
    ![1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    ![0, 0, 1, 2, 1, 1, 2, 1, 3, 0, 2, 0, 1, 1],
    ![1, 2, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 2],
    ![2, 1, 0, 0, 1, 0, 2, 1, 2, 1, 2, 1, 1, 1],
    ![0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1],
    ![1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1],
    ![1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2]]) i))
      0 HardinA229537StripData.T)

def initial (s : Fin 42) : ℤ :=
  ∑ r : Fin 4 → Fin 3, if cl r 2 = s then 1 else 0

def terminal : Fin 42 → ℤ :=
  Fin.append (0 : Fin 14 → ℤ) HardinA229537StripData.terminal

end D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P4a.HardinA229640StripData
