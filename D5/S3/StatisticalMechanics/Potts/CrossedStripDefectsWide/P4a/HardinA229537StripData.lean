/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229537StripData
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229537StripData
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229537Strip.result; premises=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229537StripCertificate.finite_certificate
   digest: Exact defect sectors of the four-row HDA transfer. -/

/-
admission_basis: open-problem-resolution (#31548; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229537Strip.result)
horizontal: proof_shape=bind-only; consumers=HardinA229537Strip.result
between: proof_shape=bind-only; consumers=HardinA229537Strip.result
cl: proof_shape=bind-only; consumers=HardinA229537Strip.result
T: proof_shape=bind-only; consumers=HardinA229537Strip.result
initial: proof_shape=bind-only; consumers=HardinA229537Strip.result
terminal: proof_shape=bind-only; consumers=HardinA229537Strip.result
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229589StripData
import Mathlib.Data.Matrix.Block

open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P4a.HardinA229537StripData
open D5.S3.Combinatorics.TraceAvoidingArrays
open D5.S3.StatisticalMechanics.Potts.StripDefects

-- A sweep boundary is a column of the original array.
def horizontal : Finset (Fin 4 × Fin 4) := HardinA229589StripData.horizontal
def between : Finset (Fin 4 × Fin 4) :=
  Finset.univ.filter fun e => e.1.val ≤ e.2.val + 1 ∧ e.2.val ≤ e.1.val + 1

def cl (p : Fin 4 → Fin 3) (d : ℕ) : Fin 28 :=
  HardinA229589StripData.cl p (if d = 0 then 0 else 1)

def T : Matrix (Fin 28) (Fin 28) ℤ :=
  Matrix.reindex (finSumFinEquiv : Fin 14 ⊕ Fin 14 ≃ Fin 28)
    (finSumFinEquiv : Fin 14 ⊕ Fin 14 ≃ Fin 28)
    (Matrix.fromBlocks HardinA233177PairTransfer.Q
      (![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 3, 2, 0, 1, 0, 2, 1, 2, 0, 1, 0, 0, 0],
    ![0, 2, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0],
    ![0, 0, 1, 2, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1],
    ![0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1],
    ![0, 0, 1, 1, 0, 1, 1, 0, 1, 2, 1, 0, 0, 0],
    ![0, 2, 1, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0],
    ![0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 2, 1, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 2, 2, 0, 2, 3, 1, 0, 1, 1],
    ![0, 1, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1],
    ![0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1]]) 0 HardinA233177PairTransfer.Q)

def initial : Fin 28 → ℤ := HardinA229589StripData.initial

def terminal : Fin 28 → ℤ := HardinA229589StripData.terminal

end D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P4a.HardinA229537StripData
