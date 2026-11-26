/- GID: D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229507StripData
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229507StripData
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229507Strip.result; premises=D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229507StripCertificate.finite_certificate
   digest: Exact defect sectors of the five-column diagonal strip. -/

/-
admission_basis: open-problem-resolution (#31593; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229507Strip.result)
cl: proof_shape=bind-only; consumers=HardinA229507Strip.result
costOne: proof_shape=bind-only; consumers=HardinA229507Strip.result
T: proof_shape=bind-only; consumers=HardinA229507Strip.result
initial: proof_shape=bind-only; consumers=HardinA229507Strip.result
terminal: proof_shape=bind-only; consumers=HardinA229507Strip.result
-/

import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203980StripData
import Mathlib.Data.Matrix.Block
import Mathlib.Logic.Equiv.Fin.Basic

namespace D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229507StripData
open HardinA203980StripData (Row boundary)

def cl (p : Row) (d : ℕ) : Fin 16 :=
  if 0 < d then (boundary p).castAdd 8 else (boundary p).natAdd 8

def costOne : Matrix (Fin 8) (Fin 8) ℤ :=
  ![![0, 0, 0, 0, 8, 8, 8, 8],
    ![0, 0, 8, 8, 12, 12, 4, 4],
    ![0, 8, 0, 8, 4, 16, 4, 0],
    ![0, 4, 4, 0, 6, 8, 2, 4],
    ![2, 6, 2, 6, 8, 16, 4, 4],
    ![1, 3, 4, 4, 8, 12, 3, 5],
    ![4, 4, 4, 4, 8, 12, 0, 4],
    ![2, 2, 0, 4, 4, 10, 2, 4]]

def T : Matrix (Fin 16) (Fin 16) ℤ :=
  Matrix.reindex (finSumFinEquiv : Fin 8 ⊕ Fin 8 ≃ Fin 16) finSumFinEquiv
    (Matrix.fromBlocks HardinA203980StripData.T costOne 0 HardinA203980StripData.T)

def initial : Fin 16 → ℤ := Fin.append HardinA203980StripData.initial (0 : Fin 8 → ℤ)

def terminal : Fin 16 → ℤ := Fin.append (0 : Fin 8 → ℤ) HardinA203980StripData.terminal

end D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229507StripData
