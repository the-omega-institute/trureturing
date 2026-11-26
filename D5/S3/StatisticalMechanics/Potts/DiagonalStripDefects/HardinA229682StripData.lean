/- GID: D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229682StripData
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229682StripData
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229682Strip.result; premises=D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229682StripCertificate.finite_certificate
   digest: Exact defect sectors of the five-column diagonal strip. -/

/-
admission_basis: open-problem-resolution (#31593; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229682Strip.result)
cl: proof_shape=bind-only; consumers=HardinA229682Strip.result
costTwo: proof_shape=bind-only; consumers=HardinA229682Strip.result
T: proof_shape=bind-only; consumers=HardinA229682Strip.result
initial: proof_shape=bind-only; consumers=HardinA229682Strip.result
terminal: proof_shape=bind-only; consumers=HardinA229682Strip.result
-/

import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203980StripData
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229507StripData
import Mathlib.Data.Matrix.Block
import Mathlib.Logic.Equiv.Fin.Basic

namespace D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229682StripData
open HardinA203980StripData (Row boundary)

def cl (p : Row) (d : ℕ) : Fin 24 :=
  if d = 2 then (boundary p).castAdd 16 else (HardinA229507StripData.cl p d).natAdd 8

def costTwo : Matrix (Fin 8) (Fin 8) ℤ :=
  ![![0, 8, 8, 16, 0, 16, 4, 4],
    ![4, 8, 4, 4, 4, 12, 6, 10],
    ![4, 4, 8, 4, 8, 24, 2, 16],
    ![4, 2, 2, 16, 6, 28, 5, 10],
    ![0, 2, 4, 6, 4, 16, 6, 14],
    ![2, 3, 6, 14, 8, 22, 5, 10],
    ![2, 6, 2, 10, 12, 20, 8, 10],
    ![1, 5, 8, 10, 14, 20, 5, 10]]

def T : Matrix (Fin 24) (Fin 24) ℤ :=
  Matrix.reindex (finSumFinEquiv : Fin 8 ⊕ Fin 16 ≃ Fin 24) finSumFinEquiv
    (Matrix.fromBlocks HardinA203980StripData.T
      (fun i => Fin.append (HardinA229507StripData.costOne i) (costTwo i)) 0 HardinA229507StripData.T)

def initial : Fin 24 → ℤ := Fin.append HardinA203980StripData.initial (0 : Fin 16 → ℤ)

def terminal : Fin 24 → ℤ := Fin.append (0 : Fin 8 → ℤ) HardinA229507StripData.terminal

end D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229682StripData
