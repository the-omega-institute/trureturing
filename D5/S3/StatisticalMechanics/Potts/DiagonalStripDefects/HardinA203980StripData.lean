/- GID: D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980StripData
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980StripData
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980Strip.result; premises=D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980StripCertificate.finite_certificate
   digest: Eight boundary classes for five-column diagonal and antidiagonal strips. -/

/-
admission_basis: open-problem-resolution (#31593; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA203980Strip.result)
Row: proof_shape=bind-only; consumers=HardinA203980Strip.result
horizontal: proof_shape=bind-only; consumers=HardinA203980Strip.result
between: proof_shape=bind-only; consumers=HardinA203980Strip.result
boundary: proof_shape=bind-only; consumers=HardinA203980Strip.result
representatives: proof_shape=bind-only; consumers=DiagonalSymmetry.class_rep, HardinA203980StripCertificate.representative_counts
T: proof_shape=bind-only; consumers=HardinA203980Strip.result
initial: proof_shape=bind-only; consumers=HardinA203980Strip.result
terminal: proof_shape=bind-only; consumers=HardinA203980Strip.result
-/

import Mathlib.Data.Matrix.Block

namespace D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203980StripData

abbrev Row := Fin 5 → Fin 3

def horizontal : Finset (Fin 5 × Fin 5) := ∅

def between : Finset (Fin 5 × Fin 5) :=
  {(0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2), (3, 4), (4, 3)}

def boundary (p : Row) : Fin 8 :=
  if p 0 = p 2 ∧ p 2 = p 4 then (if p 1 = p 3 then 0 else 1)
  else if p 0 = p 4 then (if p 1 = p 3 then 2 else 3)
  else if p 0 = p 2 ∨ p 2 = p 4 then (if p 1 = p 3 then 4 else 5)
  else (if p 1 = p 3 then 6 else 7)

def representatives : Fin 8 → Row :=
  ![![0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0],
    ![0, 0, 1, 0, 0],
    ![0, 0, 1, 1, 0],
    ![0, 0, 0, 0, 1],
    ![0, 0, 0, 1, 1],
    ![0, 0, 1, 0, 2],
    ![0, 0, 1, 1, 2]]

def T : Matrix (Fin 8) (Fin 8) ℤ :=
  ![![4, 4, 4, 4, 8, 8, 0, 0],
    ![2, 2, 0, 0, 4, 4, 2, 2],
    ![2, 0, 2, 0, 4, 0, 0, 0],
    ![1, 0, 0, 0, 2, 0, 1, 0],
    ![2, 2, 2, 2, 4, 4, 0, 0],
    ![1, 1, 0, 0, 2, 2, 1, 1],
    ![0, 2, 0, 2, 0, 4, 0, 0],
    ![0, 1, 0, 0, 0, 2, 0, 1]]

def initial : Fin 8 → ℤ := ![9, 18, 18, 36, 36, 72, 18, 36]

def terminal : Fin 8 → ℤ := 1

end D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203980StripData
