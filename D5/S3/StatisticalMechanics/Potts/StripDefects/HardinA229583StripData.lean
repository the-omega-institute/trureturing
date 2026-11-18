/- GID: D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583StripData
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583StripData
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583Strip.finite_certificate
   digest: Finite boundary classes and forward weights for width-five strips. -/

/-
admission_basis: open-problem-resolution (#30580; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229583Strip.result)
Row: proof_shape=bind-only; consumers=HardinA229583Strip.finite_certificate
Boundary: proof_shape=bind-only; consumers=HardinA229583Strip.finite_certificate
horizontal: proof_shape=bind-only; consumers=HardinA229583Strip.finite_certificate
antidiagonal: proof_shape=bind-only; consumers=HardinA229583Strip.finite_certificate
boundary: proof_shape=bind-only; consumers=HardinA229583Strip.finite_certificate
cross: proof_shape=bind-only; consumers=HardinA229583Strip.finite_certificate
Valid: proof_shape=bind-only; consumers=HardinA229583Strip.finite_certificate
decidableValid: proof_shape=bind-only; consumers=HardinA229583Strip.finite_certificate
cl: proof_shape=bind-only; consumers=HardinA229583Strip.finite_certificate
T: proof_shape=bind-only; consumers=HardinA229583Strip.finite_certificate
initial: proof_shape=bind-only; consumers=HardinA229583Strip.finite_certificate
terminal: proof_shape=bind-only; consumers=HardinA229583Strip.finite_certificate
W: proof_shape=bind-only; consumers=HardinA229583Strip.finite_certificate
-/

import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer

open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229583StripData
open DefectTransfer (bondDefects)

abbrev Row := Fin 5 → Fin 3
abbrev Boundary := Fin 4 → Fin 3
def horizontal : Finset (Fin 5 × Fin 5) :=
  Finset.univ.image fun j : Fin 4 => (j.castSucc, j.succ)
def antidiagonal : Finset (Fin 5 × Fin 5) :=
  Finset.univ.image fun j : Fin 4 => (j.succ, j.castSucc)
def boundary (r : Row) : Boundary := Fin.tail r
def cross (p : Boundary) (r : Row) : ℕ :=
  bondDefects antidiagonal (Fin.cons 0 p) r
def Valid (p : Boundary) (d : ℕ) : Prop :=
  d ≤ 1 ∧ (Finset.univ.filter fun j : Fin 3 => p j.castSucc = p j.succ).card ≤ 1 - d
private instance decidableValid (p : Boundary) (d : ℕ) : Decidable (Valid p d) :=
  inferInstanceAs (Decidable (_ ∧ _))
def cl (p : Boundary) (d : ℕ) : Fin 14 :=
  if d = 1 ∧ p 0 ≠ p 1 ∧ p 0 = p 2 ∧ p 0 ≠ p 3 ∧ p 1 ≠ p 2 ∧ p 1 = p 3 ∧ p 2 ≠ p 3 then 0 else
  if d = 1 ∧ p 0 ≠ p 1 ∧ p 0 = p 2 ∧ p 0 ≠ p 3 ∧ p 1 ≠ p 2 ∧ p 1 ≠ p 3 ∧ p 2 ≠ p 3 then 1 else
  if d = 1 ∧ p 0 ≠ p 1 ∧ p 0 ≠ p 2 ∧ p 0 = p 3 ∧ p 1 ≠ p 2 ∧ p 1 ≠ p 3 ∧ p 2 ≠ p 3 then 2 else
  if d = 1 ∧ p 0 ≠ p 1 ∧ p 0 ≠ p 2 ∧ p 0 ≠ p 3 ∧ p 1 ≠ p 2 ∧ p 1 = p 3 ∧ p 2 ≠ p 3 then 3 else
  if d = 0 ∧ p 0 = p 1 ∧ p 0 ≠ p 2 ∧ p 0 = p 3 ∧ p 1 ≠ p 2 ∧ p 1 = p 3 ∧ p 2 ≠ p 3 then 4 else
  if d = 0 ∧ p 0 = p 1 ∧ p 0 ≠ p 2 ∧ p 0 ≠ p 3 ∧ p 1 ≠ p 2 ∧ p 1 ≠ p 3 ∧ p 2 ≠ p 3 then 5 else
  if d = 0 ∧ p 0 ≠ p 1 ∧ p 0 = p 2 ∧ p 0 = p 3 ∧ p 1 ≠ p 2 ∧ p 1 ≠ p 3 ∧ p 2 = p 3 then 6 else
  if d = 0 ∧ p 0 ≠ p 1 ∧ p 0 = p 2 ∧ p 0 ≠ p 3 ∧ p 1 ≠ p 2 ∧ p 1 = p 3 ∧ p 2 ≠ p 3 then 7 else
  if d = 0 ∧ p 0 ≠ p 1 ∧ p 0 = p 2 ∧ p 0 ≠ p 3 ∧ p 1 ≠ p 2 ∧ p 1 ≠ p 3 ∧ p 2 ≠ p 3 then 8 else
  if d = 0 ∧ p 0 ≠ p 1 ∧ p 0 ≠ p 2 ∧ p 0 = p 3 ∧ p 1 = p 2 ∧ p 1 ≠ p 3 ∧ p 2 ≠ p 3 then 9 else
  if d = 0 ∧ p 0 ≠ p 1 ∧ p 0 ≠ p 2 ∧ p 0 ≠ p 3 ∧ p 1 = p 2 ∧ p 1 ≠ p 3 ∧ p 2 ≠ p 3 then 10 else
  if d = 0 ∧ p 0 ≠ p 1 ∧ p 0 ≠ p 2 ∧ p 0 = p 3 ∧ p 1 ≠ p 2 ∧ p 1 ≠ p 3 ∧ p 2 ≠ p 3 then 11 else
  if d = 0 ∧ p 0 ≠ p 1 ∧ p 0 ≠ p 2 ∧ p 0 ≠ p 3 ∧ p 1 ≠ p 2 ∧ p 1 = p 3 ∧ p 2 ≠ p 3 then 12 else
  13
def T : Matrix (Fin 14) (Fin 14) ℤ :=
  ![![5, 5, 3, 3, 1, 1, 5, 3, 3, 2, 2, 5, 5, 3],
    ![4, 4, 3, 3, 2, 2, 4, 2, 2, 3, 3, 6, 6, 3],
    ![2, 2, 3, 3, 4, 4, 2, 7, 7, 3, 3, 6, 6, 3],
    ![4, 4, 3, 3, 2, 2, 4, 6, 6, 1, 1, 4, 4, 3],
    ![0, 0, 0, 0, 0, 0, 0, 3, 3, 0, 0, 2, 2, 0],
    ![0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 2, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 4, 4, 0],
    ![0, 0, 0, 0, 0, 0, 0, 5, 5, 0, 0, 3, 3, 0],
    ![0, 0, 0, 0, 0, 0, 0, 4, 4, 0, 0, 3, 3, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 3, 3, 0],
    ![0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 3, 3, 0],
    ![0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 3, 3, 0],
    ![0, 0, 0, 0, 0, 0, 0, 4, 4, 0, 0, 3, 3, 0],
    ![0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 2, 0]]
def initial : Fin 14 → ℤ := ![12, 12, 12, 12, 12, 12, 12, 6, 6, 12, 12, 6, 6, 12]
def terminal : Fin 14 → ℤ := ![0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
def W : Fin 6 → Fin 14 → ℤ :=
  ![![12, 12, 12, 12, 12, 12, 12, 6, 6, 12, 12, 6, 6, 12],
    ![180, 180, 144, 144, 108, 108, 180, 438, 438, 108, 108, 516, 516, 144],
    ![2484, 2484, 1944, 1944, 1404, 1404, 2484, 11142, 11142, 1476, 1476, 11232, 11232, 1944],
    ![34020, 34020, 26568, 26568, 19116, 19116, 34020, 223182, 223182, 20196, 20196, 209304, 209304, 26568],
    ![465588, 465588, 363528, 363528, 261468, 261468, 465588, 4023270, 4023270, 276372, 276372, 3621672, 3621672, 363528],
    ![6371460, 6371460, 4974696, 4974696, 3577932, 3577932, 6371460, 68322366, 68322366, 3782052, 3782052, 59919912, 59919912, 4974696]]


end D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229583StripData
