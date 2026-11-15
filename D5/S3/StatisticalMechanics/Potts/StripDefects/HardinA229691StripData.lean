/- GID: D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691StripData
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691StripData
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691Strip.finite_certificate
   digest: Exact-budget transfer for Hardin's registered defective colourings. -/

/-
admission_basis: open-problem-resolution (#30838; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229691Strip.result)
Valid: proof_shape=bind-only; consumers=HardinA229691Strip.finite_certificate
decidableValid: proof_shape=bind-only; consumers=HardinA229691Strip.finite_certificate
cl: proof_shape=bind-only; consumers=HardinA229691Strip.finite_certificate
T: proof_shape=bind-only; consumers=HardinA229691Strip.finite_certificate
initial: proof_shape=bind-only; consumers=HardinA229691Strip.finite_certificate
terminal: proof_shape=bind-only; consumers=HardinA229691Strip.finite_certificate
W: proof_shape=bind-only; consumers=HardinA229691Strip.finite_certificate
-/

import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229583StripData

/-! Finite class data consumed by the registered settlement. -/
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229691StripData
open HardinA229583StripData (Row Boundary horizontal antidiagonal boundary cross)
def Valid (p : Boundary) (d : ℕ) : Prop :=
  d ≤ 2 ∧ (Finset.univ.filter fun j : Fin 3 => p j.castSucc = p j.succ).card ≤ 2 - d
private instance decidableValid (p : Boundary) (d : ℕ) : Decidable (Valid p d) :=
  inferInstanceAs (Decidable (_ ∧ _))
def cl (p : Boundary) (d : ℕ) : Fin 27 :=
  if d = 2 ∧ p 0 ≠ p 1 ∧ p 0 = p 2 ∧ p 0 ≠ p 3 ∧ p 1 ≠ p 2 ∧ p 1 = p 3 ∧ p 2 ≠ p 3 then 0 else
  if d = 2 ∧ p 0 ≠ p 1 ∧ p 0 = p 2 ∧ p 0 ≠ p 3 ∧ p 1 ≠ p 2 ∧ p 1 ≠ p 3 ∧ p 2 ≠ p 3 then 1 else
  if d = 2 ∧ p 0 ≠ p 1 ∧ p 0 ≠ p 2 ∧ p 0 = p 3 ∧ p 1 ≠ p 2 ∧ p 1 ≠ p 3 ∧ p 2 ≠ p 3 then 2 else
  if d = 2 ∧ p 0 ≠ p 1 ∧ p 0 ≠ p 2 ∧ p 0 ≠ p 3 ∧ p 1 ≠ p 2 ∧ p 1 = p 3 ∧ p 2 ≠ p 3 then 3 else
  if d = 1 ∧ p 0 = p 1 ∧ p 0 ≠ p 2 ∧ p 0 = p 3 ∧ p 1 ≠ p 2 ∧ p 1 = p 3 ∧ p 2 ≠ p 3 then 4 else
  if d = 1 ∧ p 0 = p 1 ∧ p 0 ≠ p 2 ∧ p 0 ≠ p 3 ∧ p 1 ≠ p 2 ∧ p 1 ≠ p 3 ∧ p 2 ≠ p 3 then 5 else
  if d = 1 ∧ p 0 ≠ p 1 ∧ p 0 = p 2 ∧ p 0 = p 3 ∧ p 1 ≠ p 2 ∧ p 1 ≠ p 3 ∧ p 2 = p 3 then 6 else
  if d = 1 ∧ p 0 ≠ p 1 ∧ p 0 = p 2 ∧ p 0 ≠ p 3 ∧ p 1 ≠ p 2 ∧ p 1 = p 3 ∧ p 2 ≠ p 3 then 7 else
  if d = 1 ∧ p 0 ≠ p 1 ∧ p 0 = p 2 ∧ p 0 ≠ p 3 ∧ p 1 ≠ p 2 ∧ p 1 ≠ p 3 ∧ p 2 ≠ p 3 then 8 else
  if d = 1 ∧ p 0 ≠ p 1 ∧ p 0 ≠ p 2 ∧ p 0 = p 3 ∧ p 1 = p 2 ∧ p 1 ≠ p 3 ∧ p 2 ≠ p 3 then 9 else
  if d = 1 ∧ p 0 ≠ p 1 ∧ p 0 ≠ p 2 ∧ p 0 ≠ p 3 ∧ p 1 = p 2 ∧ p 1 ≠ p 3 ∧ p 2 ≠ p 3 then 10 else
  if d = 1 ∧ p 0 ≠ p 1 ∧ p 0 ≠ p 2 ∧ p 0 = p 3 ∧ p 1 ≠ p 2 ∧ p 1 ≠ p 3 ∧ p 2 ≠ p 3 then 11 else
  if d = 1 ∧ p 0 ≠ p 1 ∧ p 0 ≠ p 2 ∧ p 0 ≠ p 3 ∧ p 1 ≠ p 2 ∧ p 1 = p 3 ∧ p 2 ≠ p 3 then 12 else
  if d = 1 ∧ p 0 ≠ p 1 ∧ p 0 ≠ p 2 ∧ p 0 ≠ p 3 ∧ p 1 ≠ p 2 ∧ p 1 ≠ p 3 ∧ p 2 = p 3 then 13 else
  if d = 0 ∧ p 0 = p 1 ∧ p 0 = p 2 ∧ p 0 ≠ p 3 ∧ p 1 = p 2 ∧ p 1 ≠ p 3 ∧ p 2 ≠ p 3 then 14 else
  if d = 0 ∧ p 0 = p 1 ∧ p 0 ≠ p 2 ∧ p 0 = p 3 ∧ p 1 ≠ p 2 ∧ p 1 = p 3 ∧ p 2 ≠ p 3 then 15 else
  if d = 0 ∧ p 0 = p 1 ∧ p 0 ≠ p 2 ∧ p 0 ≠ p 3 ∧ p 1 ≠ p 2 ∧ p 1 ≠ p 3 ∧ p 2 = p 3 then 16 else
  if d = 0 ∧ p 0 = p 1 ∧ p 0 ≠ p 2 ∧ p 0 ≠ p 3 ∧ p 1 ≠ p 2 ∧ p 1 ≠ p 3 ∧ p 2 ≠ p 3 then 17 else
  if d = 0 ∧ p 0 ≠ p 1 ∧ p 0 = p 2 ∧ p 0 = p 3 ∧ p 1 ≠ p 2 ∧ p 1 ≠ p 3 ∧ p 2 = p 3 then 18 else
  if d = 0 ∧ p 0 ≠ p 1 ∧ p 0 = p 2 ∧ p 0 ≠ p 3 ∧ p 1 ≠ p 2 ∧ p 1 = p 3 ∧ p 2 ≠ p 3 then 19 else
  if d = 0 ∧ p 0 ≠ p 1 ∧ p 0 = p 2 ∧ p 0 ≠ p 3 ∧ p 1 ≠ p 2 ∧ p 1 ≠ p 3 ∧ p 2 ≠ p 3 then 20 else
  if d = 0 ∧ p 0 ≠ p 1 ∧ p 0 ≠ p 2 ∧ p 0 = p 3 ∧ p 1 = p 2 ∧ p 1 ≠ p 3 ∧ p 2 ≠ p 3 then 21 else
  if d = 0 ∧ p 0 ≠ p 1 ∧ p 0 ≠ p 2 ∧ p 0 ≠ p 3 ∧ p 1 = p 2 ∧ p 1 = p 3 ∧ p 2 = p 3 then 22 else
  if d = 0 ∧ p 0 ≠ p 1 ∧ p 0 ≠ p 2 ∧ p 0 ≠ p 3 ∧ p 1 = p 2 ∧ p 1 ≠ p 3 ∧ p 2 ≠ p 3 then 23 else
  if d = 0 ∧ p 0 ≠ p 1 ∧ p 0 ≠ p 2 ∧ p 0 = p 3 ∧ p 1 ≠ p 2 ∧ p 1 ≠ p 3 ∧ p 2 ≠ p 3 then 24 else
  if d = 0 ∧ p 0 ≠ p 1 ∧ p 0 ≠ p 2 ∧ p 0 ≠ p 3 ∧ p 1 ≠ p 2 ∧ p 1 = p 3 ∧ p 2 ≠ p 3 then 25 else
  26
def T : Matrix (Fin 27) (Fin 27) ℤ :=
  ![![5, 5, 3, 3, 1, 1, 5, 3, 3, 2, 2, 5, 5, 3, 2, 7, 1, 7, 3, 5, 5, 5, 2, 5, 5, 5, 5],
    ![4, 4, 3, 3, 2, 2, 4, 2, 2, 3, 3, 6, 6, 3, 0, 7, 2, 7, 2, 8, 8, 5, 3, 5, 5, 5, 6],
    ![2, 2, 3, 3, 4, 4, 2, 7, 7, 3, 3, 6, 6, 3, 0, 2, 4, 2, 7, 5, 5, 5, 3, 5, 5, 5, 6],
    ![4, 4, 3, 3, 2, 2, 4, 6, 6, 1, 1, 4, 4, 3, 4, 5, 2, 5, 6, 2, 2, 8, 1, 8, 8, 8, 4],
    ![0, 0, 0, 0, 0, 0, 0, 3, 3, 0, 0, 2, 2, 0, 0, 1, 0, 1, 3, 7, 7, 1, 0, 1, 7, 7, 2],
    ![0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 0, 2, 2, 7, 7, 2, 0, 2, 8, 8, 2],
    ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 4, 4, 0, 0, 1, 0, 1, 1, 8, 8, 5, 0, 5, 2, 2, 4],
    ![0, 0, 0, 0, 0, 0, 0, 5, 5, 0, 0, 3, 3, 0, 0, 1, 0, 1, 5, 3, 3, 2, 0, 2, 5, 5, 3],
    ![0, 0, 0, 0, 0, 0, 0, 4, 4, 0, 0, 3, 3, 0, 0, 2, 0, 2, 4, 2, 2, 3, 0, 3, 6, 6, 3],
    ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 3, 3, 0, 0, 5, 0, 5, 1, 7, 7, 2, 0, 2, 5, 5, 3],
    ![0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 3, 3, 0, 0, 4, 0, 4, 2, 5, 5, 1, 0, 1, 4, 4, 3],
    ![0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 3, 3, 0, 0, 4, 0, 4, 2, 7, 7, 3, 0, 3, 6, 6, 3],
    ![0, 0, 0, 0, 0, 0, 0, 4, 4, 0, 0, 3, 3, 0, 0, 2, 0, 2, 4, 6, 6, 1, 0, 1, 4, 4, 3],
    ![0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 0, 2, 2, 5, 5, 4, 0, 4, 8, 8, 2],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 2, 2, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 0, 0, 0, 2, 2, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 2, 2, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 2, 2, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 4, 4, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 5, 0, 0, 0, 3, 3, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 4, 0, 0, 0, 3, 3, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 3, 3, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 3, 3, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 3, 3, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 4, 0, 0, 0, 3, 3, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 2, 2, 0]]
def initial : Fin 27 → ℤ := ![12, 12, 12, 12, 12, 12, 12, 6, 6, 12, 12, 6, 6, 12, 12, 6, 12, 6, 6, 0, 0, 6, 12, 6, 0, 0, 6]
def terminal : Fin 27 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
def W : Fin 8 → Fin 27 → ℤ :=
  ![![12, 12, 12, 12, 12, 12, 12, 6, 6, 12, 12, 6, 6, 12, 12, 6, 12, 6, 6, 0, 0, 6, 12, 6, 0, 0, 6],
    ![180, 180, 144, 144, 108, 108, 180, 438, 438, 108, 108, 516, 516, 144, 72, 486, 108, 486, 438, 942, 942, 510, 108, 510, 954, 954, 516],
    ![2484, 2484, 1944, 1944, 1404, 1404, 2484, 11142, 11142, 1476, 1476, 11232, 11232, 1944, 936, 9702, 1404, 9702, 11142, 37350, 37350, 10050, 1476, 10050, 37278, 37278, 11232],
    ![34020, 34020, 26568, 26568, 19116, 19116, 34020, 223182, 223182, 20196, 20196, 209304, 209304, 26568, 12744, 173070, 19116, 173070, 223182, 993438, 993438, 179586, 20196, 179586, 958446, 958446, 209304],
    ![465588, 465588, 363528, 363528, 261468, 261468, 465588, 4023270, 4023270, 276372, 276372, 3621672, 3621672, 363528, 174312, 2913894, 261468, 2913894, 4023270, 22210038, 22210038, 3033018, 276372, 3033018, 20838870, 20838870, 3621672],
    ![6371460, 6371460, 4974696, 4974696, 3577932, 3577932, 6371460, 68322366, 68322366, 3782052, 3782052, 59919912, 59919912, 4974696, 2385288, 47327166, 3577932, 47327166, 68322366, 449438382, 449438382, 49380354, 3782052, 49380354, 412458318, 412458318, 59919912],
    ![87191316, 87191316, 68076936, 68076936, 48962556, 48962556, 87191316, 1116505782, 1116505782, 51756084, 51756084, 961725960, 961725960, 68076936, 32641704, 749602998, 48962556, 749602998, 1116505782, 8519487174, 8519487174, 783513162, 51756084, 783513162, 7681405446, 7681405446, 961725960],
    ![1193183460, 1193183460, 931609512, 931609512, 670035564, 670035564, 1193183460, 17763290766, 17763290766, 708264324, 708264324, 15100570152, 15100570152, 931609512, 446690376, 11653127694, 670035564, 11653127694, 17763290766, 154178657982, 154178657982, 12196766322, 708264324, 12196766322, 137032507998, 137032507998, 15100570152]]

end D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229691StripData
