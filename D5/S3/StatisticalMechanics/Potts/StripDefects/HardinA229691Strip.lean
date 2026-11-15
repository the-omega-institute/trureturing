/- GID: D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691Strip
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691Strip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691Strip.finite_certificate
   digest: Exact-budget transfer for Hardin's registered defective colourings. -/

/-
admission_basis: open-problem-resolution (#30838; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229691Strip.result)
Valid: proof_shape=bind-only; consumers=finite_certificate, result
cl: proof_shape=bind-only; consumers=finite_certificate, result
T: proof_shape=bind-only; consumers=finite_certificate, result
initial: proof_shape=bind-only; consumers=finite_certificate, result
terminal: proof_shape=bind-only; consumers=finite_certificate, result
W: proof_shape=bind-only; consumers=finite_certificate, result
cellOrder: proof_shape=bind-only; consumers=a, result
Normal: proof_shape=bind-only; consumers=a, result
decidableNormal: proof_shape=bind-only; consumers=a, result
decidableValid: proof_shape=bind-only; consumers=finite_certificate
a: proof_shape=bind-only; consumers=result
finite_certificate: proof_shape=bind-only; consumers=result
result: proof_shape=bind-only; consumers=external sequence A229691
-/

import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229583StripData
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import Mathlib.Logic.Equiv.Fin.Basic

/-! Literal row-major canonical counts and row transfer. -/
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229691Strip
open HardinA229583StripData (Row Boundary horizontal antidiagonal boundary cross)
open DefectTransfer (bondDefects defects literalCount lumped_count forward forward_shift)
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical (Canonical canonical_pattern_card)

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

private abbrev cellOrder (n : ℕ) : LinearOrder (Fin n × Fin 5) :=
  LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective
private def Normal {n : ℕ} (A : Fin n × Fin 5 → Fin 3) : Prop :=
  @Canonical (Fin n × Fin 5) (cellOrder n).toLT 3 A
private instance decidableNormal {n : ℕ} (A : Fin n × Fin 5 → Fin 3) : Decidable (Normal A) := by
  unfold Normal Canonical
  change Decidable (∀ (i : Fin n × Fin 5) (b : Fin 3), b < A i →
    ∃ j : Fin n × Fin 5, finProdFinEquiv j < finProdFinEquiv i ∧ A j = b)
  infer_instance

/-- Literal row-major canonical arrays at the exact defect budget. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun A : Fin n × Fin 5 → Fin 3 =>
    defects horizontal antidiagonal (List.ofFn fun i j => A (i, j)) = 2 ∧ Normal A).card

theorem finite_certificate :
    (∀ p (d : Fin 3), Valid p d.val →
      terminal (cl p d.val) = (if d.val = 0 then 1 else 0)) ∧
    (∀ p (d : Fin 3), Valid p d.val → ∀ r : Row,
      cross p r + bondDefects horizontal r r ≤ d.val →
      Valid (boundary r) (d.val - (cross p r + bondDefects horizontal r r))) ∧
    (∀ p (d : Fin 3), Valid p d.val → ∀ s : Fin 27,
      (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d.val ∧
        cl (boundary r) (d.val - (cross p r + bondDefects horizontal r r)) = s
        then (1 : ℤ) else 0) = T (cl p d.val) s) ∧
    (∀ r : Row, bondDefects horizontal r r ≤ 2 →
      Valid (boundary r) (2 - bondDefects horizontal r r)) ∧
    (∀ s : Fin 27, (∑ r : Row, if bondDefects horizontal r r ≤ 2 ∧
      cl (boundary r) (2 - bondDefects horizontal r r) = s then (1 : ℤ) else 0) = initial s) ∧
    (W 0 = initial ∧ ∀ i : Fin 7, W i.succ = Matrix.vecMul (W i.castSucc) T) ∧
    W 7 = ∑ j : Fin 6, (![-5832, 14580, -13122, 4995, -729, 45] j : ℤ) • W ⟨1 + j.val, by omega⟩ := by
  decide +kernel

attribute [local irreducible] a

/-- The registered recurrence at every index at least 8. -/
theorem result (n : ℕ) :
    (a (n + 8) : ℤ) = 45 * a (n + 7) - 729 * a (n + 6) + 4995 * a (n + 5) - 13122 * a (n + 4) + 14580 * a (n + 3) - 5832 * a (n + 2) := by
  have labelled (m : ℕ) :
      (literalCount (q := 3) horizontal antidiagonal 2 (m + 1) : ℤ) =
        dotProduct initial ((T ^ m).mulVec terminal) := by
    apply lumped_count horizontal antidiagonal boundary cross Valid cl T initial terminal 2
      (by decide +kernel)
    · intro p d h
      exact finite_certificate.1 p ⟨d, by have hd : d ≤ 2 := h.1; omega⟩ h
    · intro p d h r hr
      exact finite_certificate.2.1 p ⟨d, by have hd : d ≤ 2 := h.1; omega⟩ h r hr
    · intro p d h s
      exact finite_certificate.2.2.1 p ⟨d, by have hd : d ≤ 2 := h.1; omega⟩ h s
    · exact finite_certificate.2.2.2.1
    · exact finite_certificate.2.2.2.2.1
  have tab (i : Fin 8) : forward T initial i.val = W i := by
    induction i using Fin.induction with
    | zero => exact finite_certificate.2.2.2.2.2.1.1.symm
    | succ i ih =>
      rw [forward, Fin.val_succ, Function.iterate_succ_apply']
      change Matrix.vecMul (forward T initial i.val) T = W i.succ
      change forward T initial i.val = W i.castSucc at ih
      rw [ih]
      exact (finite_certificate.2.2.2.2.2.1.2 i).symm
  have poly : forward T initial (1 + 6) =
      ∑ j : Fin 6, (![-5832, 14580, -13122, 4995, -729, 45] j : ℤ) • forward T initial (1 + j.val) := by
    rw [tab ⟨7, by omega⟩]
    simp_rw [show ∀ j : Fin 6, forward T initial (1 + j.val) = W ⟨1 + j.val, by omega⟩
      from fun j => tab ⟨1 + j.val, by omega⟩]
    exact finite_certificate.2.2.2.2.2.2
  have scale (m : ℕ) : literalCount (q := 3) horizontal antidiagonal 2 (m + 1) = 6 * a (m + 1) := by
    classical
    let S : (Fin (m + 1) × Fin 5 → Fin 3) → Prop := fun A =>
      defects horizontal antidiagonal (List.ofFn fun i j => A (i, j)) = 2
    have invariant : ∀ e : Equiv.Perm (Fin 3), ∀ A, S (e ∘ A) ↔ S A := by
      intro e A
      change defects horizontal antidiagonal _ = 2 ↔ _
      rw [show (List.ofFn fun i j => (e ∘ A) (i, j)) =
        (List.ofFn fun i j => A (i, j)).map (fun r => e ∘ r) by rw [List.map_ofFn]; rfl,
        DefectTransfer.relabel_defects]
    have nonconstant : ∀ A, S A → ∃ x y, A x ≠ A y := by
      intro A h
      by_contra he
      push_neg at he
      have const : A = fun _ => A (0, 0) := funext fun x => he x (0, 0)
      change defects horizontal antidiagonal _ = 2 at h
      rw [const] at h
      simp only [List.ofFn_const] at h
      rw [DefectTransfer.constant_defects] at h
      have cards : horizontal.card = 4 ∧ antidiagonal.card = 4 := by decide +kernel
      rw [cards.1, cards.2] at h
      omega
    have orbit := @canonical_pattern_card (Fin (m + 1) × Fin 5) inferInstance
      (cellOrder (m + 1)) S invariant nonconstant
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype] at orbit
    unfold literalCount a Normal
    convert orbit using 1
    apply congrArg (fun x : ℕ => 6 * x)
    apply congrArg Finset.card
    ext A
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, S]
  have bridge (m : ℕ) :
      dotProduct initial ((T ^ m).mulVec terminal) = 6 * (a (m + 1) : ℤ) := by
    rw [← labelled, scale]
    push_cast
    rfl
  have h := forward_shift T initial terminal 6 1 ![-5832, 14580, -13122, 4995, -729, 45] poly n
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_one] at h
  have h1 := bridge (n + 1)
  have h2 := bridge (n + 2)
  have h3 := bridge (n + 3)
  have h4 := bridge (n + 4)
  have h5 := bridge (n + 5)
  have h6 := bridge (n + 6)
  have h7 := bridge (n + 7)
  simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] at h h1 h2 h3 h4 h5 h6 h7
  rw [h1, h2, h3, h4, h5, h6, h7] at h
  norm_num only [Nat.reduceAdd, zero_add] at h
  linarith

end D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229691Strip
