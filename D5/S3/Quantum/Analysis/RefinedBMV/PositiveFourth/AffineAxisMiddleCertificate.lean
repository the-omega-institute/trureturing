/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveFourth/AffineAxisMiddleCertificate
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Nonnegativity of the middle-axis sign for all degrees at least eleven. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineAxisMiddleData
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffinePackedSweep
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineCertificateSign
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineAxisMiddleIdentity

/-! Bind the affine quotient to the middle-axis Gram sign and check every
mixed origin of its two annihilating chains. -/

namespace RefinedBMV.ThreeBlockGram.PositiveSpectrum.GroupedAffineMasks.AxisMiddle

open RefinedBMV.DividedDifference.SparseExpansion
open AffineRadixIdentity
open private checkedIdentity from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineAxisMiddleIdentity

private theorem checkedRoots : certificate.checkRootExponents 11 = true := by decide +kernel

private theorem checkedRates : certificate.checkRates = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
-- The coefficient mass and chain dimensions are computed from the concrete table.
private theorem checkedBounds : certificate.staticCheck 12 172 1578 193 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
-- The kernel computes the concrete affine prefix checks for these rows.
private theorem checkedRows0 :
    certificate.checkShiftBlock 1578 193 0 8 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
-- The kernel computes the concrete affine prefix checks for these rows.
private theorem checkedRows8 :
    certificate.checkShiftBlock 1578 193 8 8 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
-- The kernel computes the concrete affine prefix checks for these rows.
private theorem checkedRows16 :
    certificate.checkShiftBlock 1578 193 16 8 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
-- The kernel computes the concrete affine prefix checks for these rows.
private theorem checkedRows24 :
    certificate.checkShiftBlock 1578 193 24 8 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
-- The kernel computes the concrete affine prefix checks for these rows.
private theorem checkedRows32 :
    certificate.checkShiftBlock 1578 193 32 8 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
-- The kernel computes the concrete affine prefix checks for these rows.
private theorem checkedRows40 :
    certificate.checkShiftBlock 1578 193 40 8 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
-- The kernel computes the concrete affine prefix checks for these rows.
private theorem checkedRows48 :
    certificate.checkShiftBlock 1578 193 48 8 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
-- The kernel computes the concrete affine prefix checks for these rows.
private theorem checkedRows56 :
    certificate.checkShiftBlock 1578 193 56 8 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
-- The kernel computes the concrete affine prefix checks for these rows.
private theorem checkedRows64 :
    certificate.checkShiftBlock 1578 193 64 8 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
-- The kernel computes the concrete affine prefix checks for these rows.
private theorem checkedRows72 :
    certificate.checkShiftBlock 1578 193 72 8 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
-- The kernel computes the concrete affine prefix checks for these rows.
private theorem checkedRows80 :
    certificate.checkShiftBlock 1578 193 80 8 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
-- The kernel computes the concrete affine prefix checks for these rows.
private theorem checkedRows88 :
    certificate.checkShiftBlock 1578 193 88 3 = true := by decide +kernel

private theorem checkedRows (k : ℕ) (hk : k < certificate.rootsU.length) :
    certificate.checkRow 1578 193 k = true := by
  rw [← certificate.checkShiftRow_eq]
  have hk' : k < 91 := hk
  have fromBlock (start count : ℕ) (hend : start + count ≤ certificate.rootsU.length)
      (hcheck : certificate.checkShiftBlock 1578 193 start count = true)
      (hmem : k ∈ List.range' start count) :
      certificate.checkShiftRow 1578 193 k = true := by
    rw [certificate.checkShiftBlock_eq 1578 193 start count hend] at hcheck
    exact List.all_eq_true.mp hcheck k hmem
  by_cases hk8 : k < 8
  · exact fromBlock 0 8 (by decide) checkedRows0
      (List.mem_range'_1.mpr (by omega))
  by_cases hk16 : k < 16
  · exact fromBlock 8 8 (by decide) checkedRows8
      (List.mem_range'_1.mpr (by omega))
  by_cases hk24 : k < 24
  · exact fromBlock 16 8 (by decide) checkedRows16
      (List.mem_range'_1.mpr (by omega))
  by_cases hk32 : k < 32
  · exact fromBlock 24 8 (by decide) checkedRows24
      (List.mem_range'_1.mpr (by omega))
  by_cases hk40 : k < 40
  · exact fromBlock 32 8 (by decide) checkedRows32
      (List.mem_range'_1.mpr (by omega))
  by_cases hk48 : k < 48
  · exact fromBlock 40 8 (by decide) checkedRows40
      (List.mem_range'_1.mpr (by omega))
  by_cases hk56 : k < 56
  · exact fromBlock 48 8 (by decide) checkedRows48
      (List.mem_range'_1.mpr (by omega))
  by_cases hk64 : k < 64
  · exact fromBlock 56 8 (by decide) checkedRows56
      (List.mem_range'_1.mpr (by omega))
  by_cases hk72 : k < 72
  · exact fromBlock 64 8 (by decide) checkedRows64
      (List.mem_range'_1.mpr (by omega))
  by_cases hk80 : k < 80
  · exact fromBlock 72 8 (by decide) checkedRows72
      (List.mem_range'_1.mpr (by omega))
  by_cases hk88 : k < 88
  · exact fromBlock 80 8 (by decide) checkedRows80
      (List.mem_range'_1.mpr (by omega))
  exact fromBlock 88 3 (by decide) checkedRows88
    (List.mem_range'_1.mpr (by omega))

theorem middle_axis_nonneg (p : ℕ) (hp : 11 ≤ p) {r t : ℝ}
    (hr : 0 < r) (hr₁ : r < 1) (ht : 0 < t) (ht₁ : t < 1) :
    0 ≤ GramSign.axisMiddle.value
      (affineEntries ((p - 11 : ℕ) : ℝ) (r ^ 4) (t ^ 4) (r ^ p) (t ^ p)) := by
  rw [← factor_mul_table_of_checkIdentity .axisMiddle certificate 11 _ checkedIdentity]
  exact mul_nonneg (GramSign.removedFactor_nonneg _ (by positivity) (by positivity)
    (pow_le_one₀ hr.le hr₁.le) (by positivity) (pow_le_one₀ ht.le ht₁.le) (by positivity)
    (affineEntries_nonneg_at_degree p hp hr hr₁ ht ht₁ 6)
    (affineEntries_nonneg_at_degree p hp hr hr₁ ht ht₁ 7))
    (certificate.nonneg_tableTerms_at_degree 11 12 172 1578 193 p hp checkedRoots checkedRates
      checkedBounds checkedRows hr hr₁.le ht ht₁.le)

#print axioms middle_axis_nonneg


end RefinedBMV.ThreeBlockGram.PositiveSpectrum.GroupedAffineMasks.AxisMiddle
