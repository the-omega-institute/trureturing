/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/LeftStripGeometricIntervalSign
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/LeftStripGeometricIntervalSign
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict negativity of the mixed left-strip kernel derivative for gaps from one to three halves. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.GeometricCertificate.Band1
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.GeometricCertificate.Band2
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.GeometricCertificate.Band3

/-! # The strict mixed logarithmic kernel sign for left-strip gaps in [1, 3/2] -/

namespace RefinedBMV.PositiveCenter

open private band_sound from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripGeometricCertificate

/-- The original mixed logarithmic kernel derivative is strictly negative on the
left strip for gaps from one to three halves. -/
theorem leftStrip_logKernel_mixed_lt_gap_one_to_three_halves {p : ℕ} (hp : 11 ≤ p) {u v : ℝ}
    (hu : 0 < u) (humax : u ≤ 1 / 2) (hd : 1 ≤ v - u) (hdmax : v - u ≤ 3 / 2) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 := by
  have huv : u < v := by linarith only [hd]
  refine leftStrip_logKernel_mixed_lt_of_geometric_scalar hp hu humax huv ?_
  intro a ha
  have ha₀ : 0 ≤ a := ha.1.le
  have hau : a < u := ha.2
  have hamax : a ≤ 1 / 2 := hau.le.trans humax
  have hw : 1 ≤ v - a := by linarith only [hd, hau]
  have hwmax : v - a ≤ 2 := by linarith only [hdmax, humax, ha₀]
  have hw₀ : 0 < v - a := by linarith only [hw]
  change 0 < leftStripGeometricScalar (3 / (p : ℝ)) a (v - a)
  by_cases h₁ : v - a ≤ 5 / 4
  · exact band_sound hp ha₀ hamax hw₀ (by norm_num) (by simpa using hw)
      (by simpa using h₁) LocalTaylor.band1
  by_cases h₂ : v - a ≤ 3 / 2
  · exact band_sound hp ha₀ hamax hw₀ (by norm_num)
      (by simpa using (le_of_lt (lt_of_not_ge h₁))) (by simpa using h₂) LocalTaylor.band2
  exact band_sound hp ha₀ hamax hw₀ (by norm_num)
    (by simpa using (le_of_lt (lt_of_not_ge h₂))) (by simpa using hwmax) LocalTaylor.band3

/--
info: 'RefinedBMV.PositiveCenter.leftStrip_logKernel_mixed_lt_gap_one_to_three_halves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms leftStrip_logKernel_mixed_lt_gap_one_to_three_halves

end RefinedBMV.PositiveCenter
