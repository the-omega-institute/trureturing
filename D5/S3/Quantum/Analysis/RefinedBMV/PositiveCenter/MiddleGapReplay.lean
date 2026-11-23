/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/MiddleGapReplay
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/MiddleGapReplay
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict mixed derivative negativity for lower logarithmic coordinate at least four. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MiddleGapCertificate.Band1
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MiddleGapCertificate.Band2
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MiddleGapCertificate.Band3
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MiddleGapCertificate.Band4
import Batteries.Tactic.OpenPrivate

/-! # The right strip of the positive-center kernel -/

namespace RefinedBMV.PositiveCenter.MiddleGapReplay

open private Box.split rectangle verify verify_children strip_of_verify from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MiddleGapCertificate

private theorem rectangle_checked : verify rectangle 11 = true :=
  verify_children (b := rectangle) (n := 10)
    (verify_children (b := (Box.split rectangle).1) (n := 9) band1_checked band2_checked)
    (verify_children (b := (Box.split rectangle).2) (n := 9) band3_checked band4_checked)

/-- The mixed derivative is negative on the full positive-rate strip above lower coordinate four. -/
theorem logKernel_mixed_of_lower_four_le {p : ℕ} (hp : 11 ≤ p) {u v : ℝ}
    (hu : 4 ≤ u) (huv : u < v) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 := by
  by_cases hShort : v - u ≤ 2
  · exact CompactGap.logKernel_shortGap_mixed hp hu huv hShort
  by_cases hTail : 4 ≤ v - u
  · exact logKernel_mixed_of_four_le hp hu hTail
  · exact strip_of_verify rectangle_checked hp hu (lt_of_not_ge hShort) (le_of_not_ge hTail)

#print axioms logKernel_mixed_of_lower_four_le

end RefinedBMV.PositiveCenter.MiddleGapReplay
