import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.GeometricCertificate.Band1
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.GeometricCertificate.Band2
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.GeometricCertificate.Band3
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.GeometricCertificate.Band4
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.GeometricCertificate.Band5
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.GeometricCertificate.Band6

/-! # The strict mixed logarithmic kernel sign on the left strip -/

namespace RefinedBMV.PositiveCenter.LocalTaylor

private theorem moderateLeftStripCheck_verified : moderateLeftStripCheck 5 = true := by
  simp only [moderateLeftStripCheck, band1, band2, band3, band4, band5, band6, Bool.and_true]

end RefinedBMV.PositiveCenter.LocalTaylor

namespace RefinedBMV.PositiveCenter

/-- The original mixed logarithmic kernel derivative is strictly negative in the
left strip with gap at least one. -/
theorem leftStrip_logKernel_mixed_lt_ge_one {p : ℕ} (hp : 11 ≤ p) {u v : ℝ}
    (hu : 0 < u) (humax : u ≤ 1 / 2) (hd : 1 ≤ v - u) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 :=
  leftStrip_logKernel_mixed_lt_of_certificate LocalTaylor.moderateLeftStripCheck_verified
    hp hu humax hd

/-- info: 'RefinedBMV.PositiveCenter.leftStrip_logKernel_mixed_lt_ge_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms leftStrip_logKernel_mixed_lt_ge_one

end RefinedBMV.PositiveCenter
