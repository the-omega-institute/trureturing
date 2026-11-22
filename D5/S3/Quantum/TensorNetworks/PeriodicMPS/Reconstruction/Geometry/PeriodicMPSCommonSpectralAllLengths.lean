/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSCommonSpectralAllLengths
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSCommonSpectralAllLengths
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: The all-length determinant calculation applies to the literal trace-word Jacobian. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSCommonSpectralDeterminant

/-! The literal nine-by-nine Jacobian minor for every suffix length at least five. -/

set_option autoImplicit false

namespace PeriodicMPSCommonSpectralDeterminant

open PeriodicMPSCommonSpectralJets (literalJacobian literalJacobian_eq_closedForm)

/-- The literal derivative has a nonsingular nine-by-nine minor at every witness length. -/
theorem literalJacobian_det_ne_zero {m : ℕ} (hm : 5 ≤ m) :
    (literalJacobian m).det ≠ 0 := by
  rw [literalJacobian_eq_closedForm m (by omega), Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ (by norm_num)))
    (det_L_at_length_ge_five_ne_zero hm)

end PeriodicMPSCommonSpectralDeterminant
