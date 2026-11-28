import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D
import Reg.Support.SingleDependentReadout

/-! Observation dependence for the source coordinate and metric operands. -/

open _root_.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Real

namespace Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

/-- One source function operand, with its first argument as state. -/
abbrev operandSignature (Y : Type) : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => Y)

private theorem binary_ne {f : ℝ → ℝ → ℝ} {x y z : ℝ}
    (h : f x z ≠ f y z) : f x ≠ f y := fun e => h (congrFun e z)

theorem minkowskiT_changes : minkowskiT 0 ≠ minkowskiT 1 := by
  apply binary_ne (z := 0)
  norm_num [minkowskiT, arctan_one]
  linarith [Real.pi_pos]

theorem factor_changes : conformalFactor 0 ≠ conformalFactor π := by
  apply binary_ne (z := 0)
  norm_num [conformalFactor]

theorem inverseTime_changes : inverseTime 0 ≠ inverseTime (π / 2) := by
  apply binary_ne (z := 0)
  norm_num [inverseTime, conformalFactor]

theorem inverseRadius_changes : inverseRadius 0 ≠ inverseRadius π := by
  apply binary_ne (z := π / 2)
  norm_num [inverseRadius, conformalFactor]

theorem minkowskiMetric_changes : minkowskiMetric 0 ≠ minkowskiMetric 1 := by
  intro h
  have e := congrArg (fun f : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ => f 0 0 0 1 0) h
  norm_num [minkowskiMetric, angularSpeedSq] at e

theorem eta_changes : deSitterEta 0 ≠ deSitterEta 1 := by
  intro h
  have e := congrArg deSitterTime h
  rw [deSitterTime_left_inverse, deSitterTime_left_inverse] at e
  norm_num at e

theorem time_changes : deSitterTime (deSitterEta 0) ≠ deSitterTime (deSitterEta 1) := by
  rw [deSitterTime_left_inverse, deSitterTime_left_inverse]
  norm_num

theorem cos_changes : cos 0 ≠ cos π := by norm_num

theorem sin_changes : sin 0 ≠ sin (π / 2) := by norm_num

theorem einsteinMetric_changes : einsteinMetric 0 ≠ einsteinMetric (π / 2) := by
  intro h
  have e := congrArg (fun f : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ => f 0 0 0 1 0) h
  norm_num [einsteinMetric, angularSpeedSq] at e

theorem deSitterMetric_changes : deSitterMetric 0 ≠ deSitterMetric 1 := by
  intro h
  have e := congrArg (fun f : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ => f 0 0 1 0 0 0 0) h
  norm_num [deSitterMetric, angularSpeedSq] at e

theorem scale_changes : deSitterScale 0 ≠ deSitterScale 1 := by
  apply binary_ne (z := 0)
  norm_num [deSitterScale]

theorem profile_changes : kruskalF 0 ≠ kruskalF 1 := by
  apply binary_ne (z := 2)
  norm_num [kruskalF, OmegaMath.ExponentialRadialCoordinates.profile]

theorem coefficient_changes : kruskalFactor 0 ≠ kruskalFactor 1 := by
  apply binary_ne (z := 1)
  have hp := OmegaMath.ExponentialRadialCoordinates.coefficient_pos
    (M := 1) (r := 1) (by norm_num) (by norm_num)
  simpa [kruskalFactor, OmegaMath.ExponentialRadialCoordinates.coefficient] using ne_of_lt hp

theorem exterior_changes : U_ext 0 ≠ U_ext 1 := by
  intro h
  have e := congrArg (fun f : ℝ → ℝ → ℝ => f 0 4) h
  have hp := (OmegaMath.ExponentialRadialCoordinates.exterior_signs
    (M := 1) (r := 4) (by norm_num) (by norm_num) 0).1
  have hz : U_ext 0 0 4 = 0 := by
    norm_num [U_ext, OmegaMath.ExponentialRadialCoordinates.leftCoordinate,
      Real.sqrt_eq_zero_of_nonpos]
  exact (ne_of_lt hp) (e.symm.trans hz)

theorem radius_changes : cycloidRadius 0 ≠ cycloidRadius 1 := by
  apply binary_ne (z := 0)
  norm_num [cycloidRadius, OmegaMath.ExponentialRadialCoordinates.cycloidalRadius]

theorem radial_changes : radialReachable 0 ≠ radialReachable 1 := by
  intro h
  have e := congrArg (fun f : ℝ → ℝ → ℝ → Prop => f 0 0 0) h
  have hp : radialReachable 0 0 0 0 := (radialReachable_iff _ _ _ _).2 (by norm_num)
  have hn : ¬ radialReachable 1 0 0 0 := by rw [radialReachable_iff]; norm_num
  exact hn (e ▸ hp)

theorem spherical_changes : sphericalReachable 0 ≠ sphericalReachable 1 := by
  intro h
  have e := congrArg (fun f : ℝ → ℝ → ℝ → Prop => f 0 0 0) h
  have hp : sphericalReachable 0 0 0 0 := (sphericalReachable_iff _ _ _ _).2 (by norm_num)
  have hn : ¬ sphericalReachable 1 0 0 0 := by rw [sphericalReachable_iff]; norm_num
  exact hn (e ▸ hp)

theorem omega_changes : desitterOmega 0 ≠ desitterOmega 1 := by
  apply binary_ne (z := 0)
  norm_num [desitterOmega]

theorem eta_zero : deSitterEta 0 = 0 := by
  norm_num [deSitterEta, Real.arctan_one]
  ring

theorem time_zero : deSitterTime 0 = 0 := by
  simpa only [eta_zero] using deSitterTime_left_inverse 0

end
end Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D
