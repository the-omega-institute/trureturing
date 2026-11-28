import Reg.D5.S3.Quantum.Gauge.DiracLandauEulerHeisenberg4D.Common

/-! Readouts for electromagnetic invariants and optical response. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.Lorentz.MaxwellRainichStressEnergy4D (V3 M4 eta4 fieldOfTensor
  fieldTensor maxwellStressCov)
open _root_.D5.S3.Quantum.Gauge.DiracLandauEulerHeisenberg4D
open _root_.Reg.Support.UnitSixO (operandSignature)
open LeanInformationAudit Matrix

namespace Reg.D5.S3.Quantum.Gauge.DiracLandauEulerHeisenberg4D.Optics

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

private def axial : V3 := ![0, 0, 1]

local macro "expandEH" : tactic =>
  `(tactic| norm_num [realize, axial, eulerHeisenbergLagrangian, eulerHeisenbergQuartic,
    eulerHeisenbergCoefficient, I1, I2,
    _root_.D5.S3.Geometry.Lorentz.MaxwellRainichStressEnergy4D.spatialNormSq,
    _root_.D5.S3.Geometry.Lorentz.MaxwellRainichStressEnergy4D.spatialDot] at *)

namespace Invariance

abbrev signature : Signature := operandSignature ℝ (ℝ → V3 → V3 → ℝ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (α m : ℝ) (E B : V3),
    (∀ Λ : M4, Λᵀ * eta4 * Λ = eta4 → Λ.det = 1 →
      let EB := fieldOfTensor (Λᵀ * fieldTensor E B * Λ)
      R.readout () () α m EB.1 EB.2 = eulerHeisenbergLagrangian α m E B) ∧
    eulerHeisenbergLagrangian α m (-E) B = eulerHeisenbergLagrangian α m E B ∧
    eulerHeisenbergLagrangian α m E (-B) = eulerHeisenbergLagrangian α m E B ∧
    (I1 E B = 0 → I2 E B = 0 → eulerHeisenbergLagrangian α m E B = 0)

def family : Registration arena (type_of% (@euler_heisenberg_lorentz_and_cp_invariance)) :=
  unitFamily% arena (@euler_heisenberg_lorentz_and_cp_invariance) (unitObserve% eulerHeisenbergLagrangian)
    (unitObserve% (fun _ _ _ _ => 0))
    (by
      intro h
      have hw := (h 0 1 0 axial).1 1 (by simp) (by simp)
      expandEH)
    (by
      refine ⟨(), 0, 1, ?_⟩
      intro h
      have hw := congrFun (congrFun (congrFun h 1) 0) axial
      change eulerHeisenbergLagrangian 0 1 0 axial =
        eulerHeisenbergLagrangian 1 1 0 axial at hw
      expandEH)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@euler_heisenberg_lorentz_and_cp_invariance) (Realization signature) Unit Unit :=
  bindMagnetic%
    `D5.S3.Quantum.Gauge.DiracLandauEulerHeisenberg4D.euler_heisenberg_lorentz_and_cp_invariance.__information_unit
    `Reg.D5.S3.Quantum.Gauge.DiracLandauEulerHeisenberg4D.Optics.Invariance.family
    arena family (unitObserve% eulerHeisenbergLagrangian)
    (unitPath% euler_heisenberg_lorentz_and_cp_invariance eulerHeisenbergLagrangian 0 0)

end Invariance

namespace Duality

abbrev signature : Signature := operandSignature V3 (V3 → ℝ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ E B : V3,
    (∀ θ : ℝ, let EB := dualityRotate E B θ
      maxwellStressCov EB.1 EB.2 = maxwellStressCov E B ∧
      I1 EB.1 EB.2 = Real.cos (2 * θ) * I1 E B - 2 * Real.sin (2 * θ) * I2 E B ∧
      I2 EB.1 EB.2 = Real.cos (2 * θ) * I2 E B + Real.sin (2 * θ) * I1 E B / 2 ∧
      R.readout () () EB.1 EB.2 - eulerHeisenbergQuartic E B =
        3 / 4 * (I1 E B ^ 2 - 4 * I2 E B ^ 2) * Real.sin (2 * θ) ^ 2 +
          3 * I1 E B * I2 E B * Real.sin (2 * θ) * Real.cos (2 * θ)) ∧
    ((∃ θ : ℝ, let EB := dualityRotate E B θ
      eulerHeisenbergQuartic EB.1 EB.2 ≠ eulerHeisenbergQuartic E B) ↔
        I1 E B ≠ 0 ∨ I2 E B ≠ 0) ∧
    (let EB := dualityRotate 0 B (Real.pi / 4)
     eulerHeisenbergQuartic EB.1 EB.2 = (7 / 4) * eulerHeisenbergQuartic 0 B ∧
     -(1 / 2) * I1 EB.1 EB.2 = 0)

def family : Registration arena (type_of% (@euler_heisenberg_breaks_em_duality)) :=
  unitFamily% arena (@euler_heisenberg_breaks_em_duality) (unitObserve% eulerHeisenbergQuartic)
    (unitObserve% (fun _ _ => 0))
    (by
      intro h
      have hw := ((h 0 axial).1 0).2.2.2
      change 0 - eulerHeisenbergQuartic 0 axial =
        3 / 4 * (I1 0 axial ^ 2 - 4 * I2 0 axial ^ 2) * Real.sin (2 * 0) ^ 2 +
          3 * I1 0 axial * I2 0 axial * Real.sin (2 * 0) * Real.cos (2 * 0) at hw
      expandEH)
    (by
      refine ⟨(), 0, axial, ?_⟩
      intro h
      have hw := congrFun h 0
      change eulerHeisenbergQuartic 0 0 = eulerHeisenbergQuartic axial 0 at hw
      expandEH)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@euler_heisenberg_breaks_em_duality) (Realization signature) Unit Unit :=
  bindMagnetic%
    `D5.S3.Quantum.Gauge.DiracLandauEulerHeisenberg4D.euler_heisenberg_breaks_em_duality.__information_unit
    `Reg.D5.S3.Quantum.Gauge.DiracLandauEulerHeisenberg4D.Optics.Duality.family
    arena family (unitObserve% eulerHeisenbergQuartic)
    (unitPath% euler_heisenberg_breaks_em_duality eulerHeisenbergQuartic 0 0)

end Duality

namespace Indices

abbrev signature : Signature := operandSignature ℝ (ℝ → ℝ → ℝ → ℝ → ℝ → ℝ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (α m e B : ℝ), 0 < α → 0 < m → 0 < B → α = e ^ 2 / (4 * Real.pi) →
    let u := eulerHeisenbergCoefficient α m * B ^ 2
    (∀ x y,
      HasDerivAt (deriv (R.readout () () α m B x y))
        ((1 + 10 * u) * x ^ 2 - (1 - 4 * u) * y ^ 2) 0 ∧
      HasDerivAt (deriv (perpendicularProbe α m B x y))
        ((1 - 4 * u) * x ^ 2 - (1 - 12 * u) * y ^ 2) 0) ∧
    parallelPhaseSpeedSq u =
      -deriv (deriv (parallelProbe α m B 0 1)) 0 /
        deriv (deriv (parallelProbe α m B 1 0)) 0 ∧
    perpendicularPhaseSpeedSq u =
      -deriv (deriv (perpendicularProbe α m B 0 1)) 0 /
        deriv (deriv (perpendicularProbe α m B 1 0)) 0 ∧
    HasDerivAt parallelRefractiveIndex 7 0 ∧
    HasDerivAt perpendicularRefractiveIndex 4 0 ∧
    7 * u = (7 * α / (90 * Real.pi)) * (e * B / m ^ 2) ^ 2 ∧
    4 * u = (4 * α / (90 * Real.pi)) * (e * B / m ^ 2) ^ 2 ∧
    (7 * u) / (4 * u) = 7 / 4 ∧
    (u < 1 / 12 →
      0 < parallelPhaseSpeedSq u ∧ parallelPhaseSpeedSq u < 1 ∧
      0 < perpendicularPhaseSpeedSq u ∧ perpendicularPhaseSpeedSq u < 1 ∧
      (parallelPhaseSpeedSq u < perpendicularPhaseSpeedSq u ↔ u < 3 / 68))

def family : Registration arena (type_of% (@vacuum_birefringence_indices_and_subluminality)) :=
  unitFamily% arena (@vacuum_birefringence_indices_and_subluminality) (unitObserve% parallelProbe)
    (unitObserve% (fun _ _ _ _ _ _ => 0))
    (by
      intro h
      let α := 1 / (4 * Real.pi)
      have ha : 0 < α := by unfold α; positivity
      have hh := ((h α 1 1 1 ha (by norm_num) (by norm_num) (by simp [α])).1 1 0).1.deriv
      have hc : 0 ≤ eulerHeisenbergCoefficient α 1 := by unfold eulerHeisenbergCoefficient; positivity
      norm_num [realize] at hh
      linarith)
    (by
      refine ⟨(), 0, 1, ?_⟩
      intro h
      have hw := congrFun (congrFun (congrFun (congrFun (congrFun h 1) 1) 0) 0) 0
      change parallelProbe 0 1 1 0 0 0 = parallelProbe 1 1 1 0 0 0 at hw
      unfold parallelProbe at hw
      expandEH)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@vacuum_birefringence_indices_and_subluminality) (Realization signature) Unit Unit :=
  bindMagnetic%
    `D5.S3.Quantum.Gauge.DiracLandauEulerHeisenberg4D.vacuum_birefringence_indices_and_subluminality.__information_unit
    `Reg.D5.S3.Quantum.Gauge.DiracLandauEulerHeisenberg4D.Optics.Indices.family
    arena family (unitObserve% parallelProbe)
    (unitPath% vacuum_birefringence_indices_and_subluminality parallelProbe 0 0)

end Indices

end

end Reg.D5.S3.Quantum.Gauge.DiracLandauEulerHeisenberg4D.Optics
