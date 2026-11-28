import Reg.D5.S3.Quantum.Gauge.DiracLandauEulerHeisenberg4D.Common

/-! Readouts for the magnetic levels and Dirac blocks. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.Lorentz.DiracCliffordSpinors4D (γ Mat4)
open _root_.D5.S3.Quantum.Gauge.DiracLandauEulerHeisenberg4D
open _root_.Reg.Support.UnitSixO (operandSignature)
open LeanInformationAudit Matrix

namespace Reg.D5.S3.Quantum.Gauge.DiracLandauEulerHeisenberg4D.Magnetic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

private abbrev energySignature : Signature :=
  operandSignature ℝ (ℝ → ℝ → ℝ → ℕ → ℝ → ℝ)

private def energyActual : Realization energySignature := unitObserve% landauEnergySq

private theorem energyDependence : ∃ s : Unit, ∃ x y : ℝ,
    energyActual.readout s () x ≠ energyActual.readout s () y := by
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hv := congrFun (congrFun (congrFun (congrFun (congrFun h 0) 1) 2) 0) (1 / 2)
  norm_num [energyActual, realize, landauEnergySq] at hv

namespace Cancellation

abbrev arena : Arena where
  signature := energySignature
  Law R := ∀ (m pz qB g : ℝ), 0 < qB →
    (qB * (2 * (0 : ℝ) + 1 - g * (1 / 2)) = 0 ↔ g = 2) ∧
    (R.readout () () m pz qB g 0 (1 / 2) = m ^ 2 + pz ^ 2 ↔ g = 2)

def family : Registration arena (type_of% (@dirac_g2_zero_mode_iff)) :=
  unitFamily% arena (@dirac_g2_zero_mode_iff) (unitObserve% landauEnergySq)
    (unitObserve% (fun _ _ _ _ _ _ => 0))
    (by
      intro h
      have hw := (h 1 0 1 2 (by norm_num)).2.mpr rfl
      norm_num [realize] at hw)
    energyDependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@dirac_g2_zero_mode_iff) (Realization energySignature) Unit Unit :=
  bindMagnetic%
    `D5.S3.Quantum.Gauge.DiracLandauEulerHeisenberg4D.dirac_g2_zero_mode_iff.__information_unit
    `Reg.D5.S3.Quantum.Gauge.DiracLandauEulerHeisenberg4D.Magnetic.Cancellation.family
    arena family (unitObserve% landauEnergySq) (unitPath% dirac_g2_zero_mode_iff landauEnergySq 0 0)

end Cancellation

namespace Pairing

abbrev arena : Arena where
  signature := energySignature
  Law R := ∀ (m pz qB : ℝ), 0 < qB →
    ∀ (k n : ℕ) (σ : ℝ), (σ = 1 / 2 ∨ σ = -(1 / 2)) →
    (R.readout () () m pz qB 2 n σ = m ^ 2 + pz ^ 2 + 2 * (k : ℝ) * qB ↔
      (n = k ∧ σ = 1 / 2) ∨ (0 < k ∧ n = k - 1 ∧ σ = -(1 / 2)))

def family : Registration arena (type_of% (@dirac_landau_exact_twofold_degeneracy)) :=
  unitFamily% arena (@dirac_landau_exact_twofold_degeneracy) (unitObserve% landauEnergySq)
    (unitObserve% (fun _ _ _ _ _ _ => 0))
    (by
      intro h
      have hw := (h 0 0 1 (by norm_num) 1 1 (1 / 2) (Or.inl rfl)).mpr
        (Or.inl ⟨rfl, rfl⟩)
      norm_num [realize] at hw)
    energyDependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@dirac_landau_exact_twofold_degeneracy) (Realization energySignature) Unit Unit :=
  bindMagnetic%
    `D5.S3.Quantum.Gauge.DiracLandauEulerHeisenberg4D.dirac_landau_exact_twofold_degeneracy.__information_unit
    `Reg.D5.S3.Quantum.Gauge.DiracLandauEulerHeisenberg4D.Magnetic.Pairing.family
    arena family (unitObserve% landauEnergySq)
    (unitPath% dirac_landau_exact_twofold_degeneracy landauEnergySq 0 0)

end Pairing

namespace Pauli

abbrev signature : Signature := operandSignature (Fin 4) Mat4

abbrev arena : Arena where
  signature := signature
  Law R := ∀ qB : ℝ,
    (∀ i : Fin 3,
      (R.readout () () i.succ).submatrix (Fin.castAdd 2) (Fin.natAdd 2) =
        (![pauliX, pauliY, pauliZ] : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ) i) ∧
    (∀ (A : Type) [Ring A] [Algebra ℂ A] (px py x : A),
      px * py = py * px →
      px * x - x * px = algebraMap ℂ A (-Complex.I) →
      let πy := py + (qB : ℂ) • x
      pauliOperator px πy ^ 2 = pauliSquareTerm px πy qB) ∧
    (∀ ky : ℝ, pauliOperator magneticMomentumX (magneticMomentumY ky qB) ^ 2 =
      pauliSquareTerm magneticMomentumX (magneticMomentumY ky qB) qB)

def family : Registration arena (type_of% (@dirac_pauli_square_identity)) :=
  unitFamily% arena (@dirac_pauli_square_identity) (unitObserve% γ) (unitObserve% (fun _ => 0))
    (by
      intro h
      have hw := congrFun (congrFun ((h 0).1 0) 0) 1
      change (0 : ℂ) = 1 at hw
      exact zero_ne_one hw)
    (by
      refine ⟨(), 1, 3, ?_⟩
      intro h
      change γ 1 = γ 3 at h
      have h₁ := (dirac_pauli_square_identity 0).1 (0 : Fin 3)
      have h₃ := (dirac_pauli_square_identity 0).1 (2 : Fin 3)
      change (γ 1).submatrix (Fin.castAdd 2) (Fin.natAdd 2) = pauliX at h₁
      change (γ 3).submatrix (Fin.castAdd 2) (Fin.natAdd 2) = pauliZ at h₃
      rw [h, h₃] at h₁
      have hw := congrFun (congrFun h₁ 0) 0
      norm_num [pauliX, pauliZ] at hw)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@dirac_pauli_square_identity) (Realization signature) Unit Unit :=
  bindMagnetic%
    `D5.S3.Quantum.Gauge.DiracLandauEulerHeisenberg4D.dirac_pauli_square_identity.__information_unit
    `Reg.D5.S3.Quantum.Gauge.DiracLandauEulerHeisenberg4D.Magnetic.Pauli.family
    arena family (unitObserve% γ) (unitPath% dirac_pauli_square_identity γ 0 0)

end Pauli

namespace Oscillator

open Omega.Analysis.HermiteOscillator (mode)

abbrev signature : Signature := operandSignature ℝ (ℝ → ℕ → ℝ → ℝ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m pz qB ky : ℝ), 0 < qB → ∀ (n : ℕ) (i : Fin 2),
    let f := R.readout () () qB ky n
    f ≠ 0 ∧ (pauliZ i i).re = -2 * magneticSpinProjection i ∧
      ∀ x : ℝ, landauSquaredOperator m pz qB ky i f x =
        landauEnergySq m pz qB 2 n (magneticSpinProjection i) * f x

def family : Registration arena (type_of% (@dirac_landau_squared_energy_modes)) :=
  unitFamily% arena (@dirac_landau_squared_energy_modes) (unitObserve% mode)
    (unitObserve% (fun _ _ _ _ => 0))
    (by
      intro h
      exact (h 0 0 1 0 (by norm_num) 0 0).1 rfl)
    (by
      refine ⟨(), 1, 2, ?_⟩
      intro h
      have hw := congrFun (congrFun (congrFun h 0) 0) 1
      change mode 1 0 0 1 = mode 2 0 0 1 at hw
      have hsq (r : ℝ) (hr : 0 ≤ r) : (Real.sqrt (2 * r) * (1 + 0 / r)) ^ 2 = 2 * r := by
        rw [zero_div, add_zero, mul_one]
        exact Real.sq_sqrt (by positivity)
      have hmode (r : ℝ) (hr : 0 ≤ r) : mode r 0 0 1 = Real.exp (-(2 * r / 4)) := by
        unfold mode
        change ((Polynomial.hermite 0).map (Int.castRingHom ℝ)).eval _ *
          Real.exp (-((Real.sqrt (2 * r) * (1 + 0 / r)) ^ 2 / 4)) = _
        rw [hsq r hr]
        simp [Polynomial.hermite_zero]
      rw [hmode 1 (by norm_num), hmode 2 (by norm_num)] at hw
      have hvalues := Real.exp_injective hw
      norm_num at hvalues)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@dirac_landau_squared_energy_modes) (Realization signature) Unit Unit :=
  bindMagnetic%
    `D5.S3.Quantum.Gauge.DiracLandauEulerHeisenberg4D.dirac_landau_squared_energy_modes.__information_unit
    `Reg.D5.S3.Quantum.Gauge.DiracLandauEulerHeisenberg4D.Magnetic.Oscillator.family
    arena family (unitObserve% mode) (unitPath% dirac_landau_squared_energy_modes mode 0 0)

end Oscillator

end

end Reg.D5.S3.Quantum.Gauge.DiracLandauEulerHeisenberg4D.Magnetic
