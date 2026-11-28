/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeCyclicInvariantSpectrum
   generality: I
   mirror-B: none(waiver:no-B-plane-mirror-for-source-module)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The native P48q cubic rotation has a nonzero fixed branch for every cubic scalar normalization. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeGradingRotation
import OmegaBuild.Commands

/-! The exact fixed-vector spectrum of scalar normalizations of the native
P48q cubic grading rotation on the full twisted state carrier. -/

compile_only_with_mathlib

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeCyclicInvariantSpectrum

open P48qFullEnergySpectrum (totalLZero_exact_eigenvalues)
open P48qNativeGradingRotation (gradingIndex gradingRotation gradingRotation_coeff
  totalWeight_eq_gradingIndex)
open P48qThirdTwistedField (State)
open P48qTwistedStateEnergy (totalLZero totalLZero_coeff)

local notation "ζ" => (ThirdTwistedChargeCocycle.zeta : ℂ)

private theorem gradingRotation_eigenvector (v : State) (n : ℕ)
    (henergy : totalLZero v = (16 / 9 + (n : ℂ) / 3) • v) :
    gradingRotation v = ζ ^ n • v := by
  apply Finsupp.ext
  intro p
  apply MvPolynomial.ext
  intro d
  simp only [gradingRotation_coeff, Finsupp.smul_apply, MvPolynomial.coeff_smul, smul_eq_mul]
  by_cases hcoeff : (v p).coeff d = 0
  · simp only [hcoeff, mul_zero]
  · have hweight := congrArg (fun w : State => (w p).coeff d) henergy
    simp only [totalLZero_coeff, totalWeight_eq_gradingIndex, Finsupp.smul_apply,
      MvPolynomial.coeff_smul, smul_eq_mul] at hweight
    have hindex : (gradingIndex p d : ℂ) = (n : ℂ) := by
      linear_combination 3 * (mul_right_cancel₀ hcoeff hweight)
    have hindexNat : gradingIndex p d = n := by exact_mod_cast hindex
    rw [hindexNat]

/-- A weight occurs among the fixed vectors exactly when its rotation phase
cancels the scalar normalization. -/
theorem nonzero_fixed_eigenvector_iff (c a : ℂ) :
    (∃ v : State, v ≠ 0 ∧ totalLZero v = a • v ∧ (c • gradingRotation) v = v) ↔
      ∃ n : ℕ, a = 16 / 9 + (n : ℂ) / 3 ∧ c * ζ ^ n = 1 := by
  constructor
  · rintro ⟨v, hv, henergy, hfixed⟩
    obtain ⟨n, rfl⟩ := (totalLZero_exact_eigenvalues a).mp ⟨v, hv, henergy⟩
    rw [LinearMap.smul_apply, gradingRotation_eigenvector v n henergy, smul_smul] at hfixed
    exact ⟨n, rfl, smul_left_injective ℂ hv (hfixed.trans (one_smul ℂ v).symm)⟩
  · rintro ⟨n, rfl, hphase⟩
    obtain ⟨v, hv, henergy⟩ := (totalLZero_exact_eigenvalues _).mpr ⟨n, rfl⟩
    refine ⟨v, hv, henergy, ?_⟩
    rw [LinearMap.smul_apply, gradingRotation_eigenvector v n henergy, smul_smul, hphase,
      one_smul]

/-- Every cubic scalar normalization fixes a nonzero state at one of the first
three weights of the native twisted module. -/
theorem exists_nonzero_fixed_eigenvector (c : ℂ) (hc : c ^ (3 : ℕ) = 1) :
    ∃ n : ℕ, n < 3 ∧ c * ζ ^ n = 1 ∧
      ∃ v : State, v ≠ 0 ∧ totalLZero v = (16 / 9 + (n : ℂ) / 3) • v ∧
        (c • gradingRotation) v = v := by
  have hζ : IsPrimitiveRoot ζ 3 :=
    IsPrimitiveRoot.coe_units_iff.mpr ThirdTwistedChargeCocycle.zeta_primitive
  have hinv : c⁻¹ ^ (3 : ℕ) = 1 := by rw [inv_pow, hc, inv_one]
  obtain ⟨n, hn, hpow⟩ := hζ.eq_pow_of_pow_eq_one hinv
  have hphase : c * ζ ^ n = 1 := by
    rw [hpow]
    exact mul_inv_cancel₀ (fun hzero => by simp [hzero] at hc)
  exact ⟨n, hn, hphase, (nonzero_fixed_eigenvector_iff c _).mpr ⟨n, rfl, hphase⟩⟩

#print axioms nonzero_fixed_eigenvector_iff
#print axioms exists_nonzero_fixed_eigenvector

run_cmd do
  for name in [``nonzero_fixed_eigenvector_iff, ``exists_nonzero_fixed_eigenvector] do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (fun ax => [``propext, ``Classical.choice, ``Quot.sound].contains ax) do
      throwError "Unexpected axiom closure for {name}: {axioms}"

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeCyclicInvariantSpectrum
