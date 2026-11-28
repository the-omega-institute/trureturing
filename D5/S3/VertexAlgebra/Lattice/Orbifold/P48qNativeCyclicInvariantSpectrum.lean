/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeCyclicInvariantSpectrum
   generality: I
   mirror-B: none(waiver:no-B-plane-mirror-for-source-module)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cubic covariant rotations of P48q have a nonzero fixed branch. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qCubicMonodromy
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeGradingRotation
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeModeProductSpan
import OmegaBuild.Commands

/-! The exact fixed-vector spectrum of scalar normalizations of the native
P48q cubic grading rotation on the full twisted state carrier. -/

compile_only_with_mathlib

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeCyclicInvariantSpectrum

open P48qFullEnergySpectrum (totalLZero_exact_eigenvalues)
open P48qNativeGradingRotation (gradingIndex gradingRotation gradingRotation_coeff
  gradingRotation_cube totalWeight_eq_gradingIndex)
open P48qThirdTwistedField (State)
open P48qTwistedStateEnergy (totalLZero totalLZero_coeff totalLZero_ground_eigenspace
  totalLZero_vacuum vacuum vacuum_ne_zero)
open private nativeModeSpan nativeModeSpan_eq_top gradingRotation_any_coeff from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeModeProductSpan
open P48qNativeConformalZero (native_conformal_coeff_neg_six_eq_totalLZero)
open LatticeActualConformalState (omega)
open HalfFockSpectralFiberSource (actualInverse)
open P48qTwistedChargeAction (lattice g g_cube g_isometry)

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

private theorem eq_smul_gradingRotation_of_field_covariant (R : Module.End ℂ State)
    (hcov : ∀ (a : P48qAllJetWickField.NativeStates) (e : ℤ),
      R * HVertexOperator.coeff (P48qAllJetWickField.nativeField a) e =
        ζ ^ e • (HVertexOperator.coeff (P48qAllJetWickField.nativeField a) e * R))
    (c : ℂ) (hc : R vacuum = c • vacuum) : R = c • gradingRotation := by
  have hrotvac : gradingRotation vacuum = vacuum := by
    have henergy : totalLZero vacuum = (16 / 9 + (↑(0 : ℕ) : ℂ) / 3) • vacuum := by
      simpa using totalLZero_vacuum
    exact (gradingRotation_eigenvector vacuum 0 henergy).trans (by rw [pow_zero, one_smul])
  have hker : nativeModeSpan vacuum ≤ LinearMap.ker (R - c • gradingRotation) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a, e⟩, rfl⟩
    apply LinearMap.mem_ker.mpr
    have hR := LinearMap.congr_fun (hcov a e) vacuum
    change R (HVertexOperator.coeff (P48qAllJetWickField.nativeField a) e vacuum) =
      ζ ^ e • HVertexOperator.coeff (P48qAllJetWickField.nativeField a) e (R vacuum) at hR
    rw [hc, map_smul] at hR
    have hG := LinearMap.congr_fun (gradingRotation_any_coeff a e) vacuum
    change gradingRotation (HVertexOperator.coeff
      (P48qAllJetWickField.nativeField a) e vacuum) =
      ζ ^ e • HVertexOperator.coeff (P48qAllJetWickField.nativeField a) e
        (gradingRotation vacuum) at hG
    rw [hrotvac] at hG
    change R (HVertexOperator.coeff (P48qAllJetWickField.nativeField a) e vacuum) -
      (c • gradingRotation) (HVertexOperator.coeff
        (P48qAllJetWickField.nativeField a) e vacuum) = 0
    rw [LinearMap.smul_apply, hR, hG]
    module
  have heq : R - c • gradingRotation = 0 := by
    apply LinearMap.ext
    intro v
    have hv : v ∈ nativeModeSpan vacuum := by
      rw [nativeModeSpan_eq_top vacuum vacuum_ne_zero]
      exact Submodule.mem_top
    exact LinearMap.mem_ker.mp (hker hv)
  exact sub_eq_zero.mp heq

/-- A cubic field-covariant endomorphism is a scalar grading rotation and has a
nonzero fixed energy eigenvector. -/
theorem field_covariant_order_three_classification (R : Module.End ℂ State)
    (hcov : ∀ (a : P48qAllJetWickField.NativeStates) (e : ℤ),
      R * HVertexOperator.coeff (P48qAllJetWickField.nativeField a) e =
        ζ ^ e • (HVertexOperator.coeff (P48qAllJetWickField.nativeField a) e * R))
    (horder : R ^ (3 : ℕ) = 1) :
    ∃ c : ℂ, R = c • gradingRotation ∧ c ^ (3 : ℕ) = 1 ∧
      ∃ n : ℕ, n < 3 ∧ ∃ v : State, v ≠ 0 ∧
        totalLZero v = (16 / 9 + (n : ℂ) / 3) • v ∧ R v = v := by
  have hzeta : ζ ^ (-6 : ℤ) = 1 := by
    have hζ : IsPrimitiveRoot ζ 3 :=
      IsPrimitiveRoot.coe_units_iff.mpr ThirdTwistedChargeCocycle.zeta_primitive
    exact (hζ.zpow_eq_one_iff_dvd (-6)).mpr (by decide)
  have hcomm : R * totalLZero = totalLZero * R := by
    have hzero := hcov (omega lattice (actualInverse lattice)) (-6)
    rw [native_conformal_coeff_neg_six_eq_totalLZero, hzeta, one_smul] at hzero
    exact hzero
  have hground : totalLZero (R vacuum) = (16 / 9 : ℂ) • R vacuum := by
    have hvalue := congrArg (fun T : Module.End ℂ State => T vacuum) hcomm
    rw [Module.End.mul_apply, Module.End.mul_apply, totalLZero_vacuum, map_smul] at hvalue
    exact hvalue.symm
  have hmem : R vacuum ∈ totalLZero.eigenspace (16 / 9 : ℂ) :=
    Module.End.mem_eigenspace_iff.mpr hground
  rw [totalLZero_ground_eigenspace] at hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hR : R = c • gradingRotation :=
    eq_smul_gradingRotation_of_field_covariant R hcov c hc.symm
  have hpow : (c • gradingRotation) ^ (3 : ℕ) = 1 := by simpa [hR] using horder
  rw [smul_pow, gradingRotation_cube] at hpow
  have hcub : c ^ (3 : ℕ) = 1 := by
    apply smul_left_injective ℂ vacuum_ne_zero
    simpa using congrArg (fun T : Module.End ℂ State => T vacuum) hpow
  obtain ⟨n, hn, _hphase, v, hv, henergy, hfixed⟩ :=
    exists_nonzero_fixed_eigenvector c hcub
  exact ⟨c, hR, hcub, n, hn, v, hv, henergy, by simpa [hR] using hfixed⟩

/-- The actual field covariance and the conformal vacuum phase determine the
unnormalized conformal monodromy. -/
theorem eq_conformalMonodromy_of_field_covariant (R : Module.End ℂ State)
    (hcov : ∀ (a : P48qAllJetWickField.NativeStates) (e : ℤ),
      R * HVertexOperator.coeff (P48qAllJetWickField.nativeField a) e =
        ζ ^ e • (HVertexOperator.coeff (P48qAllJetWickField.nativeField a) e * R))
    (hvac : R vacuum = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (16 / 9)) • vacuum) :
    R = P48qCubicMonodromy.conformalMonodromy := by
  unfold P48qCubicMonodromy.conformalMonodromy
  exact eq_smul_gradingRotation_of_field_covariant R hcov _ hvac

#print axioms nonzero_fixed_eigenvector_iff
#print axioms exists_nonzero_fixed_eigenvector

run_cmd do
  for name in [``nonzero_fixed_eigenvector_iff, ``exists_nonzero_fixed_eigenvector,
      ``field_covariant_order_three_classification, ``eq_conformalMonodromy_of_field_covariant] do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (fun ax => [``propext, ``Classical.choice, ``Quot.sound].contains ax) do
      throwError "Unexpected axiom closure for {name}: {axioms}"

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeCyclicInvariantSpectrum
