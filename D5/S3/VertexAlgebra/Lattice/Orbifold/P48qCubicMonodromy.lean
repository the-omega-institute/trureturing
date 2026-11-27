/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qCubicMonodromy
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48qCubicMonodromy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The native P48q cubic conformal rotation has a nontrivial scalar cube. -/

import D5.S3.FiniteGroups.Cyclic.CyclicProjectiveMonodromy
import OmegaBuild.Commands
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeGradingRotation
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeConformalZero
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedStateEnergy

/-!
The conformal monodromy on the actual cubic twisted P48q state carrier,
including its vacuum phase and its covariance with the native fractional fields.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qCubicMonodromy

open FiniteGroups.Cyclic.CyclicAssociatorObstruction
  (cyclicProduct cyclicProduct_eq_one_of_mem twoCoboundary)
open FiniteGroups.Cyclic.CyclicProjectiveMonodromy (pow_orderOf_eq_cyclicProduct_smul)
open HalfFockSpectralFiberSource (actualInverse)
open LatticeActualConformalState (omega)
open LatticeSugawaraCurrents (sugawaraMode)
open NativeStandardThirdLift (standardLift)
open P48qAllJetWickField (NativeStates nativeField)
open P48qNativeConformalZero (native_conformal_coeff_neg_six_eq_totalLZero)
open P48qNativeGradingRotation (gradingRotation gradingRotation_coeff gradingRotation_cube
  gradingRotation_nativeField_coeff totalWeight_eq_gradingIndex)
open P48qThirdTwistedField (State)
open P48qTwistedChargeAction (lattice g g_cube g_isometry)
open P48qTwistedStateEnergy (totalLZero totalLZero_coeff vacuum vacuum_ne_zero)
open MvPolynomial

noncomputable section

local notation "τ" => (2 * (Real.pi : ℂ) * Complex.I)
local notation "ζ" => (ThirdTwistedChargeCocycle.zeta : ℂ)
local notation "C" => HVertexOperator.coeff
local notation "σ" => standardLift lattice g g_cube g_isometry

/-- The unnormalized conformal rotation at the twisted vacuum weight `16 / 9`. -/
def conformalMonodromy : Module.End ℂ State :=
  Complex.exp (τ * (16 / 9)) • gradingRotation

private theorem phase_gradingIndex (n : ℕ) :
    Complex.exp (τ * (16 / 9)) * ζ ^ n =
      Complex.exp (τ * (16 / 9 + (n : ℂ) / 3)) := by
  change Complex.exp (τ * (16 / 9)) * Complex.exp (τ / 3) ^ n = _
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  ring

/-- On every eigenvector of the full Fock zero mode, the rotation has the
conformal phase of that eigenvalue. -/
theorem conformalMonodromy_totalLZero_eigenvector (v : State) (a : ℂ)
    (heig : totalLZero v = a • v) :
    conformalMonodromy v = Complex.exp (τ * a) • v := by
  apply Finsupp.ext
  intro p
  apply MvPolynomial.ext
  intro d
  simp only [conformalMonodromy, LinearMap.smul_apply, Finsupp.smul_apply, coeff_smul, smul_eq_mul,
    gradingRotation_coeff, ← mul_assoc]
  by_cases hc : (v p).coeff d = 0
  · simp only [hc, mul_zero]
  · have he := congrArg (fun w : State => (w p).coeff d) heig
    simp only [totalLZero_coeff, Finsupp.smul_apply, coeff_smul, smul_eq_mul] at he
    have hw := mul_right_cancel₀ hc he
    rw [totalWeight_eq_gradingIndex] at hw
    rw [phase_gradingIndex, hw]

/-- The same eigenvector law for the actual conformal coefficient of the native field. -/
theorem conformalMonodromy_native_conformal_eigenvector (v : State) (a : ℂ)
    (heig : C (nativeField (omega lattice (actualInverse lattice))) (-6) v = a • v) :
    conformalMonodromy v = Complex.exp (τ * a) • v := by
  rw [native_conformal_coeff_neg_six_eq_totalLZero] at heig
  exact conformalMonodromy_totalLZero_eigenvector v a heig

private theorem vacuumPhase_cube :
    Complex.exp (τ * (16 / 9)) ^ (3 : ℕ) = ζ := by
  change Complex.exp (τ * (16 / 9)) ^ (3 : ℕ) = Complex.exp (τ / 3)
  have hexponent : (3 : ℂ) * (τ * (16 / 9)) = τ / 3 + (5 : ℂ) * τ := by ring
  have hperiod : Complex.exp ((5 : ℂ) * τ) = 1 := by
    simpa only [Nat.cast_ofNat] using Complex.exp_nat_mul_two_pi_mul_I 5
  rw [← Complex.exp_nat_mul, Nat.cast_ofNat, hexponent, Complex.exp_add, hperiod, mul_one]

/-- The cube of conformal monodromy on the actual state space is the primitive
third-root scalar. -/
theorem conformalMonodromy_cube : conformalMonodromy ^ 3 = ζ • (1 : Module.End ℂ State) := by
  rw [conformalMonodromy, smul_pow, gradingRotation_cube, vacuumPhase_cube]

/-- The scalar vacuum phase preserves the rotation covariance of every native
cover coefficient of a homogeneous lift eigenstate. -/
theorem conformalMonodromy_nativeField_coeff (a : NativeStates)
    (s : ℤ) (ha : σ a = ζ ^ s • a) (k h : ℤ)
    (hh : sugawaraMode lattice (actualInverse lattice) 0 a = (h : ℂ) • a) :
    conformalMonodromy * C (nativeField a) k = ζ ^ s • (C (nativeField a) k * conformalMonodromy) := by
  simp only [conformalMonodromy, smul_mul_assoc, mul_smul_comm,
    gradingRotation_nativeField_coeff a s ha k h hh, smul_smul]
  rw [mul_comm (Complex.exp (τ * (16 / 9))) (ζ ^ s)]

/-- A normalized projective action whose generator is the native conformal
monodromy detects the actual ambient associator on the cubic generator. -/
theorem cyclicProduct_eq_zeta_of_nativeMonodromy {G : Type*} [Group G]
    (α : G → G → G → ℂˣ) (x : G) (hx : orderOf x = 3) (T : G → Module.End ℂ State)
    (hOne : T 1 = 1) (hGenerator : T x = conformalMonodromy)
    (hMul : ∀ i : ℕ, T (x ^ i) * T x = (α x (x ^ i) x : ℂ) • T (x ^ i * x)) :
    cyclicProduct α x = ThirdTwistedChargeCocycle.zeta := by
  have hPower := pow_orderOf_eq_cyclicProduct_smul α x T hOne hMul
  rw [hx, hGenerator, conformalMonodromy_cube] at hPower
  have hScalar := congrArg (fun L : Module.End ℂ State => L vacuum) hPower
  simp only [LinearMap.smul_apply, Module.End.one_apply] at hScalar
  exact Units.ext ((smul_left_injective ℂ vacuum_ne_zero hScalar).symm)

/-- Such a cubic generator is excluded from a subgroup trivializing the
same associator. The projective action and its generator identification are
premises of the orbifold comparison. -/
theorem not_mem_of_nativeMonodromy {G : Type*} [Group G]
    (α : G → G → G → ℂˣ) (x : G) (hx : orderOf x = 3) (T : G → Module.End ℂ State)
    (hOne : T 1 = 1) (hGenerator : T x = conformalMonodromy)
    (hMul : ∀ i : ℕ, T (x ^ i) * T x = (α x (x ^ i) x : ℂ) • T (x ^ i * x))
    (H : Subgroup G) (β : H → H → ℂˣ)
    (hβ : ∀ a b c : H, α a.val b.val c.val = twoCoboundary β a b c) : x ∉ H := by
  intro hmem
  have h := cyclicProduct_eq_zeta_of_nativeMonodromy α x hx T hOne hGenerator hMul
  rw [cyclicProduct_eq_one_of_mem α H β hβ hmem] at h
  exact ThirdTwistedChargeCocycle.zeta_primitive.ne_one (by decide) h.symm

#print axioms conformalMonodromy
#print axioms conformalMonodromy_totalLZero_eigenvector
#print axioms conformalMonodromy_native_conformal_eigenvector
#print axioms conformalMonodromy_cube
#print axioms conformalMonodromy_nativeField_coeff
#print axioms cyclicProduct_eq_zeta_of_nativeMonodromy
#print axioms not_mem_of_nativeMonodromy

end
end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qCubicMonodromy
