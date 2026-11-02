/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianBranchKernel
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianBranchKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.WellKnown]
   utility: none
   digest: Formal regularized cross coefficients and all-index mixed neck jets of the original two-current kernel. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianPairKernel
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
Candidate adapted from the hash-pinned 2026-11-02 source supplier. Square-root coordinates p,q mean t=p^2,u=q^2.
Multiplication by p*q removes precisely t^(-1/2)u^(-1/2), and multiplication
by p removes precisely t^(-1/2). No external mode is discarded.

Transient exact rational checks connect these branch expansions to the same
current whose regular part is the pair kernel. Formal rescaling, a ring
homomorphism, supplies the branch expansion; it is not defined by its desired
coefficients. The two mixed branch series consume that expansion with the
actual formal neck root. Their coefficients are then identified with -df,
including the input/detector sign difference.

This does not construct an analytic sewn curve or identify the original
infinite resolvent with an elliptic bidifferential.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianBranchKernel

open OriginalGaussianPairKernel

/-- Independently defined by the native inverse of (1-X)^2. -/
def branchFactor : OneSeries :=
  PowerSeries.C (1 / 2 : ℂ) * (1 + PowerSeries.X) *
    (PowerSeries.invOneSubPow ℂ 2).val

private theorem inverse_square_coeff (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.invOneSubPow ℂ 2).val = (n : ℂ) + 1 := by
  simp [PowerSeries.invOneSubPow, PowerSeries.coeff_mk, Nat.add_comm]

/-- All branch modes, starting at n=0. -/
private theorem branchFactor_coeff (n : ℕ) : PowerSeries.coeff n branchFactor = (n : ℂ) + 1 / 2 := by
  rw [branchFactor, mul_assoc, add_mul, one_mul, PowerSeries.coeff_C_mul, map_add]
  cases n with
  | zero => simp [inverse_square_coeff]
  | succ n =>
    rw [PowerSeries.coeff_succ_X_mul, inverse_square_coeff, inverse_square_coeff]
    push_cast
    ring

private abbrev branchIter : Series ≃ₐ[ℂ] PowerSeries OneSeries :=
  MvPowerSeries.optionEquivLeft Unit ℂ

/-- Substitute X=t*u in the negative rational branch factor. -/
def crossExpansion : Series := branchIter.symm
  (PowerSeries.rescale (PowerSeries.X : OneSeries)
    (PowerSeries.map PowerSeries.C (-branchFactor)))

/- proof_shape: crossExpansion_coeff: content
   admission_basis: escape-witness
   escape_witness: The inverse-square branch factor is substituted at t*u,
     giving every diagonal half mode and zero off-diagonal coefficients. -/
/-- Thus the actual dt du expansion is -sum (n+1/2)t^(n-1/2)u^(n-1/2).
The theorem uses regularized integer exponents; the prefactor is (sqrt(t)sqrt(u))^(-1). -/
theorem crossExpansion_coeff (m n : ℕ) :
    coeff₂ m n crossExpansion = if m = n then -((m : ℂ) + 1 / 2) else 0 := by
  change PowerSeries.coeff n (PowerSeries.coeff m
    (branchIter (branchIter.symm (PowerSeries.rescale (PowerSeries.X : OneSeries)
      (PowerSeries.map PowerSeries.C (-branchFactor)))))) = _
  rw [AlgEquiv.apply_symm_apply]
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_map, map_neg,
    PowerSeries.coeff_mul_C, PowerSeries.coeff_X_pow, branchFactor_coeff]
  by_cases h : m = n
  · simp [h]
  · simp [h, Ne.symm h]

/-- First branch kernel in t, after removing t^(-1/2), with neck variable a. -/
def inputBranch : PowerSeries OneSeries :=
  PowerSeries.C (inverseRoot ^ 3) *
    PowerSeries.rescale (inverseRoot ^ 2) (PowerSeries.map PowerSeries.C branchFactor)

/-- Opposite branch kernel; its negative sign is the inverse-coordinate Jacobian. -/
def detectorBranch : PowerSeries OneSeries :=
  -PowerSeries.C inverseRoot *
    PowerSeries.rescale (root ^ 2) (PowerSeries.map PowerSeries.C branchFactor)

private theorem binomial_power (z : ℂ) (n : ℕ) :
    PowerSeries.binomialSeries ℂ z ^ n = PowerSeries.binomialSeries ℂ ((n : ℂ) * z) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, ← PowerSeries.binomialSeries_add]
    congr 1
    push_cast
    ring

private theorem input_root_power (n : ℕ) :
    inverseRoot ^ 3 * (inverseRoot ^ 2) ^ n =
      PowerSeries.binomialSeries ℂ (-(n : ℂ) - 3 / 2) := by
  rw [← pow_mul, ← pow_add, inverseRoot, binomial_power]
  congr 1
  push_cast
  ring

private theorem detector_root_power (n : ℕ) :
    inverseRoot * (root ^ 2) ^ n =
      PowerSeries.binomialSeries ℂ ((n : ℂ) - 1 / 2) := by
  rw [← pow_mul, root, binomial_power, inverseRoot, ← PowerSeries.binomialSeries_add]
  congr 1
  push_cast
  ring

/-- Actual input neck jet r_n*(1+a)^(-r_n-1), for every external half mode n. -/
private theorem inputBranch_coeff (n : ℕ) :
    PowerSeries.coeff n inputBranch = PowerSeries.C ((n : ℂ) + 1 / 2) *
      PowerSeries.binomialSeries ℂ (-(n : ℂ) - 3 / 2) := by
  rw [inputBranch, PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale,
    PowerSeries.coeff_map, branchFactor_coeff]
  calc
    _ = PowerSeries.C ((n : ℂ) + 1 / 2) *
        (inverseRoot ^ 3 * (inverseRoot ^ 2) ^ n) := by ring
    _ = _ := by rw [input_root_power]

/-- Actual detector neck jet -r_n*(1+a)^(r_n-1), with the opposite sign retained. -/
private theorem detectorBranch_coeff (n : ℕ) :
    PowerSeries.coeff n detectorBranch = -PowerSeries.C ((n : ℂ) + 1 / 2) *
      PowerSeries.binomialSeries ℂ ((n : ℂ) - 1 / 2) := by
  rw [detectorBranch, neg_mul, map_neg, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_rescale, PowerSeries.coeff_map, branchFactor_coeff]
  calc
    _ = -PowerSeries.C ((n : ℂ) + 1 / 2) *
        (inverseRoot * (root ^ 2) ^ n) := by ring
    _ = _ := by rw [detector_root_power]

private theorem binomial_derivative (z : ℂ) :
    PowerSeries.derivative (PowerSeries.binomialSeries ℂ z) =
      PowerSeries.C z * PowerSeries.binomialSeries ℂ (z - 1) := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_C_mul]
  simpa [PowerSeries.binomialSeries_coeff, Nat.choose_one_right,
    Ring.choose_one_right, nsmul_eq_mul, smul_eq_mul, mul_comm] using
    (Ring.choose_smul_choose z (n := n + 1) (k := 1) (by omega))

/-- These are the two derivatives of the original source primitive,
so their neck coefficients are the original -df row rather than a replacement row. -/
theorem branch_coeff_eq_negative_source_derivative (n : ℕ) :
    PowerSeries.coeff n inputBranch =
      -PowerSeries.derivative (PowerSeries.binomialSeries ℂ (-((n : ℂ) + 1 / 2))) ∧
    PowerSeries.coeff n detectorBranch =
      -PowerSeries.derivative (PowerSeries.binomialSeries ℂ ((n : ℂ) + 1 / 2)) := by
  constructor
  · rw [inputBranch_coeff, binomial_derivative]
    have he : -((n : ℂ) + 1 / 2) - 1 = -(n : ℂ) - 3 / 2 := by ring
    rw [he, map_neg, neg_mul, neg_neg]
  · rw [detectorBranch_coeff, binomial_derivative]
    have he : (n : ℂ) + 1 / 2 - 1 = (n : ℂ) - 1 / 2 := by ring
    rw [he, neg_mul]

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianBranchKernel
