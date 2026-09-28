/- GID: D5/S3/Observer/Linear/GaussianObservationDisintegration
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/GaussianObservationDisintegration
   mirror-E: none(waiver:general-gaussian-observation)
   anchors: []
   digest: Construct the actual Gaussian observation experiment and identify its conditional kernel with the inverse-precision posterior. -/

import D5.S3.Observer.Linear.GaussianObservationPrecision
import D5.S3.Observer.Linear.GaussianAffineDisintegration
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Tactic

/-!
The probability space is an actual multivariate Gaussian on the sum of the
state and noise coordinates. Both input laws and their independence are
proved. The residual covariance and its zero cross covariance with the data
are derived from the precision inverse. The posterior kernel is then proved
to disintegrate the actual joint observation law. No conditional-law,
independence, covariance-inverse or normalization conclusion is assumed.

Both beta and tau are strictly positive. Tau is noise precision, not noise
variance; tau=0 is not used as a fictitious finite-variance experiment.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Observer.Linear.GaussianObservationDisintegration

open Matrix MeasureTheory ProbabilityTheory WithLp
open D5.S3.Observer.Linear.GaussianObservationPrecision
open D5.S3.Observer.Linear.GaussianAffineDisintegration
open scoped ProbabilityTheory

variable {n p : Type*} [Fintype n] [DecidableEq n] [Fintype p] [DecidableEq p]

/-- Covariance of the actual independent state/noise input. -/
def ambientCov (β τ : ℝ) : Matrix (n ⊕ p) (n ⊕ p) ℝ :=
  Matrix.fromBlocks (β⁻¹ • (1 : Matrix n n ℝ)) 0 0 (τ⁻¹ • (1 : Matrix p p ℝ))

def signal : Matrix n (n ⊕ p) ℝ := Matrix.fromCols 1 0

def noise : Matrix p (n ⊕ p) ℝ := Matrix.fromCols 0 1

def observation (M : Matrix p n ℝ) : Matrix p (n ⊕ p) ℝ := Matrix.fromCols M 1

def gain (M : Matrix p n ℝ) (β τ : ℝ) : Matrix n p ℝ :=
  τ • (covariance M β τ * M.transpose)

/-- Innovation readout. Its first block is derived from the prior precision. -/
def innovation (M : Matrix p n ℝ) (β τ : ℝ) : Matrix n (n ⊕ p) ℝ :=
  Matrix.fromCols (β • covariance M β τ) (-gain M β τ)

theorem ambientCov_posDef (β τ : ℝ) (hβ : 0 < β) (hτ : 0 < τ) :
    (ambientCov (n := n) (p := p) β τ).PosDef := by
  have hd : ambientCov (n := n) (p := p) β τ =
      Matrix.diagonal (Sum.elim (fun _ : n => β⁻¹) (fun _ : p => τ⁻¹)) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [ambientCov, Matrix.fromBlocks, Matrix.diagonal, Matrix.one_apply]
  rw [hd, Matrix.posDef_diagonal_iff]
  intro i
  cases i with
  | inl i => exact inv_pos.mpr hβ
  | inr i => exact inv_pos.mpr hτ

/-- Multiply the innovation by the actual input covariance, cancelling only
strictly positive scalar precisions. -/
theorem innovation_times_cov (M : Matrix p n ℝ) (β τ : ℝ)
    (hβ : 0 < β) (hτ : 0 < τ) :
    innovation M β τ * ambientCov β τ =
      Matrix.fromCols (covariance M β τ) (-(covariance M β τ * M.transpose)) := by
  simp only [innovation, ambientCov, gain, Matrix.fromCols_mul_fromBlocks,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.mul_one, Matrix.neg_mul, smul_smul]
  simp [hβ.ne', hτ.ne', mul_comm]

/-- The original state is prediction plus residual, by the actual inverse equation. -/
theorem signal_reconstruction (M : Matrix p n ℝ) (β τ : ℝ)
    (hβ : 0 < β) (hτ : 0 < τ) :
    signal (n := n) (p := p) = gain M β τ * observation M + innovation M β τ := by
  have hleft : gain M β τ * M + β • covariance M β τ = 1 := by
    have hi := (precision_inverse M β τ hβ hτ.le).2
    simpa only [precision, gain, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_assoc, add_comm] using hi
  rw [observation, innovation, Matrix.mul_fromCols, Matrix.mul_one]
  ext i j
  rcases j with j | j
  · change (1 : Matrix n n ℝ) i j =
      (gain M β τ * M) i j + (β • covariance M β τ) i j
    exact (congrArg (fun A : Matrix n n ℝ => A i j) hleft).symm
  · simp [signal]

/-- Zero covariance with every data direction is derived, not postulated. -/
theorem innovation_data_covariance_zero (M : Matrix p n ℝ) (β τ : ℝ)
    (hβ : 0 < β) (hτ : 0 < τ) :
    innovation M β τ * ambientCov β τ * (observation M).transpose = 0 := by
  rw [innovation_times_cov M β τ hβ hτ, observation, Matrix.transpose_fromCols,
    Matrix.fromCols_mul_fromRows]
  simp

theorem innovation_signal_covariance (M : Matrix p n ℝ) (β τ : ℝ)
    (hβ : 0 < β) (hτ : 0 < τ) :
    innovation M β τ * ambientCov β τ * (signal (n := n) (p := p)).transpose =
      covariance M β τ := by
  rw [innovation_times_cov M β τ hβ hτ, signal, Matrix.transpose_fromCols,
    Matrix.fromCols_mul_fromRows]
  simp

/-- The innovation covariance is precisely the inverse precision. -/
theorem innovation_covariance (M : Matrix p n ℝ) (β τ : ℝ)
    (hβ : 0 < β) (hτ : 0 < τ) :
    innovation M β τ * ambientCov β τ * (innovation M β τ).transpose =
      covariance M β τ := by
  have h := innovation_signal_covariance M β τ hβ hτ
  rw [signal_reconstruction M β τ hβ hτ, Matrix.transpose_add, Matrix.transpose_mul,
    Matrix.mul_add, ← Matrix.mul_assoc,
    innovation_data_covariance_zero M β τ hβ hτ, Matrix.zero_mul, zero_add] at h
  exact h

/-- A probability measure on all state and noise coordinates, without truncation. -/
def inputLaw (β τ : ℝ) : Measure (E (n ⊕ p)) :=
  multivariateGaussian 0 (ambientCov β τ)

instance inputLaw_probability (β τ : ℝ) :
    IsProbabilityMeasure (inputLaw (n := n) (p := p) β τ) := by
  unfold inputLaw
  infer_instance

/-- This constructed input really has the specified independent Gaussian factors. -/
theorem input_factors (β τ : ℝ) (hβ : 0 < β) (hτ : 0 < τ) :
    (inputLaw (n := n) (p := p) β τ).map (action signal) =
        multivariateGaussian 0 (β⁻¹ • (1 : Matrix n n ℝ)) ∧
    (inputLaw (n := n) (p := p) β τ).map (action noise) =
        multivariateGaussian 0 (τ⁻¹ • (1 : Matrix p p ℝ)) ∧
    IndepFun (action (signal (n := n) (p := p))) (action noise) (inputLaw β τ) := by
  have hd := (ambientCov_posDef (n := n) (p := p) β τ hβ hτ).posSemidef
  refine ⟨?_, ?_, ?_⟩
  · simpa [inputLaw, signal, ambientCov, Matrix.transpose_fromCols,
      Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows] using
      map_gaussian (0 : E (n ⊕ p)) (ambientCov β τ) hd (signal (n := n) (p := p))
  · simpa [inputLaw, noise, ambientCov, Matrix.transpose_fromCols,
      Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows] using
      map_gaussian (0 : E (n ⊕ p)) (ambientCov β τ) hd (noise (n := n) (p := p))
  · apply independent_actions 0 (ambientCov β τ) hd
    simp [signal, noise, ambientCov, Matrix.transpose_fromCols,
      Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows]

/-- The data are exactly M X plus the independent input noise. -/
theorem observation_apply (M : Matrix p n ℝ) (z : E (n ⊕ p)) :
    action (observation M) z = action M (action signal z) + action noise z := by
  simp [action_apply, observation, signal, noise, Matrix.fromCols_mulVec]

def dataLaw (M : Matrix p n ℝ) (β τ : ℝ) : Measure (E p) :=
  (inputLaw β τ).map (action (observation M))

instance dataLaw_probability (M : Matrix p n ℝ) (β τ : ℝ) :
    IsProbabilityMeasure (dataLaw M β τ) := by
  unfold dataLaw
  exact (inputLaw β τ).isProbabilityMeasure_map (by fun_prop)

/-- Coordinates of this joint law are (observed data, original signal). -/
def jointLaw (M : Matrix p n ℝ) (β τ : ℝ) : Measure (E p × E n) :=
  (inputLaw β τ).map (fun z => (action (observation M) z, action signal z))

/-- The explicit posterior kernel, before proving it is conditional. -/
def posteriorKernel (M : Matrix p n ℝ) (β τ : ℝ) : Kernel (E p) (E n) :=
  translatedKernel (action (gain M β τ)) (multivariateGaussian 0 (covariance M β τ))

instance posteriorKernel_markov (M : Matrix p n ℝ) (β τ : ℝ) :
    IsMarkovKernel (posteriorKernel M β τ) := by
  unfold posteriorKernel
  infer_instance

theorem gain_eq_center (M : Matrix p n ℝ) (β τ : ℝ) (y : E p) :
    action (gain M β τ) y = toLp 2 (center M β τ (ofLp y)) := by
  simp only [action_apply, gain, center, score, Matrix.smul_mulVec,
    Matrix.mulVec_smul, Matrix.mulVec_mulVec]

/-- The kernel agrees pointwise with the preceding module's Gaussian candidate. -/
theorem posteriorKernel_eq_candidate (M : Matrix p n ℝ) (β τ : ℝ) (y : E p) :
    posteriorKernel M β τ y = candidateLaw M β τ (ofLp y) := by
  rw [posteriorKernel, translatedKernel_apply, translate_gaussian, add_zero, gain_eq_center]
  rfl

/-- Complete conditional-law identity for arbitrary rectangular sensors.
The full joint law equals data marginal times the constructed posterior kernel. -/
theorem posterior_disintegration (M : Matrix p n ℝ) (β τ : ℝ)
    (hβ : 0 < β) (hτ : 0 < τ) :
    jointLaw M β τ = (dataLaw M β τ) ⊗ₘ posteriorKernel M β τ := by
  have hd := (ambientCov_posDef (n := n) (p := p) β τ hβ hτ).posSemidef
  have hind : IndepFun (action (innovation M β τ)) (action (observation M))
      (inputLaw β τ) :=
    independent_actions 0 (ambientCov β τ) hd _ _
      (innovation_data_covariance_zero M β τ hβ hτ)
  have hlaw : (inputLaw β τ).map (action (innovation M β τ)) =
      multivariateGaussian 0 (covariance M β τ) := by
    simpa only [inputLaw, map_zero, innovation_covariance M β τ hβ hτ] using
      map_gaussian (0 : E (n ⊕ p)) (ambientCov β τ) hd (innovation M β τ)
  apply joint_eq_compProd_of_independent_residual
    (inputLaw β τ) (action signal) (action (observation M))
    (action (innovation M β τ)) (by fun_prop) (by fun_prop)
    (action (gain M β τ)) (multivariateGaussian 0 (covariance M β τ))
    hind.symm hlaw
  intro z
  have hm := congrArg (fun A : Matrix n (n ⊕ p) ℝ => action A z)
    (signal_reconstruction M β τ hβ hτ)
  simpa only [action_add, ContinuousLinearMap.add_apply, ← action_comp,
    ContinuousLinearMap.comp_apply] using hm

theorem jointLaw_fst (M : Matrix p n ℝ) (β τ : ℝ) :
    (jointLaw M β τ).fst = dataLaw M β τ := by
  unfold jointLaw dataLaw Measure.fst
  rw [Measure.map_map measurable_fst (by fun_prop)]
  rfl

/-- A regular conditional kernel for the actual joint probability measure. -/
theorem posterior_isCondKernel (M : Matrix p n ℝ) (β τ : ℝ)
    (hβ : 0 < β) (hτ : 0 < τ) :
    (jointLaw M β τ).IsCondKernel (posteriorKernel M β τ) where
  disintegrate := by rw [jointLaw_fst, ← posterior_disintegration M β τ hβ hτ]

#print axioms input_factors
#print axioms innovation_covariance
#print axioms posteriorKernel_eq_candidate
#print axioms posterior_disintegration
#print axioms posterior_isCondKernel
end D5.S3.Observer.Linear.GaussianObservationDisintegration
