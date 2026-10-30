/- GID: D5/S3/Quantum/Recovery/WernerHolevoBayesianFeedbackAdvantage
   generality: I
   mirror-B: D5/B/S3/Quantum/Recovery/WernerHolevoBayesianFeedbackAdvantage
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Bayesian feedback beats Markovian feedback for the qutrit Werner--Holevo channel. -/

import D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricQubitWitnessSpectrum
import D5.S3.Weil.BurnolGram.QuantitativeMultiOrbitWeilNegativeCertificate
import D5.S3.Quantum.QuantumChannels.NoisyWernerHolevoLindbladEmbedding
import D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction
import D5.S3.Quantum.Recovery.ActualChannelAlgebra
import D5.S3.QuantumChannels.UnitaryKrausMixingInvariance
import D5.S3.Quantum.Matrix.LinPsiMap.ReductionBlock

/-! The qutrit Werner--Holevo channel separates Bayesian and Markovian feedback. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricQubitWitnessSpectrum (qform)
open D5.S3.Weil.BurnolGram.QuantitativeMultiOrbitWeilNegativeCertificate
  (finiteComplexEnergy)
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)
open D5.S3.Quantum.QuantumChannels.NoisyWernerHolevoLindbladEmbedding (wernerHolevo)

namespace D5.S3.Quantum.Recovery.WernerHolevoBayesianFeedbackAdvantage

/-- A finite Kraus family represents the Werner--Holevo channel. -/
def IsKrausDecomposition {m : ℕ} (k : Fin m → Matrix (Fin 3) (Fin 3) ℂ) : Prop :=
  ∀ x : Matrix (Fin 3) (Fin 3) ℂ, ∑ a, k a * x * (k a)ᴴ = wernerHolevo 1 x

/-- The two-step Markovian feedback fidelity from the source. -/
def markovFidelity {m₁ m₂ : ℕ} (k₁ : Fin m₁ → Matrix (Fin 3) (Fin 3) ℂ)
    (k₂ : Fin m₂ → Matrix (Fin 3) (Fin 3) ℂ) : ℝ :=
  (1 / 9 : ℝ) * ∑ a, ∑ b,
    (((CFC.abs (k₂ b) * CFC.abs (k₁ a)).trace).re) ^ 2

/-- The two-step Bayesian feedback fidelity from the source. -/
def bayesFidelity {m₁ m₂ : ℕ} (k₁ : Fin m₁ → Matrix (Fin 3) (Fin 3) ℂ)
    (k₂ : Fin m₂ → Matrix (Fin 3) (Fin 3) ℂ) : ℝ :=
  (1 / 9 : ℝ) * ∑ a, ∑ b,
    (traceNorm (k₂ b * CFC.abs (k₁ a))) ^ 2

private def crossProduct (z : Fin 3 → ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  LinearMap.toMatrix' (_root_.crossProduct z)

private def canonicalKraus (i : Fin 3) : Matrix (Fin 3) (Fin 3) ℂ :=
  ((Real.sqrt 2)⁻¹ : ℂ) • crossProduct ((Pi.single i (1 : ℂ) : Fin 3 → ℂ))

private def rotationVector (j : Fin 3) : Fin 3 → ℂ :=
  if j.val = 0 then ![((2 : ℂ) / 3), (2 : ℂ) / 3, (-1 : ℂ) / 3]
  else if j.val = 1 then ![((-1 : ℂ) / 3), (2 : ℂ) / 3, (2 : ℂ) / 3]
  else ![((2 : ℂ) / 3), (-1 : ℂ) / 3, (2 : ℂ) / 3]

private def rotationKraus (j : Fin 3) : Matrix (Fin 3) (Fin 3) ℂ :=
  ((Real.sqrt 2)⁻¹ : ℂ) • crossProduct (rotationVector j)

private theorem quad_identity (K : Matrix (Fin 3) (Fin 3) ℂ) (x : Fin 3 → ℂ) :
    star (star x) ⬝ᵥ ((K * Matrix.vecMulVec x (star x) * Kᴴ) *ᵥ (star x)) =
      qform K x * star (qform K x) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_conjTranspose]
  simp only [star_star]
  have h := D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction.quadratic_projector
    (star x) (K *ᵥ x)
  simpa only [star_star, D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity,
    qform, Complex.star_def, Complex.mul_conj] using h

private theorem quad_sum_zero {m : ℕ} (K : Fin m → Matrix (Fin 3) (Fin 3) ℂ)
    (hK : IsKrausDecomposition K) (x : Fin 3 → ℂ) : ∑ a, ‖qform (K a) x‖ ^ 2 = 0 := by
  have he := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ =>
      star (star x) ⬝ᵥ (M *ᵥ (star x)))
    (hK (Matrix.vecMulVec x (star x)))
  have hleft : star (star x) ⬝ᵥ ((∑ a, K a * Matrix.vecMulVec x (star x) * (K a)ᴴ) *ᵥ (star x)) =
      ∑ a, qform (K a) x * star (qform (K a) x) := by
    rw [Matrix.sum_mulVec, dotProduct_sum]
    apply Finset.sum_congr rfl
    intro a ha
    exact quad_identity (K a) x
  rw [hleft] at he
  have hright : star (star x) ⬝ᵥ (wernerHolevo 1 (Matrix.vecMulVec x (star x)) *ᵥ (star x)) = 0 :=
      by
    unfold wernerHolevo
    simp [Matrix.trace, Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply,
        Matrix.transpose_apply, Fin.sum_univ_succ, Complex.star_def,
      Complex.conj_ofReal]
    ring
  rw [hright] at he
  calc
    ∑ a, ‖qform (K a) x‖ ^ 2 = ∑ a, (qform (K a) x * star (qform (K a) x)).re := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [Complex.mul_re]
    _ = (∑ a, qform (K a) x * star (qform (K a) x)).re := by
      simpa using (map_sum (Complex.re : ℂ → ℝ)
        (fun a => qform (K a) x * star (qform (K a) x)) Finset.univ).symm
    _ = 0 := by rw [he]; norm_num

private theorem quad_zero {m : ℕ} (K : Fin m → Matrix (Fin 3) (Fin 3) ℂ)
    (hK : IsKrausDecomposition K) (x : Fin 3 → ℂ) (a : Fin m) : qform (K a) x = 0 := by
  have hs := quad_sum_zero K hK x
  have hz := (Fintype.sum_eq_zero_iff_of_nonneg (fun b =>
    sq_nonneg (‖qform (K b) x‖))).mp hs
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp (congrFun hz a))

private theorem diag_zero {m : ℕ} (K : Fin m → Matrix (Fin 3) (Fin 3) ℂ)
    (hK : IsKrausDecomposition K) (a : Fin m) (i : Fin 3) : K a i i = 0 := by
  rw [← Matrix.toBilin'_single (K a) i i, Matrix.toBilin'_apply']
  exact quad_zero K hK _ a

private theorem offdiag_zero {m : ℕ} (K : Fin m → Matrix (Fin 3) (Fin 3) ℂ)
    (hK : IsKrausDecomposition K) (a : Fin m) (i j : Fin 3) :
    K a i j + K a j i = 0 := by
  have hAlt : (Matrix.toBilin' (K a)).IsAlt := by
    intro x
    rw [Matrix.toBilin'_apply']
    exact quad_zero K hK x a
  have hh := hAlt.neg_eq (Pi.single i 1) (Pi.single j 1)
  simp only [Matrix.toBilin'_single] at hh
  rw [← hh, add_neg_cancel]

private theorem tp {m : ℕ} (K : Fin m → Matrix (Fin 3) (Fin 3) ℂ)
    (hK : IsKrausDecomposition K) : ∑ a, (K a)ᴴ * K a =
      (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  apply Original8340Global.kraus_normalization_from_actual_trace K
  intro X
  rw [hK X, wernerHolevo]
  simp [Matrix.trace_add, Matrix.trace_smul,
    Matrix.trace_transpose, Matrix.trace_one]
  ring

private theorem reprK {m : ℕ} (K : Fin m → Matrix (Fin 3) (Fin 3) ℂ)
    (hK : IsKrausDecomposition K) : ∃ z : Fin m → Fin 3 → ℂ,
      ∀ a, K a = ((Real.sqrt 2)⁻¹ : ℂ) • crossProduct (z a) := by
  let z : Fin m → Fin 3 → ℂ := fun a => (Real.sqrt 2 : ℂ) •
    ![K a 2 1, K a 0 2, K a 1 0]
  refine ⟨z, ?_⟩
  intro a
  rw [crossProduct.eq_1]
  ext i j
  have hd := diag_zero K hK a
  have h01 := offdiag_zero K hK a (0 : Fin 3) 1
  have h02 := offdiag_zero K hK a (0 : Fin 3) 2
  have h12 := offdiag_zero K hK a (1 : Fin 3) 2
  have h01' := eq_neg_of_add_eq_zero_left h01
  have h02' := eq_neg_of_add_eq_zero_left h02
  have h12' := eq_neg_of_add_eq_zero_left h12
  fin_cases i <;> fin_cases j <;>
    simp [z, crossProduct, LinearMap.toMatrix'_apply, cross_apply, Pi.single_apply, hd, h01, h02,
        h12, h01', h02', h12']

private theorem frameK {m : ℕ} (K : Fin m → Matrix (Fin 3) (Fin 3) ℂ)
    (hK : IsKrausDecomposition K) (z : Fin m → Fin 3 → ℂ)
    (hr : ∀ a, K a = ((Real.sqrt 2)⁻¹ : ℂ) • crossProduct (z a)) :
    (∑ a, (Matrix.vecMulVec (z a) (star (z a)))) =
      (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  have htp := tp K hK
  simp_rw [hr] at htp
  have hs : ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = (1 / 2 : ℂ) := by
    simpa only [pow_two, one_div] using
      D5.S3.QuantumBounds.CHSHWitness.complex_sqrt_two_inv_mul_self
  have h00 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 0 0) htp
  have h11 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 1 1) htp
  have h22 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 2 2) htp
  have h01 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 0 1) htp
  have h02 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 0 2) htp
  have h12 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 1 2) htp
  simp [crossProduct, LinearMap.toMatrix'_apply, cross_apply, Pi.single_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply,
    Matrix.sum_apply, Matrix.one_apply, Fin.sum_univ_succ,
    Complex.star_def] at h00 h11 h22 h01 h02 h12
  simp only [← mul_assoc] at h00 h11 h22 h01 h02 h12
  have hs' : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
    simpa [pow_two] using hs
  simp [hs'] at h00 h11 h22 h01 h02 h12
  simp only [mul_add] at h00 h11 h22
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h00
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h11
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h22
  simp_rw [← Finset.mul_sum] at h00 h11 h22
  simp_rw [mul_assoc] at h01 h02 h12
  rw [← Finset.mul_sum] at h01 h02 h12
  have hz0' : ∑ x, (starRingEnd ℂ) (z x 0) * z x 0 = 1 := by
    linear_combination h11 + h22 - h00
  have hz1' : ∑ x, (starRingEnd ℂ) (z x 1) * z x 1 = 1 := by
    linear_combination h00 + h22 - h11
  have hz2' : ∑ x, (starRingEnd ℂ) (z x 2) * z x 2 = 1 := by
    linear_combination h00 + h11 - h22
  have hz01' : ∑ x, (starRingEnd ℂ) (z x 1) * z x 0 = 0 := by
    linear_combination (2 : ℂ) * h01
  have hz02' : ∑ x, (starRingEnd ℂ) (z x 2) * z x 0 = 0 := by
    linear_combination (2 : ℂ) * h02
  have hz12' : ∑ x, (starRingEnd ℂ) (z x 2) * z x 1 = 0 := by
    linear_combination (2 : ℂ) * h12
  have hz0 : ∑ x, z x 0 * (starRingEnd ℂ) (z x 0) = 1 := by
    simpa [mul_comm] using hz0'
  have hz1 : ∑ x, z x 1 * (starRingEnd ℂ) (z x 1) = 1 := by
    simpa [mul_comm] using hz1'
  have hz2 : ∑ x, z x 2 * (starRingEnd ℂ) (z x 2) = 1 := by
    simpa [mul_comm] using hz2'
  have hz01 : ∑ x, z x 0 * (starRingEnd ℂ) (z x 1) = 0 := by
    simpa [mul_comm] using hz01'
  have hz02 : ∑ x, z x 0 * (starRingEnd ℂ) (z x 2) = 0 := by
    simpa [mul_comm] using hz02'
  have hz12 : ∑ x, z x 1 * (starRingEnd ℂ) (z x 2) = 0 := by
    simpa [mul_comm] using hz12'
  have hz10 : ∑ x, z x 1 * (starRingEnd ℂ) (z x 0) = 0 := by
    have h := congrArg star hz01
    simpa [star_sum, star_mul, star_star, mul_comm] using h
  have hz20 : ∑ x, z x 2 * (starRingEnd ℂ) (z x 0) = 0 := by
    have h := congrArg star hz02
    simpa [star_sum, star_mul, star_star, mul_comm] using h
  have hz21 : ∑ x, z x 2 * (starRingEnd ℂ) (z x 1) = 0 := by
    have h := congrArg star hz12
    simpa [star_sum, star_mul, star_star, mul_comm] using h
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [Matrix.sum_apply, Matrix.vecMulVec_apply] using hz0
  · simpa [Matrix.sum_apply, Matrix.vecMulVec_apply] using hz01
  · simpa [Matrix.sum_apply, Matrix.vecMulVec_apply] using hz02
  · simpa [Matrix.sum_apply, Matrix.vecMulVec_apply] using hz10
  · simpa [Matrix.sum_apply, Matrix.vecMulVec_apply] using hz1
  · simpa [Matrix.sum_apply, Matrix.vecMulVec_apply] using hz12
  · simpa [Matrix.sum_apply, Matrix.vecMulVec_apply] using hz20
  · simpa [Matrix.sum_apply, Matrix.vecMulVec_apply] using hz21
  · simpa [Matrix.sum_apply, Matrix.vecMulVec_apply] using hz2

private theorem kraus_classification {m : ℕ} (K : Fin m → Matrix (Fin 3) (Fin 3) ℂ)
    (hK : IsKrausDecomposition K) :
    ∃ z : Fin m → Fin 3 → ℂ,
      (∀ a, K a = ((Real.sqrt 2)⁻¹ : ℂ) • crossProduct (z a)) ∧
        (∑ a, Matrix.vecMulVec (z a) (star (z a))) =
          (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  obtain ⟨z, hz⟩ := reprK K hK
  exact ⟨z, hz, frameK K hK z hz⟩

private theorem complement_square {n : Type} [Fintype n] [DecidableEq n]
    (c : ℂ) (V : Matrix n n ℂ) (hV : V * V = c • V) :
    (c • (1 : Matrix n n ℂ) - V) * (c • (1 : Matrix n n ℂ) - V) =
      c • (c • (1 : Matrix n n ℂ) - V) := by
  simp only [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, hV, smul_smul]
  module

private theorem complement_scale {n : Type} [DecidableEq n]
    (r c : ℂ) (hr2 : r ^ 2 = c) (V : Matrix n n ℂ) :
    r • (1 : Matrix n n ℂ) - r⁻¹ • V = r⁻¹ • (c • (1 : Matrix n n ℂ) - V) := by
  subst c
  by_cases hr : r = 0
  · simp [hr]
  · simp only [smul_sub, smul_smul]
    rw [show r⁻¹ * r ^ 2 = r by field_simp [hr]]

private theorem complement_root {n : Type} [Fintype n] [DecidableEq n]
    (c : ℂ) (r : ℝ) (hrpos : 0 < r) (hr : (r : ℂ) ≠ 0) (hr2 : (r : ℂ) ^ 2 = c)
    (V : Matrix n n ℂ) (hV : V * V = c • V)
    (hpos : (c • (1 : Matrix n n ℂ) - V).PosSemidef) :
    CFC.sqrt (c • (1 : Matrix n n ℂ) - V) =
      (r : ℂ) • (1 : Matrix n n ℂ) - ((r⁻¹ : ℝ) : ℂ) • V := by
  let H := c • (1 : Matrix n n ℂ) - V
  let S := (r : ℂ) • (1 : Matrix n n ℂ) - (r : ℂ)⁻¹ • V
  have hsq : H * H = c • H := complement_square c V hV
  have hs : S = (r : ℂ)⁻¹ • H := by
    dsimp [S, H]
    exact complement_scale (r : ℂ) c hr2 V
  have hss : S * S = H := by
    rw [hs, Matrix.smul_mul, Matrix.mul_smul, hsq]
    have he : ((r : ℂ)⁻¹ * (r : ℂ)⁻¹) * c = 1 := by
      rw [← hr2]
      field_simp [hr]
    simp only [smul_smul]
    rw [← mul_assoc, he, one_smul]
  have hsp : S.PosSemidef := by
    rw [hs]
    apply Matrix.nonneg_iff_posSemidef.mp
    have hp := hpos.smul (show (0 : ℝ) ≤ r⁻¹ by positivity)
    have heq : (r : ℂ)⁻¹ • H = (r⁻¹ : ℝ) • H := by
      ext i j
      simp [Complex.real_smul]
    rw [heq]
    exact hp.nonneg
  have hinv : ((r⁻¹ : ℝ) : ℂ) = (r : ℂ)⁻¹ := by norm_cast
  simpa [S, hinv] using (CFC.sqrt_unique hss hsp.nonneg)

private theorem vec_trace (z : Fin 3 → ℂ) :
    (Matrix.vecMulVec z (star z)).trace = (finiteComplexEnergy z : ℂ) := by
  simpa only [← Complex.ofReal_pow, EuclideanSpace.norm_sq_eq, Complex.sq_norm,
      finiteComplexEnergy, WithLp.ofLp_toLp] using
    D5.S3.Quantum.Entanglement.UniversalReplacementCapacityGrowth.pure_trace (WithLp.toLp 2 z)

private theorem abs_crossProduct (z : Fin 3 → ℂ) :
    CFC.abs (((Real.sqrt 2)⁻¹ : ℂ) • crossProduct z) =
      if z = 0 then 0 else
        ((Real.sqrt 2)⁻¹ : ℂ) •
          ((‖(WithLp.toLp 2 z : EuclideanSpace ℂ (Fin 3))‖ : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) -
            ((‖(WithLp.toLp 2 z : EuclideanSpace ℂ (Fin 3))‖)⁻¹ : ℂ) • Matrix.vecMulVec z (star z))
                := by
  by_cases hz : z = 0
  · subst z
    have hcp : crossProduct (0 : Fin 3 → ℂ) = 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [crossProduct, LinearMap.toMatrix'_apply, cross_apply,
          Pi.single_apply]
    rw [hcp]
    simp [CFC.abs]
  · have hAA : (crossProduct z)ᴴ * crossProduct z =
        (finiteComplexEnergy z : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) - Matrix.vecMulVec z (star z)
            := by
      have hstar (v : Fin 3 → ℂ) : star (_root_.crossProduct z v) =
          _root_.crossProduct (star z) (star v) := by
        ext k
        fin_cases k <;> simp [cross_apply, star_sub, star_mul, mul_comm]
      have he : star z ⬝ᵥ z = (finiteComplexEnergy z : ℂ) := by
        rw [dotProduct_comm, ← Matrix.trace_vecMulVec, vec_trace]
      ext i j
      change (star (_root_.crossProduct z (Pi.single i 1)) ⬝ᵥ
        _root_.crossProduct z (Pi.single j 1)) = _
      rw [hstar, cross_dot_cross]
      simp [Pi.star_single, he, Matrix.vecMulVec_apply, Matrix.one_apply,
        Pi.single_apply, mul_ite, eq_comm, mul_comm]
    have hV : Matrix.vecMulVec z (star z) * Matrix.vecMulVec z (star z) =
        (finiteComplexEnergy z : ℂ) • Matrix.vecMulVec z (star z) := by
      rw [Matrix.vecMulVec_mul_vecMulVec]
      rw [dotProduct_comm (star z) z, ← Matrix.trace_vecMulVec, vec_trace]
      exact Matrix.vecMulVec_smul _ _ _
    have hr : (‖(WithLp.toLp 2 z : EuclideanSpace ℂ (Fin 3))‖ : ℂ) ≠ 0 := by
      have h : 0 < ‖(WithLp.toLp 2 z : EuclideanSpace ℂ (Fin 3))‖ :=
        norm_pos_iff.mpr (by simpa using hz)
      exact_mod_cast ne_of_gt h
    have hr2 : (‖(WithLp.toLp 2 z : EuclideanSpace ℂ (Fin 3))‖ : ℂ) ^ 2 = (finiteComplexEnergy z :
        ℂ) := by
      exact_mod_cast (show ‖(WithLp.toLp 2 z : EuclideanSpace ℂ (Fin 3))‖ ^ 2 =
          finiteComplexEnergy z by
        simp [EuclideanSpace.norm_sq_eq, finiteComplexEnergy, Complex.sq_norm])
    have hpos : ((finiteComplexEnergy z : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) -
        Matrix.vecMulVec z (star z)).PosSemidef := by
      rw [← hAA]
      exact Matrix.posSemidef_conjTranspose_mul_self _
    have hroot := complement_root (finiteComplexEnergy z : ℂ) (‖(WithLp.toLp 2 z : EuclideanSpace ℂ
        (Fin 3))‖) (norm_pos_iff.mpr (by simpa using hz))
      hr hr2 (Matrix.vecMulVec z (star z)) hV hpos
    have hs := CFC.abs_smul ((Real.sqrt 2)⁻¹ : ℂ) (crossProduct z)
    change CFC.abs (((Real.sqrt 2)⁻¹ : ℂ) • crossProduct z) =
      ‖((Real.sqrt 2)⁻¹ : ℂ)‖ • CFC.abs (crossProduct z) at hs
    dsimp [CFC.abs] at hs ⊢
    simp only [Matrix.star_eq_conjTranspose] at hs ⊢
    rw [hAA, hroot] at hs
    have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    have hnorm : ‖((Real.sqrt 2)⁻¹ : ℂ)‖ = (Real.sqrt 2)⁻¹ := by
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsqrt]
    rw [hnorm] at hs
    simp only [hz, if_false]
    convert hs using 1
    ext i j
    simp [Complex.real_smul]

private theorem vec_product_trace (w z : Fin 3 → ℂ) :
    (Matrix.vecMulVec w (star w) * Matrix.vecMulVec z (star z)).trace =
      (star w ⬝ᵥ z) * (star z ⬝ᵥ w) := by
  change (D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity w *
    D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity z).trace = _
  rw [D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction.trace_projector_overlap,
    star_dotProduct z w, Complex.star_def, Complex.mul_conj]

private theorem complement_trace_product (u v : ℂ)
    (V W : Matrix (Fin 3) (Fin 3) ℂ) :
    ((u • (1 : Matrix (Fin 3) (Fin 3) ℂ) - u⁻¹ • V) *
        (v • (1 : Matrix (Fin 3) (Fin 3) ℂ) - v⁻¹ • W)).trace =
      3 * u * v - u * v⁻¹ * W.trace - u⁻¹ * v * V.trace +
        u⁻¹ * v⁻¹ * (V * W).trace := by
  simp only [sub_mul, mul_sub, smul_mul, mul_smul, Matrix.one_mul,
    Matrix.mul_one, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul,
    Matrix.trace_one, Matrix.smul_mul, Matrix.mul_smul]
  norm_num [Fintype.card_fin]
  ring

private theorem inner_product_re (w z : Fin 3 → ℂ) :
    ((star w ⬝ᵥ z) * (star z ⬝ᵥ w)).re = Complex.normSq (star w ⬝ᵥ z) := by
  rw [star_dotProduct z w, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]

private theorem abs_pair_trace (w z : Fin 3 → ℂ) (hw : w ≠ 0) (hz : z ≠ 0) :
    (CFC.abs (((Real.sqrt 2)⁻¹ : ℂ) • crossProduct w) *
        CFC.abs (((Real.sqrt 2)⁻¹ : ℂ) • crossProduct z)).trace =
      (1 / 2 : ℂ) *
        ((‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin 3))‖ : ℂ) * (‖(WithLp.toLp 2 z : EuclideanSpace
            ℂ (Fin 3))‖ : ℂ) +
          ((star w ⬝ᵥ z) * (star z ⬝ᵥ w)) /
            ((‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin 3))‖ : ℂ) * (‖(WithLp.toLp 2 z :
                EuclideanSpace ℂ (Fin 3))‖ : ℂ))) := by
  have hs : ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = (1 / 2 : ℂ) := by
    simpa only [pow_two, one_div] using
      D5.S3.QuantumBounds.CHSHWitness.complex_sqrt_two_inv_mul_self
  have hqw : (‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin 3))‖ : ℂ) ^ 2 = (finiteComplexEnergy w : ℂ)
      := by
    exact_mod_cast (show ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin 3))‖ ^ 2 =
        finiteComplexEnergy w by
      simp [EuclideanSpace.norm_sq_eq, finiteComplexEnergy, Complex.sq_norm])
  have hqz : (‖(WithLp.toLp 2 z : EuclideanSpace ℂ (Fin 3))‖ : ℂ) ^ 2 = (finiteComplexEnergy z : ℂ)
      := by
    exact_mod_cast (show ‖(WithLp.toLp 2 z : EuclideanSpace ℂ (Fin 3))‖ ^ 2 =
        finiteComplexEnergy z by
      simp [EuclideanSpace.norm_sq_eq, finiteComplexEnergy, Complex.sq_norm])
  have huw : (‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin 3))‖ : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (norm_pos_iff.mpr (show
      (WithLp.toLp 2 w : EuclideanSpace ℂ (Fin 3)) ≠ 0 by simpa using hw)))
  have huz : (‖(WithLp.toLp 2 z : EuclideanSpace ℂ (Fin 3))‖ : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (norm_pos_iff.mpr (show
      (WithLp.toLp 2 z : EuclideanSpace ℂ (Fin 3)) ≠ 0 by simpa using hz)))
  rw [abs_crossProduct w, abs_crossProduct z]
  simp only [if_neg hw, if_neg hz]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_smul]
  have hs' : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = (1 / 2 : ℂ) := by
    simpa [pow_two] using hs
  rw [hs']
  rw [complement_trace_product, vec_trace, vec_trace, vec_product_trace]
  rw [← hqw, ← hqz]

  field_simp [huw, huz]
  change 2 * (‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin 3))‖ : ℂ) * (‖(WithLp.toLp 2 z :
      EuclideanSpace ℂ (Fin 3))‖ : ℂ) *
      ((1 / 2 : ℂ) *
        (((‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin 3))‖ : ℂ) ^ 2 * (‖(WithLp.toLp 2 z :
            EuclideanSpace ℂ (Fin 3))‖ : ℂ) ^ 2 * (3 - 1 - 1) +
          (star w ⬝ᵥ z) * (star z ⬝ᵥ w)) /
          ((‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin 3))‖ : ℂ) * (‖(WithLp.toLp 2 z :
              EuclideanSpace ℂ (Fin 3))‖ : ℂ)))) =
    (‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin 3))‖ : ℂ) ^ 2 * (‖(WithLp.toLp 2 z : EuclideanSpace ℂ
        (Fin 3))‖ : ℂ) ^ 2 +
      (star w ⬝ᵥ z) * (star z ⬝ᵥ w)
  field_simp [huw, huz]
  ring

private theorem div_real_re (c : ℂ) (x y : ℝ) :
    (c / ((x : ℂ) * (y : ℂ))).re = c.re / (x * y) := by
  rw [← Complex.ofReal_mul, Complex.div_ofReal_re]


private theorem inner_cauchy (w z : Fin 3 → ℂ) :
    Complex.normSq (star w ⬝ᵥ z) ≤ finiteComplexEnergy w * finiteComplexEnergy z := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 w : EuclideanSpace ℂ (Fin 3)) (WithLp.toLp 2
      z)
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp,
    dotProduct_comm z (star w), ← Complex.normSq_eq_norm_sq, mul_pow,
    EuclideanSpace.norm_sq_eq, Complex.sq_norm, finiteComplexEnergy] using h2

private theorem abs_pair_bound (w z : Fin 3 → ℂ) :
    (((CFC.abs (((Real.sqrt 2)⁻¹ : ℂ) • crossProduct w) *
        CFC.abs (((Real.sqrt 2)⁻¹ : ℂ) • crossProduct z)).trace).re) ^ 2 ≤
      (finiteComplexEnergy w * finiteComplexEnergy z + 3 * Complex.normSq (star w ⬝ᵥ z)) / 4 := by
  by_cases hw : w = 0
  · subst w
    have hzero : ((Real.sqrt 2)⁻¹ : ℂ) • crossProduct (0 : Fin 3 → ℂ) = 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [crossProduct, LinearMap.toMatrix'_apply, cross_apply,
          Pi.single_apply]
    rw [hzero]
    simp [CFC.abs, finiteComplexEnergy]
  by_cases hz : z = 0
  · subst z
    have hzero : ((Real.sqrt 2)⁻¹ : ℂ) • crossProduct (0 : Fin 3 → ℂ) = 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [crossProduct, LinearMap.toMatrix'_apply, cross_apply,
          Pi.single_apply]
    rw [hzero]
    simp [CFC.abs, finiteComplexEnergy]
  have htrace := abs_pair_trace w z hw hz
  rw [htrace]
  simp only [Complex.mul_re, Complex.div_re]
  norm_num [Complex.normSq_apply]
  have hdiv := div_real_re (star w ⬝ᵥ z * star z ⬝ᵥ w)
    (‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin 3))‖) (‖(WithLp.toLp 2 z : EuclideanSpace ℂ (Fin
        3))‖)
  rw [hdiv, inner_product_re]
  rw [← Complex.normSq_apply]
  have hu : 0 < ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin 3))‖ :=
    norm_pos_iff.mpr (by simpa using hw)
  have hv : 0 < ‖(WithLp.toLp 2 z : EuclideanSpace ℂ (Fin 3))‖ :=
    norm_pos_iff.mpr (by simpa using hz)
  have hqw : finiteComplexEnergy w = ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin 3))‖ ^ 2 := by
    simp [EuclideanSpace.norm_sq_eq, finiteComplexEnergy, Complex.sq_norm]
  have hqz : finiteComplexEnergy z = ‖(WithLp.toLp 2 z : EuclideanSpace ℂ (Fin 3))‖ ^ 2 := by
    simp [EuclideanSpace.norm_sq_eq, finiteComplexEnergy, Complex.sq_norm]
  have hc : Complex.normSq (star w ⬝ᵥ z) ≤
      ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin 3))‖ ^ 2 * ‖(WithLp.toLp 2 z : EuclideanSpace ℂ (Fin
          3))‖ ^ 2 := by
    simpa [hqw, hqz] using inner_cauchy w z
  have huv : 0 < ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin 3))‖ * ‖(WithLp.toLp 2 z : EuclideanSpace
      ℂ (Fin 3))‖ := mul_pos hu hv
  have hcy : Complex.normSq (star w ⬝ᵥ z) /
      (‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin 3))‖ * ‖(WithLp.toLp 2 z : EuclideanSpace ℂ (Fin
          3))‖) ≤
      ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin 3))‖ * ‖(WithLp.toLp 2 z : EuclideanSpace ℂ (Fin
          3))‖ := by
    apply (div_le_iff₀ huv).2
    nlinarith [hc]
  have hcn : 0 ≤ Complex.normSq (star w ⬝ᵥ z) /
      (‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin 3))‖ * ‖(WithLp.toLp 2 z : EuclideanSpace ℂ (Fin
          3))‖) :=
    div_nonneg (Complex.normSq_nonneg _) huv.le
  have hrel : (‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin 3))‖ * ‖(WithLp.toLp 2 z : EuclideanSpace ℂ
      (Fin 3))‖) *
      (Complex.normSq (star w ⬝ᵥ z) /
        (‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin 3))‖ * ‖(WithLp.toLp 2 z : EuclideanSpace ℂ (Fin
            3))‖)) =
      Complex.normSq (star w ⬝ᵥ z) := by
    exact mul_div_cancel₀ _ (ne_of_gt huv)
  have hsquare :
      (‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin 3))‖ * ‖(WithLp.toLp 2 z : EuclideanSpace ℂ (Fin
          3))‖ +
        Complex.normSq (star w ⬝ᵥ z) /
          (‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin 3))‖ * ‖(WithLp.toLp 2 z : EuclideanSpace ℂ
              (Fin 3))‖)) ^ 2 ≤
      (‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin 3))‖ * ‖(WithLp.toLp 2 z : EuclideanSpace ℂ (Fin
          3))‖) ^ 2 +
        3 * Complex.normSq (star w ⬝ᵥ z) := by
    nlinarith [sq_nonneg (‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin 3))‖ * ‖(WithLp.toLp 2 z :
        EuclideanSpace ℂ (Fin 3))‖ -
      Complex.normSq (star w ⬝ᵥ z) /
        (‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin 3))‖ * ‖(WithLp.toLp 2 z : EuclideanSpace ℂ (Fin
            3))‖)), hrel]
  nlinarith [hsquare]

private theorem frame_q_sum {m : ℕ} (z : Fin m → Fin 3 → ℂ)
    (hframe : (∑ a, (Matrix.vecMulVec (z a) (star (z a)))) =
      (1 : Matrix (Fin 3) (Fin 3) ℂ)) : ∑ a, finiteComplexEnergy (z a) = 3 := by
  have htr := congrArg Matrix.trace hframe
  rw [Matrix.trace_sum] at htr
  change (∑ a, (Matrix.vecMulVec (z a) (star (z a))).trace) =
      (1 : Matrix (Fin 3) (Fin 3) ℂ).trace at htr
  simp_rw [vec_trace] at htr
  have htrr := congrArg Complex.re htr
  simpa [Complex.re_sum] using htrr

private theorem frame_inner_sum {m₁ m₂ : ℕ} (z : Fin m₁ → Fin 3 → ℂ)
    (w : Fin m₂ → Fin 3 → ℂ)
    (hz : (∑ a, (Matrix.vecMulVec (z a) (star (z a)))) =
      (1 : Matrix (Fin 3) (Fin 3) ℂ))
    (hw : (∑ b, (Matrix.vecMulVec (w b) (star (w b)))) =
      (1 : Matrix (Fin 3) (Fin 3) ℂ)) :
    ∑ a, ∑ b, Complex.normSq (star (w b) ⬝ᵥ z a) = 3 := by
  have hrow (v : Fin 3 → ℂ) :
      ∑ b, Complex.normSq (star (w b) ⬝ᵥ v) = finiteComplexEnergy v := by
    have hc : ∑ b, (star (w b) ⬝ᵥ v) * (star v ⬝ᵥ w b) = (finiteComplexEnergy v : ℂ) := by
      calc
        _ = ∑ b, (Matrix.vecMulVec (w b) (star (w b)) *
            Matrix.vecMulVec v (star v)).trace := by
              simp_rw [vec_product_trace]
        _ = ((∑ b, Matrix.vecMulVec (w b) (star (w b))) *
            Matrix.vecMulVec v (star v)).trace := by
              rw [Matrix.sum_mul, Matrix.trace_sum]
        _ = (finiteComplexEnergy v : ℂ) := by
          change ((∑ b, Matrix.vecMulVec (w b) (star (w b))) *
            Matrix.vecMulVec v (star v)).trace = (finiteComplexEnergy v : ℂ)
          rw [hw, Matrix.one_mul, vec_trace]
    have hre := congrArg Complex.re hc
    rw [Complex.re_sum] at hre
    simpa only [inner_product_re, Complex.ofReal_re] using hre
  simp_rw [hrow]
  exact frame_q_sum z hz

private theorem markov_bound {m₁ m₂ : ℕ} (K₁ : Fin m₁ → Matrix (Fin 3) (Fin 3) ℂ)
    (K₂ : Fin m₂ → Matrix (Fin 3) (Fin 3) ℂ)
    (h₁ : IsKrausDecomposition K₁) (h₂ : IsKrausDecomposition K₂) :
    markovFidelity K₁ K₂ ≤ 1 / 2 := by
  obtain ⟨z, hrz, hfz⟩ := kraus_classification K₁ h₁
  obtain ⟨w, hrw, hfw⟩ := kraus_classification K₂ h₂
  have hqz := frame_q_sum z hfz
  have hqw := frame_q_sum w hfw
  have hinner := frame_inner_sum z w hfz hfw
  have hprod : ∑ a, ∑ b, finiteComplexEnergy (w b) * finiteComplexEnergy (z a) = 9 := by
    simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
    rw [hqw, hqz]
    norm_num
  unfold markovFidelity
  simp_rw [hrz, hrw]
  calc
    _ ≤ (1 / 9 : ℝ) * ∑ a, ∑ b,
        (finiteComplexEnergy (w b) * finiteComplexEnergy (z a) + 3 * Complex.normSq (star (w b) ⬝ᵥ z
            a)) / 4 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
        abs_pair_bound (w b) (z a)
    _ = 1 / 2 := by
      have he : (∑ a, ∑ b,
          (finiteComplexEnergy (w b) * finiteComplexEnergy (z a) + 3 * Complex.normSq (star (w b) ⬝ᵥ
              z a)) / 4) =
          ((∑ a, ∑ b, finiteComplexEnergy (w b) * finiteComplexEnergy (z a)) +
            3 * (∑ a, ∑ b, Complex.normSq (star (w b) ⬝ᵥ z a))) / 4 := by
        simp only [div_eq_mul_inv, Finset.sum_add_distrib, Finset.sum_mul,
          Finset.mul_sum, add_mul]
      rw [he, hprod, hinner]
      norm_num

private theorem canonical_is_kraus : IsKrausDecomposition canonicalKraus := by
  have hs : ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = (1 / 2 : ℂ) := by
    simpa only [pow_two, one_div] using
      D5.S3.QuantumBounds.CHSHWitness.complex_sqrt_two_inv_mul_self
  intro X
  let C : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ := fun a =>
    crossProduct (Pi.single a 1)
  have hskew (k l : Fin 3) : D5.S3.Quantum.Matrix.LinPsiMap.skew k l =
      ![![0, -C 2, C 1], ![C 2, 0, -C 0], ![-C 1, C 0, 0]] k l := by
    change Matrix.single k l 1 - Matrix.single l k 1 = _
    ext i j
    fin_cases k <;> fin_cases l <;> fin_cases i <;> fin_cases j <;>
      norm_num [C, crossProduct.eq_1, LinearMap.toMatrix'_apply, cross_apply,
        Matrix.single_apply, Pi.single_apply]
  have hsum := D5.S3.Quantum.Matrix.LinPsiMap.skew_sum X
  simp_rw [hskew] at hsum
  norm_num [Fin.sum_univ_succ, Matrix.conjTranspose_neg, Matrix.neg_mul,
    Matrix.mul_neg] at hsum
  have hc (a : Fin 3) : canonicalKraus a * X * (canonicalKraus a)ᴴ =
      (1 / 2 : ℂ) • (C a * X * (C a)ᴴ) := by
    simp only [canonicalKraus.eq_1, Matrix.conjTranspose_smul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, star_inv₀, Complex.star_def, map_inv₀,
      Complex.conj_ofReal]
    change ((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹) • _ = _
    rw [← pow_two, hs]
  have hw : wernerHolevo 1 X = (1 / 2 : ℂ) • (X.trace • 1 - Xᵀ) := by
    simp [wernerHolevo]
    module
  simp_rw [hc]
  rw [hw, ← hsum]
  simp [Fin.sum_univ_succ]
  module

private theorem rotation_is_kraus : IsKrausDecomposition rotationKraus := by
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := by
    rw [← Complex.star_def]
    norm_num
  have h3 : (starRingEnd ℂ) (3 : ℂ) = 3 := by
    rw [← Complex.star_def]
    norm_num
  have hU (i j : Fin 3) : ∑ k, rotationVector k i * star (rotationVector k j) =
      if i = j then 1 else 0 := by
    fin_cases i <;> fin_cases j <;>
      norm_num [rotationVector.eq_1, Fin.sum_univ_succ, Complex.star_def, h2, h3]
  have hm (j : Fin 3) :
      D5.S3.QuantumChannels.UnitaryKrausMixingInvariance.unitaryKrausMixing
        rotationVector canonicalKraus j = rotationKraus j := by
    change (∑ k, rotationVector j k • canonicalKraus k) = rotationKraus j
    ext i k
    fin_cases j <;> fin_cases i <;> fin_cases k <;>
      simp [canonicalKraus.eq_1, rotationKraus.eq_1, rotationVector.eq_1, crossProduct,
        LinearMap.toMatrix'_apply, cross_apply, Pi.single_apply, Fin.sum_univ_succ] <;> ring
  intro X
  have h := D5.S3.QuantumChannels.UnitaryKrausMixingInvariance.unitary_kraus_mixing_invariance
    rotationVector canonicalKraus X hU
  simpa only [hm, Matrix.star_eq_conjTranspose] using h.trans (canonical_is_kraus X)

private theorem abs_canonical (i : Fin 3) :
    CFC.abs (canonicalKraus i) = ((Real.sqrt 2)⁻¹ : ℂ) •
      ((1 : Matrix (Fin 3) (Fin 3) ℂ) - Matrix.single i i 1) := by
  have hb : (Pi.single i (1 : ℂ) : Fin 3 → ℂ) ≠ 0 := by
    intro h
    have hi := congrFun h i
    simp [Pi.single_apply] at hi
  have hn : ‖(WithLp.toLp 2 (Pi.single i (1 : ℂ) : Fin 3 → ℂ) : EuclideanSpace ℂ (Fin 3))‖ = 1 := by
    change ‖(PiLp.single 2 i (1 : ℂ) : EuclideanSpace ℂ (Fin 3))‖ = 1
    simp only [PiLp.norm_single, norm_one]
  have hv : Matrix.vecMulVec ((Pi.single i (1 : ℂ) : Fin 3 → ℂ)) (star ((Pi.single i (1 : ℂ) : Fin 3
      → ℂ))) =
      Matrix.single i i 1 := by
    simpa only [Pi.star_single, star_one] using
      (Matrix.single_eq_single_vecMulVec_single i i (α := ℂ)).symm
  unfold canonicalKraus
  rw [abs_crossProduct]
  simp only [if_neg hb, hn, Complex.ofReal_one, inv_one, one_smul, hv]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem bayes_pair_trace (i j : Fin 3) :
    (CFC.abs (rotationKraus j * CFC.abs (canonicalKraus i))).trace.re =
      (1 + |(rotationVector j i).re|) / 2 := by
  let p : Matrix (Fin 3) (Fin 3) ℂ := 1 - Matrix.single i i 1
  let b := crossProduct (rotationVector j) * p
  let s : ℝ := |(rotationVector j i).re|
  let root : Matrix (Fin 3) (Fin 3) ℂ :=
    (s / (2 * (1 + s))) • p + (1 / (2 * (1 + s))) • (bᴴ * b)
  have hp : p.PosSemidef := by
    have he : pᴴ * p = p := by
      simp [p, sub_mul, mul_sub]
    rw [← he]
    exact Matrix.posSemidef_conjTranspose_mul_self p
  have hsn : 0 ≤ s := abs_nonneg _
  have hpos : root.PosSemidef := by
    exact (hp.smul (show (0 : ℝ) ≤ s / (2 * (1 + s)) by positivity)).add
      ((Matrix.posSemidef_conjTranspose_mul_self b).smul
        (show (0 : ℝ) ≤ 1 / (2 * (1 + s)) by positivity))
  have hsq : root * root = ((1 / 2 : ℂ) • b)ᴴ * ((1 / 2 : ℂ) • b) := by
    ext a c
    fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases c <;>
      norm_num [root, b, p, s, rotationVector.eq_1, crossProduct, LinearMap.toMatrix'_apply,
          cross_apply, Pi.single_apply, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Matrix.single_apply, Matrix.one_apply, Fin.sum_univ_succ,
        Complex.real_smul, Complex.ext_iff, Complex.mul_re, Complex.mul_im,
        Complex.div_re, Complex.div_im, Complex.normSq_apply]
  have ht : root.trace.re = (1 + s) / 2 := by
    change (∑ k, root k k).re = (1 + s) / 2
    fin_cases i <;> fin_cases j <;>
      norm_num [root, b, p, s, rotationVector.eq_1, crossProduct, LinearMap.toMatrix'_apply,
          cross_apply, Pi.single_apply, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Matrix.single_apply, Matrix.one_apply, Fin.sum_univ_succ,
        Complex.real_smul, Complex.mul_re, Complex.mul_im,
        Complex.div_re, Complex.div_im, Complex.normSq_apply]
  have hs : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = (1 / 2 : ℂ) := by
    simpa only [one_div] using
      D5.S3.QuantumBounds.CHSHWitness.complex_sqrt_two_inv_mul_self
  have hm : rotationKraus j * CFC.abs (canonicalKraus i) = (1 / 2 : ℂ) • b := by
    rw [abs_canonical]
    simp only [rotationKraus.eq_1, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    change ((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹) • b = (1 / 2 : ℂ) • b
    rw [hs]
  have hr : CFC.abs ((1 / 2 : ℂ) • b) = root := CFC.sqrt_unique hsq hpos.nonneg
  rw [hm, hr]
  exact ht

private theorem bayesian_witness : 1 / 2 < bayesFidelity canonicalKraus rotationKraus := by
  have he : bayesFidelity canonicalKraus rotationKraus = 11 / 18 := by
    unfold bayesFidelity
    change (1 / 9 : ℝ) * ∑ a, ∑ b,
      ((CFC.abs (rotationKraus b * CFC.abs (canonicalKraus a))).trace.re) ^ 2 = 11 / 18
    simp_rw [bayes_pair_trace]
    norm_num [rotationVector.eq_1, Fin.sum_univ_succ, Complex.div_re,
      Complex.div_im, Complex.normSq_apply]
  rw [he]
  norm_num

/-- For the unital Matrix (Fin 3) (Fin 3) ℂ Werner--Holevo channel, every Markovian value is at most
`1/2`, while the canonical/rational-rotation Kraus pair has Bayesian value above `1/2`.
This answers the source's request with a unital channel, hence not an amplitude
damping channel. -/
theorem result :
    (∀ (m₁ m₂ : ℕ) (k₁ : Fin m₁ → Matrix (Fin 3) (Fin 3) ℂ)
      (k₂ : Fin m₂ → Matrix (Fin 3) (Fin 3) ℂ),
      IsKrausDecomposition k₁ → IsKrausDecomposition k₂ →
        markovFidelity k₁ k₂ ≤ 1 / 2) ∧
    (∃ l₁ : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ, ∃ l₂ : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ,
      IsKrausDecomposition l₁ ∧ IsKrausDecomposition l₂ ∧
        1 / 2 < bayesFidelity l₁ l₂) := by
  constructor
  · intro m₁ m₂ k₁ k₂ h₁ h₂
    exact markov_bound k₁ k₂ h₁ h₂
  · exact ⟨canonicalKraus, rotationKraus, canonical_is_kraus, rotation_is_kraus,
      bayesian_witness⟩

end D5.S3.Quantum.Recovery.WernerHolevoBayesianFeedbackAdvantage
