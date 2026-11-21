/- GID: D5/S3/Analytic/PetzLogisticEvaluation
   generality: G
   mirror-B: D5/B/S3/Analytic/PetzLogisticEvaluation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The exact upper Petz weight gives a frequency-count bound for evaluation at zero. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Analytic.PetzStripFiniteSeries
import D5.S3.Quantum.GNSMatrix
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Exact logistic Petz evaluation

The logistic Fourier Gram is the entrywise modulus square of the correlation
Gram of the logarithm of a mean-one exponential variable, scaled by `2π`.
Euler reflection identifies the squared Gamma transform with the exact Petz
cosine transform. The matrix estimate is the correlation case of Vybíral's
variant of Schur's product theorem (DOI: 10.1016/j.aim.2020.107140).
-/

set_option autoImplicit false

noncomputable section

open Filter Matrix MeasureTheory Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

namespace PetzLogisticEvaluation

open PetzExponentialBoundaryEvaluation (petzWeight petzWeight_pos petzWeight_neg
  continuous_petzWeight distinctFrequencies)
open ExponentialGramWeightedEvaluation (exponentialSum frequency)
open private integral_petzWeight_mul_cos integrable_petzWeight from
  D5.S3.Analytic.PetzStripFiniteSeries
open private frobenius_sq from D5.S3.Quantum.Recovery.PetzExponentialBoundaryEvaluation

private def mode (ω t : ℝ) : ℂ := Complex.exp (((ω * t : ℝ) : ℂ) * Complex.I)

private theorem star_mode_mul (u v t : ℝ) : star (mode u t) * mode v t = mode (v - u) t := by
  unfold mode
  rw [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem norm_mode (ω t : ℝ) : ‖mode ω t‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

private def logExponentialMode (ω x : ℝ) : ℂ :=
  (Real.exp (-x) : ℂ) * mode ω (Real.log x / (2 * Real.pi))

private def gammaArgument (ω : ℝ) : ℂ := ((ω / (2 * Real.pi) : ℝ) : ℂ) * Complex.I

private theorem gammaArgument_re (ω : ℝ) : (gammaArgument ω).re = 0 := by
  unfold gammaArgument
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im, mul_zero, zero_mul, sub_zero]

private theorem logExponentialMode_eq (ω x : ℝ) (hx : 0 < x) :
    logExponentialMode ω x = (Real.exp (-x) : ℂ) * (x : ℂ) ^ (1 + gammaArgument ω - 1) := by
  rw [logExponentialMode, mode, add_sub_cancel_left,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'),
    ← Complex.ofReal_log hx.le]
  congr 2
  unfold gammaArgument
  push_cast
  ring

private theorem integrable_logExponentialMode (ω : ℝ) :
    IntegrableOn (logExponentialMode ω) (Ioi 0) :=
  (Complex.GammaIntegral_convergent (s := 1 + gammaArgument ω) (by
    simpa only [Complex.add_re, Complex.one_re, gammaArgument_re, add_zero] using
      (zero_lt_one : (0 : ℝ) < 1))).congr (ae_restrict_of_forall_mem measurableSet_Ioi
      (fun x hx => (logExponentialMode_eq ω x hx).symm))

private theorem integral_logExponentialMode (ω : ℝ) :
    (∫ x in Ioi (0 : ℝ), logExponentialMode ω x) = Complex.Gamma (1 + gammaArgument ω) := by
  have hs : 0 < (1 + gammaArgument ω).re := by
    rw [Complex.add_re, Complex.one_re, gammaArgument_re, add_zero]
    exact zero_lt_one
  rw [Complex.Gamma_eq_integral hs, Complex.GammaIntegral]
  exact setIntegral_congr_fun measurableSet_Ioi (logExponentialMode_eq ω)

private theorem gamma_norm_sq (ω : ℝ) :
    (‖Complex.Gamma (1 + gammaArgument ω)‖ ^ 2 : ℂ) =
      ((if ω = 0 then 1 else (ω / 2) / Real.sinh (ω / 2) : ℝ) : ℂ) := by
  by_cases hω : ω = 0
  · simp [hω, gammaArgument]
  let z := gammaArgument ω
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hz : z ≠ 0 := mul_ne_zero (by exact_mod_cast div_ne_zero hω (by positivity :
    (2 * Real.pi) ≠ 0)) Complex.I_ne_zero
  have hconj : (starRingEnd ℂ) (1 + z) = 1 - z := by
    simp [z, gammaArgument, map_add, map_mul, Complex.conj_I, map_ofNat, sub_eq_add_neg]
  have harg : (Real.pi : ℂ) * z = ((ω / 2 : ℝ) : ℂ) * Complex.I := by
    dsimp only [z, gammaArgument]
    push_cast
    field_simp [hπ]
  have hs : (Real.sinh (ω / 2) : ℂ) ≠ 0 := by
    exact_mod_cast Real.sinh_ne_zero.mpr (div_ne_zero hω (by norm_num))
  rw [ite_eq_right hω]
  change (‖Complex.Gamma (1 + z)‖ ^ 2 : ℂ) = _
  calc
    _ = (z * Complex.Gamma z) * Complex.Gamma (1 - z) := by
      rw [← Complex.conj_mul', ← Complex.Gamma_conj, hconj,
        show 1 + z = z + 1 by ring, Complex.Gamma_add_one z hz, mul_comm]
    _ = z * ((Real.pi : ℂ) / ((Real.sinh (ω / 2) : ℂ) * Complex.I)) := by
      rw [mul_assoc, Complex.Gamma_mul_Gamma_one_sub, harg, Complex.sin_mul_I,
        ← Complex.ofReal_sinh]
    _ = _ := by
      dsimp only [z, gammaArgument]
      push_cast
      field_simp [hπ, hs, Complex.I_ne_zero]

section Gram

variable {ι : Type*}

/-- The correlation of the phases of the scaled log-exponential law. -/
def correlation (ω : ι → ℝ) : Matrix ι ι ℂ :=
  Matrix.of fun i j => ∫ x in Ioi 0, logExponentialMode (ω j - ω i) x

private theorem correlation_diag (ω : ι → ℝ) (i : ι) : correlation ω i i = 1 := by
  simp [correlation, integral_logExponentialMode, gammaArgument]

private theorem correlation_posSemidef [Finite ι] (ω : ι → ℝ) : (correlation ω).PosSemidef := by
  let : Fintype ι := Fintype.ofFinite ι
  have hentry (i j : ι) (x : ℝ) :
      logExponentialMode (ω j - ω i) x =
        (Real.exp (-x) : ℂ) *
          (star (mode (ω i) (Real.log x / (2 * Real.pi))) *
            mode (ω j) (Real.log x / (2 * Real.pi))) := by
    rw [star_mode_mul, logExponentialMode]
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun a => ?_⟩
  · apply Matrix.ext
    intro i j
    simp only [Matrix.conjTranspose_apply, correlation, Matrix.of_apply, Complex.star_def]
    rw [← integral_conj]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      change (starRingEnd ℂ) (logExponentialMode (ω i - ω j) x) = _
      rw [hentry j i, hentry i j]
      simp only [Complex.star_def, map_mul, Complex.conj_ofReal, starRingEnd_self_apply]
      ring
  · let f (i j : ι) (x : ℝ) := star (a i) * a j * logExponentialMode (ω j - ω i) x
    have hi (i j : ι) : IntegrableOn (f i j) (Ioi 0) :=
      (integrable_logExponentialMode _).const_mul _
    have hform : star a ⬝ᵥ (correlation ω *ᵥ a) = ∫ x in Ioi (0 : ℝ), ∑ i, ∑ j, f i j x := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, correlation,
        Matrix.of_apply]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum _ (fun j _ => hi i j)]
      simp only [f, integral_const_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hpoint (x : ℝ) : (∑ i, ∑ j, f i j x) =
        ((Real.exp (-x) * ‖∑ i, a i * mode (ω i) (Real.log x / (2 * Real.pi))‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_mul, ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
      simp only [← Complex.star_def, star_sum]
      rw [Finset.sum_mul_sum]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      dsimp only [f]
      rw [hentry, star_mul]
      ring
    rw [hform]
    simp_rw [hpoint]
    let g (x : ℝ) := Real.exp (-x) * ‖∑ i, a i * mode (ω i) (Real.log x / (2 * Real.pi))‖ ^ 2
    have hg : (∫ x in Ioi (0 : ℝ), (g x : ℂ)) =
        Complex.ofReal (∫ x in Ioi (0 : ℝ), g x) :=
      integral_ofReal (𝕜 := ℂ) (μ := volume.restrict (Ioi (0 : ℝ))) (f := g)
    change 0 ≤ ∫ x in Ioi (0 : ℝ), (g x : ℂ)
    rw [hg]
    have hnonneg : 0 ≤ ∫ x in Ioi (0 : ℝ), g x :=
      integral_nonneg (fun x => mul_nonneg (Real.exp_pos (-x)).le (sq_nonneg _))
    exact_mod_cast hnonneg

private theorem integrable_weighted_mode (ω : ℝ) :
    Integrable (fun t => (petzWeight t : ℂ) * mode ω t) := by
  have hc : Continuous (fun t => (petzWeight t : ℂ) * mode ω t) :=
    (Complex.continuous_ofReal.comp continuous_petzWeight).mul (by unfold mode; fun_prop)
  refine integrable_petzWeight.mono' hc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ?_)
  rw [norm_mul, norm_mode, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (petzWeight_pos t).le]

private theorem integral_weighted_mode (ω : ℝ) :
    (∫ t : ℝ, (petzWeight t : ℂ) * mode ω t) =
      Complex.ofReal (∫ t : ℝ, petzWeight t * Real.cos (ω * t)) := by
  let f (t : ℝ) := (petzWeight t : ℂ) * mode ω t
  have hf : Integrable f := integrable_weighted_mode ω
  have hn : Integrable (fun t => f (-t)) := by
    simpa only [neg_one_mul] using hf.comp_mul_left' (by norm_num : (-1 : ℝ) ≠ 0)
  have hreflect : (∫ t, f (-t)) = ∫ t, f t := by
    simpa only [neg_one_mul, inv_neg, inv_one, abs_neg, abs_one, one_smul] using
      Measure.integral_comp_mul_left f (-1)
  have havg (t : ℝ) : f t + f (-t) = (2 : ℂ) * (petzWeight t * Real.cos (ω * t) : ℝ) := by
    simp only [f, petzWeight_neg, mode, mul_neg, Complex.ofReal_neg, neg_mul,
      Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg, Complex.ofReal_cos,
      Complex.ofReal_mul]
    ring
  have h := congrArg (fun g : ℝ → ℂ => ∫ t, g t) (funext havg)
  change (∫ t, f t + f (-t)) =
    ∫ t, (2 : ℂ) * (petzWeight t * Real.cos (ω * t) : ℝ) at h
  let g (t : ℝ) := petzWeight t * Real.cos (ω * t)
  have hg : (∫ t : ℝ, (g t : ℂ)) = Complex.ofReal (∫ t : ℝ, g t) :=
    integral_ofReal (𝕜 := ℂ) (μ := volume) (f := g)
  change (∫ t, f t + f (-t)) = ∫ t, (2 : ℂ) * (g t : ℂ) at h
  rw [integral_add hf hn, hreflect, integral_const_mul, hg, two_mul] at h
  change (∫ t, f t) = Complex.ofReal (∫ t : ℝ, g t)
  linear_combination (1 / 2 : ℂ) * h

/-- The actual logistic Fourier Gram is the Schur square of the log-exponential
correlation matrix, including coincident frequencies and the diagonal. -/
theorem exact_gram_factorization [Finite ι] (ω : ι → ℝ) :
    (correlation ω).PosSemidef ∧ (∀ i, correlation ω i i = 1) ∧
    ∀ i j, (∫ t : ℝ, (petzWeight t : ℂ) *
      Complex.exp ((((ω j - ω i) * t : ℝ) : ℂ) * Complex.I)) =
      (‖correlation ω i j‖ ^ 2 : ℂ) := by
  refine ⟨correlation_posSemidef ω, correlation_diag ω, fun i j => ?_⟩
  change (∫ t : ℝ, (petzWeight t : ℂ) * mode (ω j - ω i) t) = _
  rw [integral_weighted_mode, integral_petzWeight_mul_cos, correlation, Matrix.of_apply,
    integral_logExponentialMode, gamma_norm_sq]

variable [Fintype ι]

private theorem trace_sq_le_card_mul_frobenius_sq (S : Matrix ι ι ℂ) :
    ‖S.trace‖ ^ 2 ≤ (Fintype.card ι : ℝ) * ‖S‖ ^ 2 := by
  calc
    ‖S.trace‖ ^ 2 ≤ (∑ i, ‖S i i‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ (Fintype.card ι : ℝ) * ∑ i, ‖S i i‖ ^ 2 := by
      simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun _ : ι => (1 : ℝ)) (fun i => ‖S i i‖)
    _ ≤ _ := by
      rw [frobenius_sq]
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (Nat.cast_nonneg _)
      exact Finset.single_le_sum (f := fun j => ‖S i j‖ ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i)

/-- The trace of the sum of outer products evaluates the coefficient sum.
The squared Hilbert–Schmidt norm uses the entrywise squared moduli of their
correlation matrix. -/
private theorem schur_square_evaluation (A : Matrix ι ι ℂ) (hA : A.PosSemidef)
    (hdiag : ∀ i, A i i = 1) (a : ι → ℂ) :
    ‖∑ i, a i‖ ^ 2 ≤ (Fintype.card ι : ℝ) *
      (∑ i, ∑ j, star (a i) * a j * (‖A i j‖ ^ 2 : ℂ)).re := by
  classical
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  let v (i : ι) : ι → ℂ := fun k => B k i
  let P (i : ι) : Matrix ι ι ℂ := vecMulVec (v i) (star (v i))
  let S : Matrix ι ι ℂ := ∑ i, a i • P i
  have hdot (i j : ι) : star (v i) ⬝ᵥ v j = (star B * B) i j := rfl
  have hP (i : ι) : (P i)ᴴ = P i := by
    simp [P, Matrix.conjTranspose_vecMulVec]
  have hTr (i : ι) : (P i).trace = 1 := by
    change (vecMulVec (v i) (star (v i))).trace = 1
    rw [Matrix.trace_vecMulVec, dotProduct_comm, hdot, hdiag]
  have hPair (i j : ι) : (P i * P j).trace = (‖(star B * B) i j‖ ^ 2 : ℂ) := by
    have hc : star (star (v i) ⬝ᵥ v j) = v i ⬝ᵥ star (v j) := by
      rw [dotProduct_comm (v i) (star (v j))]
      exact (star_dotProduct (v j) (v i)).symm
    change (vecMulVec (v i) (star (v i)) * vecMulVec (v j) (star (v j))).trace = _
    rw [Matrix.vecMulVec_mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_smul,
      ← hc, hdot, smul_eq_mul, mul_comm, Complex.star_def, Complex.conj_mul']
  have htrace : S.trace = ∑ i, a i := by
    simp only [S, Matrix.trace_sum, Matrix.trace_smul, hTr, smul_eq_mul, mul_one]
  have hnorm : ‖S‖ ^ 2 = (∑ i, ∑ j,
      star (a i) * a j * (‖(star B * B) i j‖ ^ 2 : ℂ)).re := by
    have h := congrArg Complex.re (D5.S3.Quantum.GNSMatrix.frobenius_norm_sq_eq_trace S)
    rw [Complex.ofReal_re] at h
    rw [h]
    congr 1
    simp only [S, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, hP,
      Finset.sum_mul_sum, Matrix.trace_sum, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.trace_smul, hPair, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simpa only [htrace, hnorm] using trace_sq_le_card_mul_frobenius_sq S

private theorem weighted_energy_eq_gram (ω : ι → ℝ) (a : ι → ℂ) :
    Integrable (fun t : ℝ => petzWeight t * ‖exponentialSum ω a (t : ℂ)‖ ^ 2) ∧
    Complex.ofReal (∫ t : ℝ, petzWeight t * ‖exponentialSum ω a (t : ℂ)‖ ^ 2) =
      ∑ i, ∑ j, star (a i) * a j * (‖correlation ω i j‖ ^ 2 : ℂ) := by
  let f (i j : ι) (t : ℝ) :=
    (star (a i) * a j) * ((petzWeight t : ℂ) * mode (ω j - ω i) t)
  have hi (i j : ι) : Integrable (f i j) := (integrable_weighted_mode _).const_mul _
  have hsum (t : ℝ) : exponentialSum ω a (t : ℂ) = ∑ i, a i * mode (ω i) t := by
    simp only [exponentialSum, frequency, mode, Complex.ofReal_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_rotate Complex.I]
  have hpoint (t : ℝ) : ((petzWeight t * ‖exponentialSum ω a (t : ℂ)‖ ^ 2 : ℝ) : ℂ) =
      ∑ i, ∑ j, f i j t := by
    rw [hsum, Complex.ofReal_mul, ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    simp only [← Complex.star_def, star_sum]
    rw [Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [f]
    rw [star_mul, ← star_mode_mul]
    ring
  have hInt : Integrable (fun t : ℝ =>
      ((petzWeight t * ‖exponentialSum ω a (t : ℂ)‖ ^ 2 : ℝ) : ℂ)) := by
    rw [show (fun t : ℝ => ((petzWeight t * ‖exponentialSum ω a (t : ℂ)‖ ^ 2 : ℝ) : ℂ))
      = _ from funext hpoint]
    exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))
  refine ⟨by simpa only [RCLike.re_eq_complex_re, Complex.ofReal_re] using hInt.re, ?_⟩
  let g (t : ℝ) := petzWeight t * ‖exponentialSum ω a (t : ℂ)‖ ^ 2
  have hg : Complex.ofReal (∫ t : ℝ, g t) = ∫ t : ℝ, (g t : ℂ) :=
    (integral_ofReal (𝕜 := ℂ) (μ := volume) (f := g)).symm
  change Complex.ofReal (∫ t : ℝ, g t) = _
  rw [hg, show (fun t : ℝ => (g t : ℂ)) = _ from funext hpoint,
    integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hi i j)]
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [f]
  rw [integral_const_mul]
  exact congrArg (fun z : ℂ => star (a i) * a j * z) ((exact_gram_factorization ω).2.2 i j)

private theorem weighted_evaluation_card (ω : ι → ℝ) (a : ι → ℂ) :
    Integrable (fun t : ℝ => petzWeight t * ‖exponentialSum ω a (t : ℂ)‖ ^ 2) ∧
    ‖exponentialSum ω a 0‖ ^ 2 ≤ (Fintype.card ι : ℝ) *
      (∫ t : ℝ, petzWeight t * ‖exponentialSum ω a (t : ℂ)‖ ^ 2) := by
  obtain ⟨hi, henergy⟩ := weighted_energy_eq_gram ω a
  have hgram := exact_gram_factorization ω
  have h := schur_square_evaluation (correlation ω) hgram.1 hgram.2.1 a
  rw [← henergy, Complex.ofReal_re] at h
  exact ⟨hi, by simpa [exponentialSum] using h⟩

/-- The exact upper weight gives evaluation at zero with coefficient equal
to the number of distinct frequencies, including the empty list. -/
theorem weighted_evaluation (ω : ι → ℝ) (a : ι → ℂ) :
    Integrable (fun t : ℝ => petzWeight t * ‖exponentialSum ω a (t : ℂ)‖ ^ 2) ∧
    ‖exponentialSum ω a 0‖ ^ 2 ≤ ((distinctFrequencies ω).card : ℝ) *
      (∫ t : ℝ, petzWeight t * ‖exponentialSum ω a (t : ℂ)‖ ^ 2) := by
  classical
  let S := distinctFrequencies ω
  let coeff (r : ℝ) := ∑ i ∈ Finset.univ with ω i = r, a i
  let freq : S → ℝ := Subtype.val
  have hSum : exponentialSum freq (fun r => coeff r) = exponentialSum ω a := by
    funext z
    change (∑ r : S, coeff (r : ℝ) * Complex.exp (Complex.I * (r : ℂ) * z)) =
      ∑ i, a i * Complex.exp (Complex.I * (ω i : ℂ) * z)
    rw [Finset.sum_coe_sort S (fun r : ℝ => coeff r * Complex.exp (Complex.I * (r : ℂ) * z))]
    calc
      _ = ∑ r ∈ S, ∑ i ∈ Finset.univ with ω i = r,
          a i * Complex.exp (Complex.I * (ω i : ℂ) * z) := by
        apply Finset.sum_congr rfl
        intro r _
        dsimp only [coeff]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        rw [(Finset.mem_filter.mp hi).2]
      _ = _ := Finset.sum_fiberwise_of_maps_to
        (fun i hi => (show ω i ∈ S from Finset.mem_image_of_mem ω hi)) _
  have h := weighted_evaluation_card freq (fun r => coeff r)
  rw [hSum, Fintype.card_coe] at h
  exact h

private theorem tendsto_integral_weighted_mode :
    Tendsto (fun ω : ℝ => ∫ t : ℝ, (petzWeight t : ℂ) * mode ω t)
      (cocompact ℝ) (𝓝 0) := by
  have h := Real.tendsto_integral_exp_smul_cocompact (fun t => (petzWeight t : ℂ))
  have hπ : 2 * Real.pi ≠ 0 := by positivity
  have hscale : Tendsto (fun ω : ℝ => -(1 / (2 * Real.pi)) * ω)
      (cocompact ℝ) (cocompact ℝ) := by
    have hneg : -(1 / (2 * Real.pi)) < 0 := neg_lt_zero.mpr (by positivity)
    rw [cocompact_eq_atBot_atTop]
    exact tendsto_sup.mpr
      ⟨((tendsto_const_mul_atTop_of_neg hneg).2 tendsto_id).mono_right le_sup_right,
       ((tendsto_const_mul_atBot_of_neg hneg).2 tendsto_id).mono_right le_sup_left⟩
  convert h.comp hscale using 1
  funext ω
  apply integral_congr_ae
  exact Eventually.of_forall fun t => by
    have harg : 2 * Real.pi * -(t * (-(1 / (2 * Real.pi)) * ω)) = ω * t := by
      field_simp
    simp only [Circle.smul_def, Real.fourierChar_apply, mode,
      smul_eq_mul, harg]
    exact mul_comm _ _

/-- For a nonempty frequency index, every bound valid for all injective
frequency lists has coefficient at least the index cardinality. -/
theorem card_le_of_uniform_bound {m : ℕ} (hm : 0 < m) (K : ℝ)
    (hK : ∀ (ω : Fin m → ℝ), Function.Injective ω → ∀ a : Fin m → ℂ,
      ‖exponentialSum ω a 0‖ ^ 2 ≤ K *
        (∫ t : ℝ, petzWeight t * ‖exponentialSum ω a (t : ℂ)‖ ^ 2)) :
    (m : ℝ) ≤ K := by
  classical
  let ω (R : ℝ) (i : Fin m) : ℝ := (i.val : ℝ) * R
  let E (R : ℝ) := ∫ t : ℝ, petzWeight t * ‖exponentialSum (ω R) (fun _ => 1) (t : ℂ)‖ ^ 2
  have hPair (R : ℝ) (i j : Fin m) :
      (‖correlation (ω R) i j‖ ^ 2 : ℂ) =
        ∫ t : ℝ, (petzWeight t : ℂ) * mode (((j.val : ℝ) - i.val) * R) t := by
    rw [show ((j.val : ℝ) - i.val) * R = ω R j - ω R i by dsimp [ω]; ring]
    exact ((exact_gram_factorization (ω R)).2.2 i j).symm
  have hLimit (i j : Fin m) :
      Tendsto (fun R : ℝ => (‖correlation (ω R) i j‖ ^ 2 : ℂ)) atTop
        (𝓝 (if i = j then 1 else 0)) := by
    by_cases hij : i = j
    · subst j
      simpa only [ite_true, correlation_diag, norm_one, one_pow, Complex.ofReal_one] using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℂ)) atTop (𝓝 1))
    · have hn : (j.val : ℝ) - i.val ≠ 0 := by
        intro he
        have hval : j.val = i.val := by exact_mod_cast sub_eq_zero.mp he
        exact hij (Fin.ext hval.symm)
      have hscale : Tendsto (fun R : ℝ => ((j.val : ℝ) - i.val) * R) atTop (cocompact ℝ) := by
        rcases lt_or_gt_of_ne hn with hneg | hpos
        · exact ((tendsto_const_mul_atBot_of_neg hneg).2 tendsto_id).mono_right atBot_le_cocompact
        · exact ((tendsto_const_mul_atTop_of_pos hpos).2 tendsto_id).mono_right atTop_le_cocompact
      simp only [ite_eq_right hij, hPair]
      exact tendsto_integral_weighted_mode.comp hscale
  have hSum := tendsto_finsetSum Finset.univ (fun i _ =>
    tendsto_finsetSum Finset.univ (fun j _ => hLimit i j))
  have hEnergy : Tendsto E atTop (𝓝 (m : ℝ)) := by
    have he (R : ℝ) : (E R : ℂ) = ∑ i, ∑ j, (‖correlation (ω R) i j‖ ^ 2 : ℂ) := by
      simpa only [E, star_one, one_mul] using
        (weighted_energy_eq_gram (ω R) (fun _ => 1)).2
    have hComplex : Tendsto (fun R => (E R : ℂ)) atTop (𝓝 (m : ℂ)) := by
      simpa [he] using hSum
    simpa only [Function.comp_def, Complex.ofReal_re, Complex.natCast_re] using
      (Complex.continuous_re.tendsto (m : ℂ)).comp hComplex
  have hev : ∀ᶠ R : ℝ in atTop, (m : ℝ) ^ 2 ≤ K * E R := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have hinj : Function.Injective (ω R) := by
      intro i j h
      have h' : (i.val : ℝ) = j.val := mul_right_cancel₀ hR.ne' h
      exact Fin.ext (by exact_mod_cast h')
    have hEval := hK (ω R) hinj (fun _ => 1)
    simpa [E, exponentialSum, Complex.norm_natCast] using hEval
  have hlim : (m : ℝ) ^ 2 ≤ K * (m : ℝ) :=
    ge_of_tendsto (tendsto_const_nhds.mul hEnergy) hev
  exact le_of_mul_le_mul_right (by simpa [pow_two] using hlim) (by exact_mod_cast hm)

end Gram

#print axioms exact_gram_factorization
#print axioms weighted_evaluation
#print axioms card_le_of_uniform_bound

end PetzLogisticEvaluation
