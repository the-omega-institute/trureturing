/- GID: D5/S3/Quantum/Measurements/EntropyPowerCovarianceUncertaintyRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurements/EntropyPowerCovarianceUncertaintyRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Measurements/EntropyPowerCovarianceUncertaintyRefutation.claim; result=D5/S3/Quantum/Measurements/EntropyPowerCovarianceUncertaintyRefutation.result; claim=D5/S3/Quantum/Measurements/EntropyPowerCovarianceUncertaintyRefutation.claim
   digest: A binary coherent-state mixture violates the covariance-corrected entropy bound. -/

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! A finite Gaussian-mixture counterexample to the covariance-corrected uncertainty relation. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

noncomputable section

namespace D5.S3.Quantum.Measurements.EntropyPowerCovarianceUncertaintyRefutation

/-- The one-mode Gaussian Wigner density, in units with Planck's constant equal to one. -/
def gaussianWigner (μx μp a b c x p : ℝ) : ℝ :=
  (2 * Real.pi * Real.sqrt (a * c - b ^ 2))⁻¹ *
    Real.exp (-(c * (x - μx) ^ 2 - 2 * b * (x - μx) * (p - μp) +
      a * (p - μp) ^ 2) / (2 * (a * c - b ^ 2)))

/-- The Wigner function of a finite mixture of Gaussian states. -/
def mixtureWigner (n : ℕ) (w μx μp a b c : Fin n → ℝ) (x p : ℝ) : ℝ :=
  ∑ i, w i * gaussianWigner (μx i) (μp i) (a i) (b i) (c i) x p

def marginalX (W : ℝ → ℝ → ℝ) (x : ℝ) : ℝ := ∫ p, W x p

def marginalP (W : ℝ → ℝ → ℝ) (p : ℝ) : ℝ := ∫ x, W x p

def densityEntropy (f : ℝ → ℝ) : ℝ := -(∫ x, f x * Real.log (f x))

def meanX (W : ℝ → ℝ → ℝ) : ℝ := ∫ r : ℝ × ℝ, r.1 * W r.1 r.2

def meanP (W : ℝ → ℝ → ℝ) : ℝ := ∫ r : ℝ × ℝ, r.2 * W r.1 r.2

def covarianceXX (W : ℝ → ℝ → ℝ) : ℝ :=
  ∫ r : ℝ × ℝ, (r.1 - meanX W) ^ 2 * W r.1 r.2

def covariancePP (W : ℝ → ℝ → ℝ) : ℝ :=
  ∫ r : ℝ × ℝ, (r.2 - meanP W) ^ 2 * W r.1 r.2

def covarianceXP (W : ℝ → ℝ → ℝ) : ℝ :=
  ∫ r : ℝ × ℝ, (r.1 - meanX W) * (r.2 - meanP W) * W r.1 r.2

/-- The covariance-corrected entropy-power uncertainty inequality for all finite Gaussian
mixtures, with finite quadrature entropies and finite phase-space second moments. -/
def claim : Prop :=
  ∀ (n : ℕ) (w μx μp a b c : Fin n → ℝ),
    (∀ i, 0 ≤ w i) → (∑ i, w i) = 1 →
    (∀ i, 0 < a i) → (∀ i, 0 < c i) →
    (∀ i, (1 : ℝ) / 4 ≤ a i * c i - b i ^ 2) →
    let W := mixtureWigner n w μx μp a b c
    Integrable (fun x => marginalX W x * Real.log (marginalX W x)) →
    Integrable (fun p => marginalP W p * Real.log (marginalP W p)) →
    Integrable (fun r : ℝ × ℝ => (r.1 ^ 2 + r.2 ^ 2) * W r.1 r.2) →
    Real.log (Real.pi * Real.exp 1) ≤
      densityEntropy (marginalX W) + densityEntropy (marginalP W) -
        1 / 2 * Real.log (covarianceXX W * covariancePP W /
          (covarianceXX W * covariancePP W - covarianceXP W ^ 2))

private def q (d x : ℝ) : ℝ :=
  (gaussianPDFReal d (1 / 2) x + gaussianPDFReal (-d) (1 / 2) x) / 2

private def witnessW (d x p : ℝ) : ℝ :=
  (gaussianWigner d d (1 / 2) 0 (1 / 2) x p +
    gaussianWigner (-d) (-d) (1 / 2) 0 (1 / 2) x p) / 2

private lemma component_factor (u v x p : ℝ) :
    gaussianWigner u v (1 / 2) 0 (1 / 2) x p =
      gaussianPDFReal u (1 / 2) x * gaussianPDFReal v (1 / 2) p := by
  have hs : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hp := Real.sq_sqrt Real.pi_pos.le
  have hn := (Real.sqrt_pos.2 Real.pi_pos).ne'
  simp only [gaussianWigner, gaussianPDFReal, NNReal.coe_div, NNReal.coe_one,
    NNReal.coe_ofNat]
  norm_num only [zero_pow, mul_zero, sub_zero, zero_mul, zero_add] 
  rw [hs, show 2 * Real.pi * (1 / 2) = Real.pi by ring]
  simp only [div_one]
  rw [show -((1 / 2 : ℝ) * (x - u) ^ 2 + 1 / 2 * (p - v) ^ 2) /
      (1 / 2) = -(x - u) ^ 2 + -(p - v) ^ 2 by ring, Real.exp_add]
  field_simp
  nlinarith

private lemma gaussian_moments (m : ℝ) :
    Integrable (fun x => x * gaussianPDFReal m (1 / 2) x) ∧
    Integrable (fun x => x ^ 2 * gaussianPDFReal m (1 / 2) x) ∧
    (∫ x, x * gaussianPDFReal m (1 / 2) x) = m ∧
    (∫ x, x ^ 2 * gaussianPDFReal m (1 / 2) x) = m ^ 2 + 1 / 2 ∧
    (∫ x, (x - m) ^ 2 * gaussianPDFReal m (1 / 2) x) = 1 / 2 := by
  have hv : (1 / 2 : ℝ≥0) ≠ 0 := by norm_num
  have hlp := memLp_id_gaussianReal (μ := m) (v := (1 / 2)) 2
  have hi : Integrable (fun x : ℝ => x) (gaussianReal m (1 / 2)) :=
    hlp.integrable (by norm_num)
  have hs : Integrable (fun x : ℝ => x ^ 2) (gaussianReal m (1 / 2)) :=
    hlp.integrable_sq
  have transport (f : ℝ → ℝ) (hf : Integrable f (gaussianReal m (1 / 2))) :
      Integrable (fun x => f x * gaussianPDFReal m (1 / 2) x) := by
    rw [gaussianReal_of_var_ne_zero _ hv] at hf
    have ht := (integrable_withDensity_iff_integrable_smul'
      (measurable_gaussianPDF m (1 / 2)) (Filter.Eventually.of_forall
        fun _ => gaussianPDF_lt_top)).1 hf
    simpa only [toReal_gaussianPDF, smul_eq_mul, mul_comm] using ht
  have hmean : (∫ x, x * gaussianPDFReal m (1 / 2) x) = m := by
    simpa only [integral_gaussianReal_eq_integral_smul hv, smul_eq_mul, mul_comm]
      using (integral_id_gaussianReal (μ := m) (v := (1 / 2)))
  have hvv := variance_eq_sub hlp
  simp only [variance_id_gaussianReal, Pi.pow_apply, id_eq, integral_id_gaussianReal,
    NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] at hvv
  have hsecond : (∫ x, x ^ 2 * gaussianPDFReal m (1 / 2) x) = m ^ 2 + 1 / 2 := by
    rw [integral_gaussianReal_eq_integral_smul hv] at hvv
    simp only [smul_eq_mul, mul_comm] at hvv
    linarith
  have hc := variance_fun_id_gaussianReal (μ := m) (v := (1 / 2))
  rw [variance_eq_integral measurable_id'.aemeasurable, integral_id_gaussianReal,
    integral_gaussianReal_eq_integral_smul hv] at hc
  refine ⟨transport _ hi, transport _ hs, hmean, hsecond, ?_⟩
  simpa only [smul_eq_mul, mul_comm, NNReal.coe_div, NNReal.coe_one,
    NNReal.coe_ofNat] using hc

private lemma gaussian_log (m x : ℝ) :
    Real.log (gaussianPDFReal m (1 / 2) x) = -Real.log Real.pi / 2 - (x - m) ^ 2 := by
  simp only [gaussianPDFReal, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
  rw [show 2 * Real.pi * (1 / 2) = Real.pi by ring,
    show (2 : ℝ) * (1 / 2) = 1 by norm_num, div_one,
    Real.log_mul (inv_ne_zero (Real.sqrt_pos.2 Real.pi_pos).ne') (Real.exp_ne_zero _),
    Real.log_inv, Real.log_sqrt Real.pi_pos.le, Real.log_exp]
  ring

private lemma gaussian_entropy (m : ℝ) :
    Integrable (fun x => gaussianPDFReal m (1 / 2) x *
      Real.log (gaussianPDFReal m (1 / 2) x)) ∧
    densityEntropy (gaussianPDFReal m (1 / 2)) =
      1 / 2 * Real.log (Real.pi * Real.exp 1) := by
  have hi := gaussian_moments m
  have hg := integrable_gaussianPDFReal m (1 / 2)
  have hp : Integrable (fun x => (x - m) ^ 2 * gaussianPDFReal m (1 / 2) x) := by
    convert (hi.2.1.sub (hi.1.const_mul (2 * m))).add (hg.const_mul (m ^ 2)) using 1
    ext x
    dsimp only [Pi.add_apply, Pi.sub_apply]
    ring
  have he (x : ℝ) : gaussianPDFReal m (1 / 2) x *
      Real.log (gaussianPDFReal m (1 / 2) x) =
      (-Real.log Real.pi / 2) * gaussianPDFReal m (1 / 2) x -
        (x - m) ^ 2 * gaussianPDFReal m (1 / 2) x := by
    rw [gaussian_log]
    ring
  refine ⟨((hg.const_mul _).sub hp).congr (Filter.Eventually.of_forall
    fun x => (he x).symm), ?_⟩
  simp only [densityEntropy, he]
  rw [integral_sub (hg.const_mul _) hp, integral_const_mul,
    integral_gaussianPDFReal_eq_one _ (by norm_num), hi.2.2.2.2,
    Real.log_mul Real.pi_ne_zero (Real.exp_ne_zero _), Real.log_exp]
  ring

private lemma binary_pointwise (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    -((a + b) / 2 * Real.log ((a + b) / 2)) ≤
      -(a * Real.log a + b * Real.log b) / 2 + (a + b) / 2 * Real.log 2 := by
  have step (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
      u * (Real.log u - Real.log 2) ≤ u * Real.log ((u + v) / 2) := by
    rcases hu.eq_or_lt with rfl | hu
    · simp
    have hh : 0 < u / 2 := by positivity
    have he := Real.log_le_log hh (show u / 2 ≤ (u + v) / 2 by linarith)
    rw [Real.log_div hu.ne' (by norm_num)] at he
    exact mul_le_mul_of_nonneg_left he hu.le
  have h1 := step a b ha hb
  have h2 := step b a hb ha
  rw [add_comm b a] at h2
  nlinarith

private lemma binary_entropy_bound (f g : ℝ → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfi : Integrable f) (hgi : Integrable g)
    (hfm : (∫ x, f x) = 1) (hgm : (∫ x, g x) = 1)
    (hfl : Integrable (fun x => f x * Real.log (f x)))
    (hgl : Integrable (fun x => g x * Real.log (g x)))
    (hql : Integrable (fun x => (f x + g x) / 2 * Real.log ((f x + g x) / 2))) :
    densityEntropy (fun x => (f x + g x) / 2) ≤
      (densityEntropy f + densityEntropy g) / 2 + Real.log 2 := by
  have hqi := (hfi.add hgi).div_const 2
  have hbase : Integrable (fun x => -(f x * Real.log (f x) + g x * Real.log (g x)) / 2) :=
    (hfl.add hgl).neg.div_const 2
  have hmix : Integrable (fun x => (f x + g x) / 2 * Real.log 2) :=
    hqi.mul_const (Real.log 2)
  have hmajor := hbase.add hmix
  have hi := integral_mono hql.neg hmajor (fun x => binary_pointwise (f x) (g x) (hf x) (hg x))
  dsimp only [Pi.add_apply, Pi.neg_apply] at hi
  rw [integral_neg, integral_add hbase hmix, integral_div, integral_neg, integral_add hfl hgl,
    integral_mul_const, integral_div, integral_add hfi hgi, hfm, hgm] at hi
  dsimp only [densityEntropy]
  linarith

private lemma mixture_entropy_integrable (d : ℝ) :
    Integrable (fun x => q d x * Real.log (q d x)) := by
  sorry

private lemma marginals (d : ℝ) :
    marginalX (witnessW d) = q d ∧ marginalP (witnessW d) = q d := by
  sorry

private lemma moments (d : ℝ) :
    meanX (witnessW d) = 0 ∧ meanP (witnessW d) = 0 ∧
    covarianceXX (witnessW d) = d ^ 2 + 1 / 2 ∧
    covariancePP (witnessW d) = d ^ 2 + 1 / 2 ∧
    covarianceXP (witnessW d) = d ^ 2 := by
  sorry

private lemma second_integrable (d : ℝ) :
    Integrable (fun r : ℝ × ℝ => (r.1 ^ 2 + r.2 ^ 2) * witnessW d r.1 r.2) := by
  sorry

private lemma entropy_upper (d : ℝ) :
    densityEntropy (q d) + densityEntropy (q d) ≤
      Real.log (Real.pi * Real.exp 1) + 2 * Real.log 2 := by
  have h := binary_entropy_bound (gaussianPDFReal d (1 / 2))
    (gaussianPDFReal (-d) (1 / 2)) (gaussianPDFReal_nonneg _ _)
    (gaussianPDFReal_nonneg _ _) (integrable_gaussianPDFReal _ _)
    (integrable_gaussianPDFReal _ _)
    (integral_gaussianPDFReal_eq_one _ (by norm_num))
    (integral_gaussianPDFReal_eq_one _ (by norm_num))
    (gaussian_entropy d).1 (gaussian_entropy (-d)).1 (mixture_entropy_integrable d)
  change densityEntropy (q d) ≤ _ at h
  rw [(gaussian_entropy d).2, (gaussian_entropy (-d)).2] at h
  linarith

private lemma correction_violation :
    2 * Real.log 2 < 1 / 2 * Real.log
      (((6 : ℝ) ^ 2 + 1 / 2) * (6 ^ 2 + 1 / 2) /
        (((6 : ℝ) ^ 2 + 1 / 2) * (6 ^ 2 + 1 / 2) - (6 ^ 2) ^ 2)) := by
  have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 16)
    (by norm_num : (16 : ℝ) < 5329 / 145)
  have he : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  rw [he] at h
  norm_num only [show (((6 : ℝ) ^ 2 + 1 / 2) * (6 ^ 2 + 1 / 2) /
    (((6 : ℝ) ^ 2 + 1 / 2) * (6 ^ 2 + 1 / 2) - (6 ^ 2) ^ 2)) =
      5329 / 145 by norm_num]
  linarith

/-- The equal mixture of coherent states with means `(6,6)` and `(-6,-6)` refutes
the universal covariance-corrected quadrature entropy inequality. -/
theorem result : ¬ claim := by
  intro h
  let m : Fin 2 → ℝ := ![6, -6]
  have hw : mixtureWigner 2 (fun _ => 1 / 2) m m
      (fun _ => 1 / 2) (fun _ => 0) (fun _ => 1 / 2) = witnessW 6 := by
    funext x p
    simp only [mixtureWigner, Fin.sum_univ_two, m, Matrix.cons_val_zero,
      Matrix.cons_val_one, witnessW]
    ring
  have hc := h 2 (fun _ => 1 / 2) m m (fun _ => 1 / 2) (fun _ => 0)
    (fun _ => 1 / 2) (fun _ => by norm_num) (by norm_num [Fin.sum_univ_two])
    (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num)
  dsimp only at hc
  rw [hw, (marginals 6).1, (marginals 6).2] at hc
  have hc := hc (mixture_entropy_integrable 6) (mixture_entropy_integrable 6)
    (second_integrable 6)
  rw [(moments 6).2.2.1, (moments 6).2.2.2.1, (moments 6).2.2.2.2] at hc
  have hu := entropy_upper 6
  have hv := correction_violation
  linarith

end D5.S3.Quantum.Measurements.EntropyPowerCovarianceUncertaintyRefutation
