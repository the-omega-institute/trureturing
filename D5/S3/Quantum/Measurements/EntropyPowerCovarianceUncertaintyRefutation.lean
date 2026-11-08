/- GID: D5/S3/Quantum/Measurements/EntropyPowerCovarianceUncertaintyRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurements/EntropyPowerCovarianceUncertaintyRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Measurements/EntropyPowerCovarianceUncertaintyRefutation.claim; result=D5/S3/Quantum/Measurements/EntropyPowerCovarianceUncertaintyRefutation.result; claim=D5/S3/Quantum/Measurements/EntropyPowerCovarianceUncertaintyRefutation.claim
   digest: A binary coherent-state mixture violates the covariance-corrected entropy bound. -/

import D5.S3.Entropy.Mixing.MixtureEntropyBracket
import D5.S3.Fourier.Asymptotics.GaussianComplexMoments

/-! A finite Gaussian-mixture counterexample to the covariance-corrected uncertainty relation
of Hertz, Jabbour and Cerf, arXiv:1702.07286v2, Section III.B.

The claim quantifies over finite mixtures of physical one-mode Gaussian Wigner densities.
This is a subclass of the source's all-state reading. Its refutation concerns mixed states;
it does not settle the corresponding pure-state or Wigner-entropy conjectures. -/

open MeasureTheory ProbabilityTheory
open D5.S3.Entropy.Mixing.MixtureEntropyBracket (mixture)
open scoped BigOperators NNReal

noncomputable section

namespace D5.S3.Quantum.Measurements.EntropyPowerCovarianceUncertaintyRefutation

/-- The one-mode Gaussian Wigner density, in units with Planck's constant equal to one. -/
def gaussianWigner (μx μp a b c x p : ℝ) : ℝ :=
  (2 * Real.pi * Real.sqrt (a * c - b ^ 2))⁻¹ *
    Real.exp (-(c * (x - μx) ^ 2 - 2 * b * (x - μx) * (p - μp) +
      a * (p - μp) ^ 2) / (2 * (a * c - b ^ 2)))

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
    let W := fun x p => mixture w
      (fun i y => gaussianWigner (μx i) (μp i) (a i) (b i) (c i) y p) x
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
  have hp := Real.sq_sqrt Real.pi_pos.le
  have hn := (Real.sqrt_pos.2 Real.pi_pos).ne'
  change (2 * Real.pi * Real.sqrt ((1 / 2) * (1 / 2) - (0 : ℝ) ^ 2))⁻¹ *
    Real.exp (-((1 / 2) * (x - u) ^ 2 - 2 * 0 * (x - u) * (p - v) +
      (1 / 2) * (p - v) ^ 2) / (2 * ((1 / 2) * (1 / 2) - (0 : ℝ) ^ 2))) = _
  simp only [gaussianPDFReal, NNReal.coe_div, NNReal.coe_one,
    NNReal.coe_ofNat]
  norm_num only [zero_pow, mul_zero, sub_zero, zero_mul, zero_add]
  rw [show 2 * Real.pi * (1 / 2) = Real.pi by ring]
  simp only [div_one]
  rw [show -((1 / 2 : ℝ) * (x - u) ^ 2 + 1 / 2 * (p - v) ^ 2) /
      (1 / 2) = -(x - u) ^ 2 + -(p - v) ^ 2 by ring, Real.exp_add]
  field_simp
  nlinarith

open D5.S3.Fourier.Asymptotics.GaussianComplexMoments in
private lemma gaussian_moments (m : ℝ) :
    Integrable (fun x => x * gaussianPDFReal m (1 / 2) x) ∧
    Integrable (fun x => x ^ 2 * gaussianPDFReal m (1 / 2) x) ∧
    (∫ x, x * gaussianPDFReal m (1 / 2) x) = m ∧
    (∫ x, x ^ 2 * gaussianPDFReal m (1 / 2) x) = m ^ 2 + 1 / 2 ∧
    (∫ x, (x - m) ^ 2 * gaussianPDFReal m (1 / 2) x) = 1 / 2 := by
  have hv : (1 / 2 : ℝ≥0) ≠ 0 := by norm_num
  have hpdf (x : ℝ) :
      gaussianDensity m (1 / 2) x =
        gaussianPDFReal m (1 / 2) x := by
    rw [gaussianDensity_eq_pdf m (1 / 2) (by norm_num) x]
    congr 1
  have hpow (n : ℕ) : Integrable (fun x => x ^ n * gaussianPDFReal m (1 / 2) x) := by
    apply (Integrable.iff_ofReal (𝕜 := ℂ)).mpr
    have h : Integrable (fun x =>
        densityMonomial m (1 / 2) n 0 x) :=
      density_monomial_integrable
        m (1 / 2) (by norm_num) n 0
    simpa only [densityMonomial,
      zero_mul, Complex.exp_zero, mul_one, hpdf, RCLike.ofReal_eq_complex_ofReal,
      Complex.ofReal_mul, Complex.ofReal_pow] using h
  have hmean : (∫ x, x * gaussianPDFReal m (1 / 2) x) = m := by
    have h := density_moment_one m (1 / 2) (by norm_num) 0
    dsimp only [densityMonomial, tiltedMean, gaussianMGF, gaussianExponent] at h
    simp only [zero_mul,
      mul_zero, add_zero, Complex.exp_zero, mul_one, pow_one, hpdf,
      ← Complex.ofReal_mul, integral_complex_ofReal] at h
    norm_num at h
    exact h
  have hsecond : (∫ x, x ^ 2 * gaussianPDFReal m (1 / 2) x) = m ^ 2 + 1 / 2 := by
    have h := density_moment_two m (1 / 2) (by norm_num) 0
    dsimp only [densityMonomial, tiltedMean, gaussianMGF, gaussianExponent] at h
    simp only [zero_mul,
      mul_zero, add_zero, Complex.exp_zero, mul_one, hpdf, ← Complex.ofReal_pow,
      ← Complex.ofReal_mul, integral_complex_ofReal] at h
    norm_num at h
    apply Complex.ofReal_injective
    push_cast
    exact h
  have hc := variance_fun_id_gaussianReal (μ := m) (v := (1 / 2))
  rw [variance_eq_integral measurable_id'.aemeasurable, integral_id_gaussianReal,
    integral_gaussianReal_eq_integral_smul hv] at hc
  refine ⟨?_, hpow 2, hmean, hsecond, ?_⟩
  · simpa only [pow_one] using hpow 1
  · simpa only [smul_eq_mul, mul_comm, NNReal.coe_div, NNReal.coe_one,
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
  change -(∫ x, gaussianPDFReal m (1 / 2) x * Real.log (gaussianPDFReal m (1 / 2) x)) = _
  simp_rw [he]
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
  change -(∫ x, (f x + g x) / 2 * Real.log ((f x + g x) / 2)) ≤
    (-(∫ x, f x * Real.log (f x)) + -(∫ x, g x * Real.log (g x))) / 2 + Real.log 2
  linarith

private lemma mixture_entropy_integrable (d : ℝ) :
    Integrable (fun x => q d x * Real.log (q d x)) := by
  have hqi : Integrable (q d) :=
    ((integrable_gaussianPDFReal d (1 / 2)).add
      (integrable_gaussianPDFReal (-d) (1 / 2))).div_const 2
  have hmajor : Integrable (fun x =>
      -(gaussianPDFReal d (1 / 2) x * Real.log (gaussianPDFReal d (1 / 2) x) +
        gaussianPDFReal (-d) (1 / 2) x * Real.log (gaussianPDFReal (-d) (1 / 2) x)) / 2 +
          q d x * Real.log 2) :=
    (((gaussian_entropy d).1.add (gaussian_entropy (-d)).1).neg.div_const 2).add
      (hqi.mul_const _)
  have hle (m x : ℝ) : gaussianPDFReal m (1 / 2) x ≤ 1 := by
    apply (Real.log_nonpos_iff (gaussianPDFReal_nonneg _ _ _)).1
    rw [gaussian_log]
    have hp : 0 ≤ Real.log Real.pi := Real.log_nonneg (le_trans (by norm_num) Real.two_le_pi)
    nlinarith [sq_nonneg (x - m)]
  have hnonneg (x : ℝ) : 0 ≤ q d x := by
    exact div_nonneg (add_nonneg (gaussianPDFReal_nonneg _ _ _)
      (gaussianPDFReal_nonneg _ _ _)) (by norm_num)
  have hupper (x : ℝ) : q d x ≤ 1 := by
    change (gaussianPDFReal d (1 / 2) x + gaussianPDFReal (-d) (1 / 2) x) / 2 ≤ 1
    linarith [hle d x, hle (-d) x]
  have hcont (m : ℝ) : Continuous (gaussianPDFReal m (1 / 2)) := by
    change Continuous (fun x : ℝ => (Real.sqrt (2 * Real.pi * (1 / 2)))⁻¹ *
      Real.exp (-(x - m) ^ 2 / (2 * (1 / 2))))
    fun_prop
  have hmeas : AEStronglyMeasurable (fun x => q d x * Real.log (q d x)) volume := by
    exact (Real.Continuous.mul_log (((hcont d).add (hcont (-d))).div_const 2)).aestronglyMeasurable
  apply hmajor.mono' hmeas
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonpos
    (Real.mul_log_nonpos (hnonneg x) (hupper x))]
  exact binary_pointwise _ _ (gaussianPDFReal_nonneg _ _ _)
    (gaussianPDFReal_nonneg _ _ _)

private lemma marginals (d : ℝ) :
    marginalX (witnessW d) = q d ∧ marginalP (witnessW d) = q d := by
  have hx (x : ℝ) : marginalX (witnessW d) x = q d x := by
    change (∫ p, (gaussianWigner d d (1 / 2) 0 (1 / 2) x p +
      gaussianWigner (-d) (-d) (1 / 2) 0 (1 / 2) x p) / 2) =
        (gaussianPDFReal d (1 / 2) x + gaussianPDFReal (-d) (1 / 2) x) / 2
    simp_rw [component_factor]
    rw [integral_div, integral_add
      ((integrable_gaussianPDFReal d (1 / 2)).const_mul _)
      ((integrable_gaussianPDFReal (-d) (1 / 2)).const_mul _),
      integral_const_mul, integral_const_mul,
      integral_gaussianPDFReal_eq_one _ (by norm_num),
      integral_gaussianPDFReal_eq_one _ (by norm_num)]
    simp only [mul_one]
  have hp (p : ℝ) : marginalP (witnessW d) p = q d p := by
    change (∫ x, (gaussianWigner d d (1 / 2) 0 (1 / 2) x p +
      gaussianWigner (-d) (-d) (1 / 2) 0 (1 / 2) x p) / 2) =
        (gaussianPDFReal d (1 / 2) p + gaussianPDFReal (-d) (1 / 2) p) / 2
    simp_rw [component_factor]
    rw [integral_div, integral_add
      ((integrable_gaussianPDFReal d (1 / 2)).mul_const _)
      ((integrable_gaussianPDFReal (-d) (1 / 2)).mul_const _),
      integral_mul_const, integral_mul_const,
      integral_gaussianPDFReal_eq_one _ (by norm_num),
      integral_gaussianPDFReal_eq_one _ (by norm_num)]
    simp only [one_mul]
  exact ⟨funext hx, funext hp⟩

private lemma witness_product (d : ℝ) (f g : ℝ → ℝ)
    (hfp : Integrable (fun x => f x * gaussianPDFReal d (1 / 2) x))
    (hfn : Integrable (fun x => f x * gaussianPDFReal (-d) (1 / 2) x))
    (hgp : Integrable (fun x => g x * gaussianPDFReal d (1 / 2) x))
    (hgn : Integrable (fun x => g x * gaussianPDFReal (-d) (1 / 2) x)) :
    Integrable (fun r : ℝ × ℝ => f r.1 * g r.2 * witnessW d r.1 r.2) ∧
    (∫ r : ℝ × ℝ, f r.1 * g r.2 * witnessW d r.1 r.2) =
      ((∫ x, f x * gaussianPDFReal d (1 / 2) x) *
        (∫ p, g p * gaussianPDFReal d (1 / 2) p) +
      (∫ x, f x * gaussianPDFReal (-d) (1 / 2) x) *
        (∫ p, g p * gaussianPDFReal (-d) (1 / 2) p)) / 2 := by
  have he (r : ℝ × ℝ) : f r.1 * g r.2 * witnessW d r.1 r.2 =
      ((f r.1 * gaussianPDFReal d (1 / 2) r.1) *
        (g r.2 * gaussianPDFReal d (1 / 2) r.2) +
      (f r.1 * gaussianPDFReal (-d) (1 / 2) r.1) *
        (g r.2 * gaussianPDFReal (-d) (1 / 2) r.2)) / 2 := by
    change f r.1 * g r.2 *
      ((gaussianWigner d d (1 / 2) 0 (1 / 2) r.1 r.2 +
        gaussianWigner (-d) (-d) (1 / 2) 0 (1 / 2) r.1 r.2) / 2) = _
    rw [component_factor, component_factor]
    ring
  constructor
  · exact (((hfp.mul_prod hgp).add (hfn.mul_prod hgn)).div_const 2).congr
      (Filter.Eventually.of_forall fun r => (he r).symm)
  · simp_rw [he]
    rw [MeasureTheory.Measure.volume_eq_prod, integral_div,
      integral_add (hfp.mul_prod hgp) (hfn.mul_prod hgn),
      integral_prod_mul (fun x => f x * gaussianPDFReal d (1 / 2) x)
        (fun p => g p * gaussianPDFReal d (1 / 2) p),
      integral_prod_mul (fun x => f x * gaussianPDFReal (-d) (1 / 2) x)
        (fun p => g p * gaussianPDFReal (-d) (1 / 2) p)]

private lemma moments (d : ℝ) :
    meanX (witnessW d) = 0 ∧ meanP (witnessW d) = 0 ∧
    covarianceXX (witnessW d) = d ^ 2 + 1 / 2 ∧
    covariancePP (witnessW d) = d ^ 2 + 1 / 2 ∧
    covarianceXP (witnessW d) = d ^ 2 := by
  have hi (m : ℝ) : Integrable (fun x => (1 : ℝ) * gaussianPDFReal m (1 / 2) x) := by
    simpa only [one_mul] using integrable_gaussianPDFReal m (1 / 2)
  have hn (m : ℝ) : (∫ x, gaussianPDFReal m (1 / 2) x) = 1 :=
    integral_gaussianPDFReal_eq_one m (by norm_num : (1 / 2 : ℝ≥0) ≠ 0)
  have hx := (witness_product d (fun x => x) (fun _ => 1)
    (gaussian_moments d).1 (gaussian_moments (-d)).1 (hi d) (hi (-d))).2
  have hp := (witness_product d (fun _ => 1) (fun p => p)
    (hi d) (hi (-d)) (gaussian_moments d).1 (gaussian_moments (-d)).1).2
  simp only [mul_one, one_mul, hn, (gaussian_moments d).2.2.1,
    (gaussian_moments (-d)).2.2.1, add_neg_cancel, zero_div] at hx hp
  have hxx := (witness_product d (fun x => x ^ 2) (fun _ => 1)
    (gaussian_moments d).2.1 (gaussian_moments (-d)).2.1 (hi d) (hi (-d))).2
  have hpp := (witness_product d (fun _ => 1) (fun p => p ^ 2)
    (hi d) (hi (-d)) (gaussian_moments d).2.1 (gaussian_moments (-d)).2.1).2
  have hxp := (witness_product d (fun x => x) (fun p => p)
    (gaussian_moments d).1 (gaussian_moments (-d)).1
    (gaussian_moments d).1 (gaussian_moments (-d)).1).2
  simp only [mul_one, one_mul, hn, (gaussian_moments d).2.2.2.1,
    (gaussian_moments (-d)).2.2.2.1] at hxx hpp
  simp only [(gaussian_moments d).2.2.1, (gaussian_moments (-d)).2.2.1] at hxp
  change meanX (witnessW d) = 0 at hx
  change meanP (witnessW d) = 0 at hp
  refine ⟨hx, hp, ?_, ?_, ?_⟩
  · change (∫ r : ℝ × ℝ, (r.1 - meanX (witnessW d)) ^ 2 * witnessW d r.1 r.2) = _
    rw [hx]
    simp only [sub_zero]
    linarith [hxx]
  · change (∫ r : ℝ × ℝ, (r.2 - meanP (witnessW d)) ^ 2 * witnessW d r.1 r.2) = _
    rw [hp]
    simp only [sub_zero]
    linarith [hpp]
  · change (∫ r : ℝ × ℝ, (r.1 - meanX (witnessW d)) *
      (r.2 - meanP (witnessW d)) * witnessW d r.1 r.2) = _
    rw [hx, hp]
    simp only [sub_zero]
    nlinarith [hxp]

private lemma second_integrable (d : ℝ) :
    Integrable (fun r : ℝ × ℝ => (r.1 ^ 2 + r.2 ^ 2) * witnessW d r.1 r.2) := by
  have hi (m : ℝ) : Integrable (fun x => (1 : ℝ) * gaussianPDFReal m (1 / 2) x) := by
    simpa only [one_mul] using integrable_gaussianPDFReal m (1 / 2)
  have hxx := (witness_product d (fun x => x ^ 2) (fun _ => 1)
    (gaussian_moments d).2.1 (gaussian_moments (-d)).2.1 (hi d) (hi (-d))).1
  have hpp := (witness_product d (fun _ => 1) (fun p => p ^ 2)
    (hi d) (hi (-d)) (gaussian_moments d).2.1 (gaussian_moments (-d)).2.1).1
  convert hxx.add hpp using 1
  ext r
  simp only [Pi.add_apply, mul_one, one_mul, add_mul]

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

private lemma correction_violation (d : ℝ) (hd : (16 : ℝ) ≤ d ^ 2) :
    2 * Real.log 2 < 1 / 2 * Real.log
      ((d ^ 2 + 1 / 2) * (d ^ 2 + 1 / 2) /
        ((d ^ 2 + 1 / 2) * (d ^ 2 + 1 / 2) - (d ^ 2) ^ 2)) := by
  have hden_eq : (d ^ 2 + 1 / 2) * (d ^ 2 + 1 / 2) - (d ^ 2) ^ 2 =
      d ^ 2 + 1 / 4 := by ring
  have hden : 0 < (d ^ 2 + 1 / 2) * (d ^ 2 + 1 / 2) - (d ^ 2) ^ 2 := by
    rw [hden_eq]
    nlinarith [sq_nonneg d]
  have hprod : 0 ≤ (d ^ 2 - 16) * d ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg d)
  have hratio : (16 : ℝ) <
      (d ^ 2 + 1 / 2) * (d ^ 2 + 1 / 2) /
        ((d ^ 2 + 1 / 2) * (d ^ 2 + 1 / 2) - (d ^ 2) ^ 2) := by
    apply (lt_div_iff₀ hden).2
    nlinarith [hprod]
  have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 16) hratio
  have he : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  rw [he] at h
  linarith

/-- The equal mixture of coherent states with means `(6,6)` and `(-6,-6)` refutes
the universal covariance-corrected quadrature entropy inequality. -/
theorem result : ¬ claim := by
  intro h
  let m : Fin 2 → ℝ := ![6, -6]
  have hw (x p : ℝ) : mixture (fun _ : Fin 2 => 1 / 2)
      (fun i y => gaussianWigner (m i) (m i) (1 / 2) 0 (1 / 2) y p) x = witnessW 6 x p := by
    change (∑ i : Fin 2, 1 / 2 * gaussianWigner (m i) (m i) (1 / 2) 0 (1 / 2) x p) =
      (gaussianWigner 6 6 (1 / 2) 0 (1 / 2) x p +
        gaussianWigner (-6) (-6) (1 / 2) 0 (1 / 2) x p) / 2
    simp only [Fin.sum_univ_two, m, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hc := h 2 (fun _ => 1 / 2) m m (fun _ => 1 / 2) (fun _ => 0)
    (fun _ => 1 / 2) (fun _ => by norm_num) (by norm_num [Fin.sum_univ_two])
    (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num)
  dsimp only at hc
  simp_rw [hw] at hc
  rw [(marginals 6).1, (marginals 6).2] at hc
  have hc := hc (mixture_entropy_integrable 6) (mixture_entropy_integrable 6)
    (second_integrable 6)
  rw [(moments 6).2.2.1, (moments 6).2.2.2.1, (moments 6).2.2.2.2] at hc
  have hu := entropy_upper 6
  have hv := correction_violation 6 (by norm_num : (16 : ℝ) ≤ 6 ^ 2)
  linarith

end D5.S3.Quantum.Measurements.EntropyPowerCovarianceUncertaintyRefutation
