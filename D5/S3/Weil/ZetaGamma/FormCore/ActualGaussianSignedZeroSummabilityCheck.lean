import D5.S3.Weil.ZetaGamma.FormCore.GaussianGammaDomainCheck
import D5.S3.Weil.ZetaBridge.ClassicExplicitFormula

/- SOURCE DRAFT, NOT COMPILED. Actual Gaussian consumer only.
   Append to a check importing the accepted GaussianGammaDomainCheck.
   Add this genuine supplier import to the IMPORT BLOCK:
     import D5.S3.Weil.ZetaBridge.ClassicExplicitFormula

   The complete zero-counting reciprocal weight is reused directly. It is
   not inferred from local finiteness or compact-test summability. The
   actual full-line transform envelope is paid below from the accepted
   translated jets, fourfold identity and actual even-B fold; no K/decay
   bound, RH, zero simplicity, finite truncation, or spectrum hypothesis
   is introduced.
-/

noncomputable section

namespace D5.S3.Weil.ZetaGamma.FormCore.ActualGaussianSignedZeroSummabilityDraft

open Real Set MeasureTheory Filter
open scoped Topology ComplexConjugate
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData
open D5.S3.Weil.ZetaBridge.ClassicExplicitFormula
open D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample
open D5.S3.Weil.ZetaGamma.FormCore.FullPhiTranslatedJetsDraft
open RHFourJetDraft

open private fullJet fullJet_continuous fullJet_deriv
  fullJet_eq_phi_derivative fullJet_zero_eq_phi literalGaussian
  correctedGaussian centeredGaussianCharge trig_product_integrable
  correctedGaussian_evenB_full_exponential_fold from
  D5.S3.Weil.ZetaGamma.FormCore.GaussianGammaDomainCheck

/-- The literal ordinary full-line transform of the actual source image. -/
def actualGaussianSpectrum (a : ℝ) (q z : ℂ) : ℂ :=
  ∫ r : ℝ, actualSuzukiEvenBProfile (correctedGaussian a q) r *
    Complex.exp (Complex.I*z*(r:ℂ))

theorem actualGaussianSpectrum_integrable {a : ℝ} (ha : 0 ≤ a)
    (q z : ℂ) (hz : |z.im| ≤ 1/2) :
    Integrable (fun r : ℝ => actualSuzukiEvenBProfile (correctedGaussian a q) r *
      Complex.exp (Complex.I*z*(r:ℂ))) volume :=
  (correctedGaussian_evenB_full_exponential_fold ha q z hz).1

private def phiJet (a : ℝ) (k : ℕ) (t : ℝ) : ℝ := fullJet k (a+t)

private theorem phiJet_continuous (a : ℝ) (k : ℕ) :
    Continuous (phiJet a k) :=
  (fullJet_continuous k).comp (continuous_const.add continuous_id)

private theorem phiJet_deriv (a : ℝ) (k : ℕ) (t : ℝ) :
    HasDerivAt (phiJet a k) (phiJet a (k+1) t) t := by
  convert! (fullJet_deriv k (a+t)).comp t ((hasDerivAt_id t).const_add a) using 1 <;>
    simp only [phiJet, add_comm, mul_one]

private theorem phiJet_integrable {a : ℝ} (ha : 0 ≤ a) (k : ℕ) :
    IntegrableOn (fun t : ℝ => |phiJet a k t| *exp (t/2)) (Ioi 0) := by
  apply IntegrableOn.congr_fun ((translated_phi_jets k ha).1) ?_ measurableSet_Ioi
  intro t ht
  have ht0 : 0 < t := ht
  dsimp only [phiJet]
  rw [fullJet_eq_phi_derivative k (by linarith : 0 < a+t)]
  ring

private theorem phiJet_tendsto {a : ℝ} (ha : 0 ≤ a) (k : ℕ) :
    Tendsto (fun t : ℝ => |phiJet a k t| *exp (t/2)) atTop (𝓝 0) := by
  apply ((translated_phi_jets k ha).2).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  dsimp only [phiJet]
  rw [fullJet_eq_phi_derivative k (by linarith : 0 < a+t)]
  ring

private def rayEnvelope (a : ℝ) : ℝ :=
  2*(jetBudget (phiJet a 0)+|phiJet a 1 0|+|phiJet a 3 0|+
    jetBudget (phiJet a 4))

private theorem jetBudget_nonneg (f : ℝ → ℝ) : 0 ≤ jetBudget f :=
  integral_nonneg (fun t => mul_nonneg (abs_nonneg _) (exp_nonneg _))

private theorem rayEnvelope_nonneg (a : ℝ) : 0 ≤ rayEnvelope a := by
  have h0 := jetBudget_nonneg (phiJet a 0)
  have h4 := jetBudget_nonneg (phiJet a 4)
  dsimp only [rayEnvelope]
  positivity

private theorem phi_cosineRay_fourfold {a : ℝ} (ha : 0 ≤ a)
    (z : ℂ) (hz : |z.im| ≤ 1/2) :
    z^2*(z^2*cosineRay (phiJet a 0) z+(phiJet a 1 0:ℂ)) =
      (phiJet a 3 0:ℂ)+cosineRay (phiJet a 4) z := by
  exact cosineRay_fourfold (phiJet a 0) (phiJet a 1) (phiJet a 2)
    (phiJet a 3) (phiJet a 4)
    (phiJet_continuous a 0) (phiJet_continuous a 2) (phiJet_continuous a 4)
    (fun t _ => phiJet_deriv a 0 t) (fun t _ => phiJet_deriv a 1 t)
    (fun t _ => phiJet_deriv a 2 t) (fun t _ => phiJet_deriv a 3 t)
    (phiJet_integrable ha 0) (phiJet_integrable ha 2) (phiJet_integrable ha 4)
    (phiJet_tendsto ha 0) (phiJet_tendsto ha 1)
    (phiJet_tendsto ha 2) (phiJet_tendsto ha 3) z hz

/-- The accepted denominator-free fourfold identity gives an actual high
    frequency bound. This proof never divides by a possibly zero spectral
    node: its explicit domain is norm z >= 1. -/
private theorem phi_cosineRay_high_product_bound {a : ℝ} (ha : 0 ≤ a)
    (z : ℂ) (hz : |z.im| ≤ 1/2) (hzn : 1 ≤ ‖z‖) :
    ‖z‖^2*‖cosineRay (phiJet a 0) z‖ ≤
      |phiJet a 1 0|+|phiJet a 3 0|+jetBudget (phiJet a 4) := by
  have hsq : 1 ≤ ‖z‖^2 := by nlinarith [norm_nonneg z]
  have houter :
      ‖z‖^2*‖z^2*cosineRay (phiJet a 0) z+(phiJet a 1 0:ℂ)‖ ≤
        |phiJet a 3 0|+jetBudget (phiJet a 4) := by
    calc
      _ = ‖z^2*(z^2*cosineRay (phiJet a 0) z+(phiJet a 1 0:ℂ))‖ := by
        rw [norm_mul, norm_pow]
      _ = ‖(phiJet a 3 0:ℂ)+cosineRay (phiJet a 4) z‖ := by
        rw [phi_cosineRay_fourfold ha z hz]
      _ ≤ ‖(phiJet a 3 0:ℂ)‖+‖cosineRay (phiJet a 4) z‖ := norm_add_le _ _
      _ ≤ _ := by
        simpa only [Complex.norm_real, Real.norm_eq_abs, add_comm] using
          add_le_add_left
            (cosineRay_norm_le (phiJet a 4) (phiJet_continuous a 4)
              (phiJet_integrable ha 4) z hz) ‖(phiJet a 3 0:ℂ)‖
  have hinner :
      ‖z^2*cosineRay (phiJet a 0) z+(phiJet a 1 0:ℂ)‖ ≤
        |phiJet a 3 0|+jetBudget (phiJet a 4) :=
    (le_mul_of_one_le_left (norm_nonneg _) hsq).trans houter
  calc
    _ = ‖z^2*cosineRay (phiJet a 0) z‖ := by rw [norm_mul, norm_pow]
    _ = ‖(z^2*cosineRay (phiJet a 0) z+(phiJet a 1 0:ℂ))-
        (phiJet a 1 0:ℂ)‖ := by congr 1; ring
    _ ≤ ‖z^2*cosineRay (phiJet a 0) z+(phiJet a 1 0:ℂ)‖+
        ‖(phiJet a 1 0:ℂ)‖ := norm_sub_le _ _
    _ ≤ _ := by
      have hh := add_le_add_right hinner ‖(phiJet a 1 0:ℂ)‖
      simpa only [Complex.norm_real, Real.norm_eq_abs, add_assoc, add_comm,
        add_left_comm] using hh

/-- The low frequency bound pays the whole closed half-strip, including
    z=0. Together with the four-jet high bound it gives a positive-denominator
    envelope with no finite-set exception or extra hypothesis. -/
private theorem phi_cosineRay_weighted_norm_le {a : ℝ} (ha : 0 ≤ a)
    (z : ℂ) (hz : |z.im| ≤ 1/2) :
    (1+‖z‖^2)*‖cosineRay (phiJet a 0) z‖ ≤ rayEnvelope a := by
  have hL := cosineRay_norm_le (phiJet a 0) (phiJet_continuous a 0)
    (phiJet_integrable ha 0) z hz
  have hL0 := jetBudget_nonneg (phiJet a 0)
  have hH0 : 0 ≤ |phiJet a 1 0|+|phiJet a 3 0|+jetBudget (phiJet a 4) :=
    add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))
      (jetBudget_nonneg (phiJet a 4))
  by_cases hsmall : ‖z‖ ≤ 1
  · have hsq : ‖z‖^2 ≤ 1 := by nlinarith [norm_nonneg z]
    have hm := mul_le_mul hL (show 1+‖z‖^2 ≤ 2 by linarith)
      (by positivity : (0:ℝ)≤1+‖z‖^2) hL0
    dsimp only [rayEnvelope]
    nlinarith [hm]
  · have hsq : 1 ≤ ‖z‖^2 := by nlinarith [norm_nonneg z]
    have hH := phi_cosineRay_high_product_bound ha z hz (le_of_not_ge hsmall)
    have hn : ‖cosineRay (phiJet a 0) z‖ ≤
        |phiJet a 1 0|+|phiJet a 3 0|+jetBudget (phiJet a 4) :=
      (le_mul_of_one_le_left (norm_nonneg _) hsq).trans hH
    dsimp only [rayEnvelope]
    nlinarith [hH, hn]

private theorem actualGaussianSpectrum_eq_cosine {a : ℝ} (ha : 0 ≤ a)
    (q z : ℂ) (hz : |z.im| ≤ 1/2) :
    actualGaussianSpectrum a q z =
      2*((Real.pi^(1/4:ℝ)/4:ℝ):ℂ)*
        (cosineRay (phiJet a 0) z-q*cosineRay (phiJet 0 0) z) := by
  have hia := (trig_product_integrable (phiJet a 0) (phiJet_continuous a 0)
    (phiJet_integrable ha 0) z hz).1
  have hi0 := (trig_product_integrable (phiJet 0 0) (phiJet_continuous 0 0)
    (phiJet_integrable (by norm_num : (0:ℝ)≤0) 0) z hz).1
  rw [actualGaussianSpectrum, (correctedGaussian_evenB_full_exponential_fold ha q z hz).2]
  calc
    _ = 2*(∫ t : ℝ in Ioi 0,
        ((Real.pi^(1/4:ℝ)/4:ℝ):ℂ)*
          (((phiJet a 0 t:ℝ):ℂ)*Complex.cos (z*(t:ℂ))-
            q*(((phiJet 0 0 t:ℝ):ℂ)*Complex.cos (z*(t:ℂ))))) := by
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      have ht0 : 0 < t := ht
      dsimp only
      rw [correctedGaussian_actualSuzukiEvenB ha, abs_of_pos ht0]
      dsimp only [phiJet]
      rw [fullJet_zero_eq_phi (by linarith : 0≤a+t),
        fullJet_zero_eq_phi (by linarith : 0≤(0:ℝ)+t)]
      simp only [zero_add]
      ring
    _ = _ := by
      rw [integral_const_mul, integral_sub hia (hi0.const_mul q), integral_const_mul]
      dsimp only [cosineRay]
      ring

private def actualSpectrumEnvelope (a : ℝ) (q : ℂ) : ℝ :=
  2*‖((Real.pi^(1/4:ℝ)/4:ℝ):ℂ)‖*(rayEnvelope a+‖q‖*rayEnvelope 0)

private theorem actualSpectrumEnvelope_nonneg (a : ℝ) (q : ℂ) :
    0 ≤ actualSpectrumEnvelope a q := by
  exact mul_nonneg (by positivity)
    (add_nonneg (rayEnvelope_nonneg a)
      (mul_nonneg (norm_nonneg q) (rayEnvelope_nonneg 0)))

theorem actualGaussianSpectrum_strip_envelope {a : ℝ} (ha : 0 ≤ a)
    (q z : ℂ) (hz : |z.im| ≤ 1/2) :
    ‖actualGaussianSpectrum a q z‖ ≤ actualSpectrumEnvelope a q/(1+‖z‖^2) := by
  have hA := phi_cosineRay_weighted_norm_le ha z hz
  have h0 := phi_cosineRay_weighted_norm_le (by norm_num : (0:ℝ)≤0) z hz
  have hV : ‖actualGaussianSpectrum a q z‖ ≤
      2*‖((Real.pi^(1/4:ℝ)/4:ℝ):ℂ)‖*
        (‖cosineRay (phiJet a 0) z‖+‖q‖*‖cosineRay (phiJet 0 0) z‖) := by
    rw [actualGaussianSpectrum_eq_cosine ha q z hz, norm_mul, norm_mul]
    norm_num only [Complex.norm_ofNat]
    apply mul_le_mul_of_nonneg_left ?_ (by positivity)
    simpa only [norm_mul] using
      norm_sub_le (cosineRay (phiJet a 0) z) (q*cosineRay (phiJet 0 0) z)
  apply (le_div_iff₀ (by positivity : (0:ℝ)<1+‖z‖^2)).2
  calc
    _ ≤ (2*‖((Real.pi^(1/4:ℝ)/4:ℝ):ℂ)‖*
        (‖cosineRay (phiJet a 0) z‖+‖q‖*‖cosineRay (phiJet 0 0) z‖)) *
          (1+‖z‖^2) := mul_le_mul_of_nonneg_right hV (by positivity)
    _ = 2*‖((Real.pi^(1/4:ℝ)/4:ℝ):ℂ)‖*
        ((1+‖z‖^2)*‖cosineRay (phiJet a 0) z‖+
          ‖q‖*((1+‖z‖^2)*‖cosineRay (phiJet 0 0) z‖)) := by ring
    _ ≤ actualSpectrumEnvelope a q :=
      mul_le_mul_of_nonneg_left
        (add_le_add hA (mul_le_mul_of_nonneg_left h0 (norm_nonneg q))) (by positivity)

/-- Exact transport of the existing complete zeta zero-counting weight.
    zero_sum_inv_sq is proved from a two-sided local count with multiplicity;
    neither RH nor local finiteness alone is used as a substitute. -/
private theorem actual_reciprocal_weight_summable :
    Summable (fun n : ℕ => (zetaZeroData.multiplicity n:ℝ)/
      (1+‖zetaZeroData.gamma n‖^2)) := by
  have hs := (zeroEquiv zetaZeroData).summable_iff.mpr
    (Zeta23.WeilEF.zero_sum_inv_sq Zeta23.zetaSeam)
  refine hs.congr fun n => ?_
  change (Zeta23.zeroMult (zetaZeroData.zero n):ℝ)/
    (1+Complex.normSq (Zeta23.gammaOf (zetaZeroData.zero n))) = _
  rw [← multiplicity_eq_zeroMult, gammaOf_eq_spectralParameter]
  simp only [ZeroData.gamma, Complex.normSq_eq_norm_sq]

/-- Full signed zero summands are absolutely summable, with the exact
    analytic multiplicities. Both gamma and conj gamma lie in the real
    half-strip used by the actual transform envelope. -/
theorem actualGaussian_signed_zero_sum_abs_summable {a : ℝ} (ha : 0 ≤ a) (q : ℂ) :
    Summable (fun n : ℕ => (zetaZeroData.multiplicity n:ℝ)*
      ‖actualGaussianSpectrum a q (zetaZeroData.gamma n)*
        conj (actualGaussianSpectrum a q (conj (zetaZeroData.gamma n)))‖) := by
  let K := actualSpectrumEnvelope a q
  have hK : 0 ≤ K := actualSpectrumEnvelope_nonneg a q
  apply Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (actual_reciprocal_weight_summable.mul_left (K^2))
  let z := zetaZeroData.gamma n
  let d := 1+‖z‖^2
  have hd : 0 < d := by dsimp only [d]; positivity
  have hd1 : 1 ≤ d := by dsimp only [d]; nlinarith [sq_nonneg ‖z‖]
  have hstrip : |z.im| ≤ 1/2 := by
    have hs := (zetaZeroData.zero_isNontrivial n).2
    have he : z.im = (1/2:ℝ)-(zetaZeroData.zero n).re := by
      dsimp only [z, ZeroData.gamma, spectralParameter]
      simp [D5.S3.Weil.Convention.criticalAbscissa]
      <;> ring
    rw [he, abs_le]
    constructor <;> linarith [hs.1, hs.2]
  have h1 : ‖actualGaussianSpectrum a q z‖ ≤ K/d :=
    actualGaussianSpectrum_strip_envelope ha q z hstrip
  have h2 : ‖actualGaussianSpectrum a q (conj z)‖ ≤ K/d := by
    simpa only [Complex.norm_conj] using
      actualGaussianSpectrum_strip_envelope ha q (conj z)
        (by simpa only [Complex.conj_im, abs_neg] using hstrip)
  have hprod : ‖actualGaussianSpectrum a q z*
      conj (actualGaussianSpectrum a q (conj z))‖ ≤ (K/d)*(K/d) := by
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul h1 h2 (norm_nonneg _) (div_nonneg hK hd.le)
  change (zetaZeroData.multiplicity n:ℝ)*
    ‖actualGaussianSpectrum a q z*conj (actualGaussianSpectrum a q (conj z))‖ ≤
      K^2*((zetaZeroData.multiplicity n:ℝ)/d)
  calc
    _ ≤ (zetaZeroData.multiplicity n:ℝ)*((K/d)*(K/d)) :=
      mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg _)
    _ = K^2*((zetaZeroData.multiplicity n:ℝ)/d^2) := by
      field_simp
      <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left (Nat.cast_nonneg _) hd (by nlinarith : d≤d^2))
      (sq_nonneg K)

/-- This is a convergent complex signed sum, rather than a sum of squared
    norms. Absolute convergence supplies no positivity statement. -/
theorem actualGaussian_signed_zero_sum_summable {a : ℝ} (ha : 0 ≤ a) (q : ℂ) :
    Summable (fun n : ℕ => (zetaZeroData.multiplicity n:ℂ)*
      actualGaussianSpectrum a q (zetaZeroData.gamma n)*
        conj (actualGaussianSpectrum a q (conj (zetaZeroData.gamma n)))) := by
  apply Summable.of_norm
  simpa only [norm_mul, Complex.norm_natCast, Complex.norm_conj, mul_assoc] using
    actualGaussian_signed_zero_sum_abs_summable ha q

/-- Dropping the positive analytic multiplicities gives the requested
    distinct-index absolute series as well. -/
theorem actualGaussian_signed_zero_sum_unweighted_abs_summable
    {a : ℝ} (ha : 0 ≤ a) (q : ℂ) :
    Summable (fun n : ℕ =>
      ‖actualGaussianSpectrum a q (zetaZeroData.gamma n)*
        conj (actualGaussianSpectrum a q (conj (zetaZeroData.gamma n)))‖) := by
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (actualGaussian_signed_zero_sum_abs_summable ha q)
  have hm : (1:ℝ) ≤ zetaZeroData.multiplicity n := by
    exact_mod_cast (Nat.succ_le_iff.mpr (zetaZeroData.multiplicity_pos n))
  exact le_mul_of_one_le_left (norm_nonneg _) hm

/-- The requested literal full-line statement, on the SAME actual centered
    Gaussian used by the H6/mean-zero/Gamma/nonzero/high-cap witness. -/
theorem actual_centered_gaussian_signed_zero_sum_abs_summable :
    let a : ℝ := Real.log (4/3:ℝ)/2
    let F : ℝ → ℂ := correctedGaussian a (centeredGaussianCharge a)
    Summable (fun n : ℕ => (zetaZeroData.multiplicity n:ℝ)*
      ‖(∫ r : ℝ, actualSuzukiEvenBProfile F r*
          Complex.exp (Complex.I*zetaZeroData.gamma n*(r:ℂ)))*
        conj (∫ r : ℝ, actualSuzukiEvenBProfile F r*
          Complex.exp (Complex.I*conj (zetaZeroData.gamma n)*(r:ℂ)))‖) := by
  exact actualGaussian_signed_zero_sum_abs_summable
    (div_pos (Real.log_pos (by norm_num : (1:ℝ)<4/3)) (by norm_num)).le _

end D5.S3.Weil.ZetaGamma.FormCore.ActualGaussianSignedZeroSummabilityDraft

#print axioms D5.S3.Weil.ZetaGamma.FormCore.ActualGaussianSignedZeroSummabilityDraft.actualGaussian_signed_zero_sum_summable
#print axioms D5.S3.Weil.ZetaGamma.FormCore.ActualGaussianSignedZeroSummabilityDraft.actual_centered_gaussian_signed_zero_sum_abs_summable

end
