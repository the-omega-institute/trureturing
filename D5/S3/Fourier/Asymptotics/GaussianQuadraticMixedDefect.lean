/- GID: D5/S3/Fourier/Asymptotics/GaussianQuadraticMixedDefect
   generality: G
   mirror-B: D5/B/S3/Fourier/Asymptotics/GaussianQuadraticMixedDefect
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Mixed characteristic functions of Gaussian linear and quadratic sums. -/

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal

namespace D5.S3.Fourier.Asymptotics.GaussianQuadraticMixedDefect

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The mixed characteristic function of a linear and a centered diagonal quadratic
Gaussian sum differs from the product by a quantity controlled by the largest quadratic
coefficient and the variance of the linear sum. The finite index type may be empty. -/
theorem result {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (G : ι → Ω → ℝ)
    (hG : ∀ j, HasLaw (G j) (gaussianReal 0 1) P) (hind : iIndepFun G P)
    (Y : Ω → ℝ) (hjoint : HasGaussianLaw (fun ω => (Y ω, fun j => G j ω)) P)
    (a : ι → ℝ) (M : ℝ) (hM : 0 ≤ M) (ha : ∀ j, |a j| ≤ M) :
    ‖charFun (P.map (fun ω => Y ω + ∑ j, a j * ((G j ω)^2 - 1))) 1 -
      charFun (P.map Y) 1 *
        charFun (P.map (fun ω => ∑ j, a j * ((G j ω)^2 - 1))) 1‖ ≤
      (M * Var[Y; P]) * Real.exp (M * Var[Y; P]) := by
  classical
  have hlinear (a b : ι → ℝ) (M : ℝ) (hM : 0 ≤ M) (ha : ∀ j, |a j| ≤ M) :
    ‖charFun (P.map (fun ω => ∑ j, (a j * ((G j ω)^2 - 1) + b j * G j ω))) 1 -
      charFun (P.map (fun ω => ∑ j, a j * ((G j ω)^2 - 1))) 1 *
        Complex.exp (-(∑ j, (b j : ℂ)^2) / 2)‖ ≤
      (M * ∑ j, (b j)^2) * Real.exp (M * ∑ j, (b j)^2) := by
    classical
    have hsingle (a b : ℝ) :
        charFun ((gaussianReal 0 1).map (fun x => a * (x^2 - 1) + b*x)) 1 =
          charFun ((gaussianReal 0 1).map (fun x => a * (x^2 - 1))) 1 *
            Complex.exp (-(b : ℂ)^2 / (2 * (1 - 2 * (a : ℂ) * I))) := by
      have hi (b : ℝ) :
          charFun ((gaussianReal 0 1).map (fun x => a * (x^2-1) + b*x)) 1 =
          (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ *
            (Real.pi / (1/2 - (a : ℂ)*I)) ^ (1/2 : ℂ) *
            Complex.exp (-(a : ℂ)*I - (b : ℂ)^2 / (2 * (1-2*(a : ℂ)*I))) := by
        rw [charFun_apply_real, integral_map (by fun_prop) (by fun_prop)]
        simp only [ofReal_one, one_mul]
        simp_rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0),
          Complex.real_smul, gaussianPDFReal]
        push_cast
        simp only [sub_zero, mul_one]
        simp_rw [mul_assoc, integral_const_mul, ← Complex.exp_add]
        have he (x : ℝ) :
            (-((x : ℂ)^2) / 2 + ((a : ℂ)*((x : ℂ)^2-1) + (b : ℂ)*x)*I) =
            ((a : ℂ)*I-1/2)*x^2 + ((b : ℂ)*I)*x + (-(a : ℂ)*I) := by ring
        simp_rw [he]
        rw [integral_cexp_quadratic (by simp)]
        rw [show -((a : ℂ)*I-1/2) = 1/2-(a : ℂ)*I by ring]
        congr 3
        rw [show 4*((a : ℂ)*I-1/2) = -(2*(1-2*((a : ℂ)*I))) by ring]
        simp only [mul_pow, I_sq, mul_neg_one, div_neg, neg_div, neg_neg]
      rw [hi]
      have hzero := hi 0
      simp only [zero_mul, add_zero, ofReal_zero, zero_pow (by decide : 2 ≠ 0),
        zero_div, sub_zero] at hzero
      rw [hzero]
      simp only [sub_eq_add_neg, neg_div, Complex.exp_add, mul_assoc]
    let F (j : ι) (ω : Ω) := a j * ((G j ω)^2-1)
    let H (j : ι) (ω : Ω) := F j ω + b j * G j ω
    let z (j : ι) : ℂ := 1 - 2 * (a j : ℂ) * I
    let D : ℂ := ∑ j, (-(b j : ℂ)^2 / (2*z j) + (b j : ℂ)^2 / 2)
    have hchar (j : ι) : charFun (P.map (H j)) 1 =
        charFun (P.map (F j)) 1 * Complex.exp (-(b j : ℂ)^2 / (2*z j)) := by
      have hm (f : ℝ → ℝ) (hf : Measurable f) :
          P.map (f ∘ G j) = (gaussianReal 0 1).map f := by
        rw [← AEMeasurable.map_map_of_aemeasurable hf.aemeasurable (hG j).aemeasurable,
          (hG j).map_eq]
      change charFun (P.map ((fun x => a j * (x^2-1)+b j*x) ∘ G j)) 1 =
        charFun (P.map ((fun x => a j * (x^2-1)) ∘ G j)) 1 * _
      rw [hm _ (by fun_prop), hm _ (by fun_prop)]
      exact hsingle (a j) (b j)
    have hindF : iIndepFun F P := hind.comp (fun j x => a j*(x^2-1)) (fun _ => by fun_prop)
    have hindH : iIndepFun H P := hind.comp (fun j x => a j*(x^2-1)+b j*x)
      (fun _ => by fun_prop)
    have hprod : charFun (P.map (fun ω => ∑ j, H j ω)) 1 =
        charFun (P.map (fun ω => ∑ j, F j ω)) 1 *
          Complex.exp (-(∑ j, (b j : ℂ)^2)/2) * Complex.exp D := by
      rw [hindH.charFun_map_fun_sum_eq_prod (fun j => by
          dsimp [H, F]; fun_prop), hindF.charFun_map_fun_sum_eq_prod (fun j => by
          dsimp [F]; fun_prop)]
      simp only [Finset.prod_apply, hchar, Finset.prod_mul_distrib, ← Complex.exp_sum]
      rw [mul_assoc, ← Complex.exp_add]
      congr 2
      dsimp [D]
      simp only [Finset.sum_add_distrib, ← Finset.sum_div]
      ring
    have hD : ‖D‖ ≤ M * ∑ j, (b j)^2 := by
      calc
        ‖D‖ ≤ ∑ j, ‖-(b j : ℂ)^2 / (2*z j) + (b j : ℂ)^2/2‖ := norm_sum_le _ _
        _ ≤ ∑ j, M * (b j)^2 := by
          apply Finset.sum_le_sum
          intro j hj
          have hre : (z j).re = 1 := by simp [z]
          have hn : 1 ≤ ‖z j‖ := by
            simpa [hre] using Complex.abs_re_le_norm (z j)
          have hz : z j ≠ 0 := by intro h; norm_num [h] at hn
          have he : -(b j : ℂ)^2 / (2*z j) + (b j : ℂ)^2/2 =
              -(a j : ℂ)*I*(b j : ℂ)^2 / z j := by
            field_simp
            dsimp [z]
            ring
          rw [he, norm_div]
          calc
            _ ≤ ‖-(a j : ℂ)*I*(b j : ℂ)^2‖ := div_le_self (norm_nonneg _) hn
            _ = |a j| * (b j)^2 := by simp [sq_abs]
            _ ≤ M * (b j)^2 := mul_le_mul_of_nonneg_right (ha j) (sq_nonneg _)
        _ = _ := (Finset.mul_sum ..).symm
    have hA : ‖charFun (P.map (fun ω => ∑ j, F j ω)) 1‖ ≤ 1 := by
      have hm : AEMeasurable (fun ω => ∑ j, F j ω) P := by dsimp [F]; fun_prop
      have := Measure.isProbabilityMeasure_map hm
      exact norm_charFun_le_one _
    have hB : ‖Complex.exp (-(∑ j, (b j : ℂ)^2)/2)‖ ≤ 1 := by
      rw [Complex.norm_exp, Real.exp_le_one_iff]
      have hs : (∑ j, (b j : ℂ)^2) = ((∑ j, (b j)^2 : ℝ) : ℂ) := by simp
      rw [hs]
      simp only [← ofReal_neg, ← ofReal_ofNat, ← ofReal_div, ofReal_re]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Finset.sum_nonneg fun j _ => sq_nonneg _)) (by norm_num)
    have he : ‖Complex.exp D - 1‖ ≤ ‖D‖ * Real.exp ‖D‖ := by
      simpa using Complex.norm_exp_sub_sum_le_norm_mul_exp D 1
    change ‖charFun (P.map (fun ω => ∑ j, H j ω)) 1 -
      charFun (P.map (fun ω => ∑ j, F j ω)) 1 * _‖ ≤ _
    rw [hprod, ← mul_sub_one, norm_mul]
    calc
      _ ≤ 1 * ‖Complex.exp D - 1‖ := by
        gcongr
        rw [norm_mul]
        exact mul_le_one₀ hA (norm_nonneg _) hB
      _ ≤ ‖D‖ * Real.exp ‖D‖ := by simpa using he
      _ ≤ _ := by gcongr
  let b (j : ι) : ℝ := cov[Y, G j; P]
  let L : (ι → ℝ) →L[ℝ] ℝ := ∑ j, b j • ContinuousLinearMap.proj j
  let S (ω : Ω) : ℝ := ∑ j, b j * G j ω
  let R (ω : Ω) : ℝ := Y ω - S ω
  have hYL : HasGaussianLaw Y P := hjoint.fst
  have hGL (j : ι) : HasGaussianLaw (G j) P := hjoint.snd.eval j
  have hSL : HasGaussianLaw S P := by
    convert! hjoint.snd.map L using 1
    ext ω
    simp [S, L, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
  have hRL : HasGaussianLaw R P := by
    convert! hjoint.map
      (ContinuousLinearMap.fst ℝ ℝ (ι → ℝ) - L.comp (ContinuousLinearMap.snd ℝ ℝ (ι → ℝ)))
      using 1
    ext ω
    simp [R, S, L, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
  have hcov (i j : ι) : cov[G i, G j; P] = if i = j then 1 else 0 := by
    split_ifs with h
    · subst j
      rw [covariance_self (hG i).aemeasurable, (hG i).variance_eq, variance_id_gaussianReal]
      norm_num
    · exact (hind.indepFun h).covariance_eq_zero (hGL i).memLp_two (hGL j).memLp_two
  have hRG (j : ι) : cov[R, G j; P] = 0 := by
    dsimp [R]
    rw [covariance_fun_sub_left hYL.memLp_two hSL.memLp_two (hGL j).memLp_two]
    dsimp [S]
    rw [covariance_fun_sum_left (fun i => (hGL i).memLp_two.const_mul (b i))
      (hGL j).memLp_two]
    simp_rw [covariance_const_mul_left, hcov]
    simp [b]
  have hRind : IndepFun R (fun ω j => G j ω) P := by
    have hJ : HasGaussianLaw (fun ω => (fun _ : Unit => R ω, fun j => G j ω)) P := by
      let A := ContinuousLinearMap.fst ℝ ℝ (ι → ℝ) -
        L.comp (ContinuousLinearMap.snd ℝ ℝ (ι → ℝ))
      convert! hjoint.map ((ContinuousLinearMap.pi (fun _ : Unit => A)).prod
        (ContinuousLinearMap.snd ℝ ℝ (ι → ℝ))) using 1
      ext ω u
      · simp [A, R, S, L, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
      · rfl
    have hi := hJ.indepFun_of_covariance_eval (fun _ j => hRG j)
    simpa only [Function.comp_def, id_eq] using
      hi.comp (measurable_pi_apply ()) measurable_id
  have hmean (j : ι) : P[G j] = 0 := by
    rw [(hG j).integral_eq, integral_id_gaussianReal]
  have hmeanS : P[S] = 0 := by
    dsimp [S]
    rw [integral_finsetSum _ (fun i _ => (hGL i).integrable.const_mul (b i))]
    simp [integral_const_mul, hmean]
  have hvarS : Var[S; P] = ∑ j, (b j)^2 := by
    dsimp [S]
    rw [variance_fun_sum (fun j => (hGL j).memLp_two.const_mul (b j))]
    simp_rw [covariance_const_mul_left, covariance_const_mul_right, hcov]
    simp [pow_two]
  have hRS : IndepFun R S P := by
    convert! hRind.comp measurable_id L.continuous.measurable using 1
    ext ω
    simp [Function.comp_def, S, L, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply]
  have hvar : Var[R; P] + ∑ j, (b j)^2 = Var[Y; P] := by
    rw [← hvarS, ← hRS.variance_add hRL.memLp_two hSL.memLp_two]
    congr 1
    ext ω
    simp [R]
  have hb : ∑ j, (b j)^2 ≤ Var[Y; P] := by
    have := variance_nonneg R P
    linarith
  have hcfS : charFun (P.map S) 1 = Complex.exp (-(∑ j, (b j : ℂ)^2)/2) := by
    rw [hSL.charFun_map_eq]
    simpa [RCLike.inner_apply, hmeanS, hvarS, ← ofReal_sum, ← ofReal_pow, neg_div]
  let Q (ω : Ω) := ∑ j, a j * ((G j ω)^2-1)
  have hmQ : AEMeasurable Q P := by dsimp [Q]; fun_prop
  have hRQ : IndepFun R (fun ω => S ω + Q ω) P := by
    convert! hRind.comp measurable_id
      (show Measurable (fun x : ι → ℝ => (∑ j, b j*x j) + ∑ j, a j*((x j)^2-1)) by
        fun_prop) using 1
  have hY : charFun (P.map Y) 1 = charFun (P.map R) 1 * charFun (P.map S) 1 := by
    have he : Y = fun ω => R ω + S ω := by ext ω; simp [R]
    rw [he, hRS.charFun_map_fun_add_eq_mul hRL.aemeasurable hSL.aemeasurable]
    rfl
  have hsum : charFun (P.map (fun ω => Y ω + Q ω)) 1 =
      charFun (P.map R) 1 * charFun (P.map (fun ω => S ω + Q ω)) 1 := by
    have he : (fun ω => Y ω + Q ω) = fun ω => R ω + (S ω + Q ω) := by
      ext ω
      dsimp [R]
      ring
    rw [he]
    exact congrFun (hRQ.charFun_map_fun_add_eq_mul hRL.aemeasurable
      (hSL.aemeasurable.add hmQ)) 1
  have heq : (fun ω => S ω + Q ω) =
      fun ω => ∑ j, (a j*((G j ω)^2-1)+b j*G j ω) := by
    ext ω
    simp [S, Q, Finset.sum_add_distrib, add_comm]
  change ‖charFun (P.map (fun ω => Y ω + Q ω)) 1 -
    charFun (P.map Y) 1 * charFun (P.map Q) 1‖ ≤ _
  rw [hsum, hY, hcfS]
  have hid (x y z w : ℂ) : x*y - (x*z)*w = x*(y-w*z) := by ring
  rw [hid, norm_mul]
  have hnR : ‖charFun (P.map R) 1‖ ≤ 1 := by
    have := Measure.isProbabilityMeasure_map hRL.aemeasurable
    exact norm_charFun_le_one _
  calc
    _ ≤ 1 * ‖charFun (P.map (fun ω => S ω + Q ω)) 1 -
        charFun (P.map Q) 1 * Complex.exp (-(∑ j, (b j : ℂ)^2)/2)‖ := by gcongr
    _ ≤ (M * ∑ j, (b j)^2) * Real.exp (M * ∑ j, (b j)^2) := by
      simpa only [one_mul, heq] using hlinear a b M hM ha
    _ ≤ _ := by
      gcongr
      exact mul_nonneg hM (variance_nonneg Y P)

end D5.S3.Fourier.Asymptotics.GaussianQuadraticMixedDefect
