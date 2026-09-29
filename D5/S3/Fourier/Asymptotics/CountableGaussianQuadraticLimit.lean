/- GID: D5/S3/Fourier/Asymptotics/CountableGaussianQuadraticLimit
   generality: G
   mirror-B: D5/B/S3/Fourier/Asymptotics/CountableGaussianQuadraticLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Countable Gaussian quadratic sums converge to a Gaussian, including zero variance. -/

import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic
open MeasureTheory ProbabilityTheory Filter Complex
open scoped Topology ENNReal NNReal

namespace D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Square-summable rows of independent standard Gaussian squares, centered and weighted
by uniformly vanishing coefficients, converge in law to the Gaussian with the limiting variance.
The sums are constructed in L² and zero limiting variance is included. -/
theorem result (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (G : ℕ → ℕ → Ω → ℝ) (a : ℕ → ℕ → ℝ) (v : ℝ≥0)
  (hG : ∀ n j, HasLaw (G n j) (gaussianReal 0 1) P)
  (hind : ∀ n, iIndepFun (G n) P)
  (ha : ∀ n, Summable (fun j => (a n j) ^ 2))
  (hM : Tendsto (fun n => ⨆ j, |a n j|) atTop (𝓝 0))
  (hS : Tendsto (fun n => ∑' j, (a n j) ^ 2) atTop (𝓝 ((v : ℝ) / 2))) :
  ∃ (hmem : ∀ n j, MemLp (fun ω => a n j * ((G n j ω) ^ 2 - 1)) 2 P)
    (Q : ℕ → Lp ℝ 2 P),
    (∀ n, HasSum (fun j => (hmem n j).toLp
      (fun ω => a n j * ((G n j ω) ^ 2 - 1))) (Q n)) ∧
    TendstoInDistribution (fun n => ⇑(Q n)) atTop (id : ℝ → ℝ)
      (fun _ => P) (gaussianReal 0 v) := by
  classical
  have hrow (G : ℕ → Ω → ℝ) (a : ℕ → ℝ)
      (hG : ∀ j, HasLaw (G j) (gaussianReal 0 1) P)
      (hind : iIndepFun G P) (ha : Summable (fun j => (a j) ^ 2)) :
      ∃ (hm : ∀ j, MemLp (fun ω => a j * ((G j ω) ^ 2 - 1)) 2 P)
        (Q : Lp ℝ 2 P),
        HasSum (fun j => (hm j).toLp (fun ω => a j * ((G j ω) ^ 2 - 1))) Q := by
    classical
    have hfour : (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1) = 3 := by
      have hd (x : ℝ) : HasDerivAt (fun t : ℝ => Real.exp (t ^ 2 / 2))
          (x * Real.exp (x ^ 2 / 2)) x := by
        convert (((hasDerivAt_id x).pow 2).div_const 2).exp using 1 <;>
          simp only [Pi.pow_def, id_eq] <;> ring
      have hd1 : deriv (fun t : ℝ => Real.exp (t ^ 2 / 2)) =
          fun t => t * Real.exp (t ^ 2 / 2) := funext (fun t => (hd t).deriv)
      have hd2 : deriv (fun t : ℝ => t * Real.exp (t ^ 2 / 2)) =
          fun t => (1+t ^ 2) * Real.exp (t ^ 2 / 2) := by
        ext t
        convert ((hasDerivAt_id t).mul (hd t)).deriv using 1 <;>
          simp only [Pi.mul_def, id_eq] <;> ring
      have hd3 : deriv (fun t : ℝ => (1+t ^ 2) * Real.exp (t ^ 2 / 2)) =
          fun t => (3 * t+t ^ 3) * Real.exp (t ^ 2 / 2) := by
        ext t
        convert (((hasDerivAt_const t 1).add ((hasDerivAt_id t).pow 2)).mul (hd t)).deriv
          using 1 <;> simp only [Pi.mul_def, Pi.add_def, Pi.pow_def, id_eq] <;> ring
      have h4 := ((((hasDerivAt_id (0 : ℝ)).const_mul 3).add
          ((hasDerivAt_id 0).pow 3)).mul (hd 0)).deriv
      have hm := iteratedDeriv_mgf_zero (X := (id : ℝ → ℝ)) (μ := gaussianReal 0 1)
        (by simp [integrableExpSet_id_gaussianReal]) 4
      simp only [Pi.pow_apply, id_eq] at hm
      rw [← hm, mgf_id_gaussianReal]
      simp only [zero_mul, NNReal.coe_one, one_mul, zero_add]
      norm_num only [iteratedDeriv_succ, iteratedDeriv_zero]
      rw [hd1, hd2, hd3]
      simpa only [Pi.mul_def, Pi.add_def, Pi.pow_def, id_eq, zero_pow (by omega : 3 ≠ 0),
        zero_pow (by omega : 2 ≠ 0), mul_zero, zero_add, zero_div, Real.exp_zero,
        mul_one, one_mul, add_zero] using h4
    have hLp (j : ℕ) (p : ℝ≥0) : MemLp (G j) p P := by
      have hm : MemLp id p (P.map (G j)) := by
        rw [(hG j).map_eq]
        exact memLp_id_gaussianReal p
      simpa only [Function.id_comp] using
        (memLp_map_measure_iff aestronglyMeasurable_id (hG j).aemeasurable).mp hm
    have hh : ENNReal.HolderTriple 4 4 2 := ⟨by
      apply (ENNReal.toReal_eq_toReal_iff' (by simp) (by simp)).mp
      norm_num [ENNReal.toReal_add]⟩
    have hs (j : ℕ) : MemLp (fun ω => (G j ω) ^ 2) 2 P := by
      have h4 : MemLp (G j) 4 P := by simpa using hLp j 4
      simpa only [pow_two, Pi.mul_def] using
        (h4.mul h4 : MemLp (G j * G j) 2 P)
    let Y : ℕ → Ω → ℝ := fun j ω => (G j ω) ^ 2 - 1
    have hY (j : ℕ) : MemLp (Y j) 2 P := (hs j).sub (memLp_const (1 : ℝ))
    have hm (j : ℕ) : MemLp (fun ω => a j * Y j ω) 2 P := (hY j).const_mul (a j)
    have hmeanG (j : ℕ) : (∫ ω, G j ω ∂P) = 0 := by
      rw [(hG j).integral_eq, integral_id_gaussianReal]
    have hsecond (j : ℕ) : (∫ ω, (G j ω) ^ 2 ∂P) = 1 := by
      have hv := variance_eq_sub (hLp j 2)
      rw [(hG j).variance_eq, variance_id_gaussianReal, hmeanG] at hv
      simpa using hv.symm
    have hfourG (j : ℕ) : (∫ ω, (G j ω) ^ 4 ∂P) = 3 := by
      exact ((hG j).integral_comp (f := fun x : ℝ => x ^ 4) (by fun_prop)).trans hfour
    have hmeanY (j : ℕ) : (∫ ω, Y j ω ∂P) = 0 := by
      dsimp [Y]
      rw [integral_sub ((hs j).integrable (by norm_num)) (integrable_const 1), hsecond]
      simp
    have hYY (j : ℕ) : (∫ ω, (Y j ω) ^ 2 ∂P) = 2 := by
      have hsqint := (hs j).integrable_sq
      have hid : (fun ω => (Y j ω) ^ 2) =
          (fun ω => (G j ω) ^ 4 - 2 * (G j ω) ^ 2 + 1) := by
        funext ω
        dsimp [Y]
        ring
      rw [hid, integral_add, integral_sub, integral_const_mul, hfourG, hsecond]
      · norm_num
      · convert hsqint using 1
        ext ω
        ring
      · exact ((hs j).integrable (by norm_num)).const_mul 2
      · exact (hsqint.congr (by filter_upwards [] with ω; ring)).sub
          (((hs j).integrable (by norm_num)).const_mul 2)
      · exact integrable_const 1
    have hindY : iIndepFun Y P := hind.comp (fun _ x => x ^ 2-1) (fun _ => by fun_prop)
    let X (j : ℕ) : Lp ℝ 2 P := (hY j).toLp (Y j)
    have hXinner (i j : ℕ) : inner ℝ (X i) (X j) = if i = j then 2 else 0 := by
      rw [L2.inner_def]
      have heq : (fun ω => inner ℝ (X i ω) (X j ω)) =ᵐ[P]
          (fun ω => Y i ω * Y j ω) := by
        filter_upwards [(hY i).coeFn_toLp, (hY j).coeFn_toLp] with ω hi hj
        simp [X, hi, hj, mul_comm]
      rw [integral_congr_ae heq]
      split_ifs with hij
      · subst j
        simpa only [pow_two] using hYY i
      · simpa only [Pi.mul_apply, hmeanY, zero_mul] using
          (hindY.indepFun hij).integral_mul_eq_mul_integral
            (hY i).aestronglyMeasurable (hY j).aestronglyMeasurable
    let e (j : ℕ) : Lp ℝ 2 P := (Real.sqrt 2)⁻¹ • X j
    have he : Orthonormal ℝ e := by
      rw [orthonormal_iff_ite]
      intro i j
      dsimp [e]
      rw [inner_smul_left, inner_smul_right, hXinner]
      simp only [conj_trivial]
      split_ifs with hij
      · have hh2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
        have hh0 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
        field_simp
        nlinarith
      · simp
    have hsumm : Summable (fun j => (a j * Real.sqrt 2) • e j) := by
      have h := (he.orthogonalFamily.summable_iff_norm_sq_summable
        (fun j => a j * Real.sqrt 2)).2 ?_
      · simpa using h
      · simpa [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] using ha.mul_right 2
    have hsame (j : ℕ) : (a j * Real.sqrt 2) • e j = (hm j).toLp (fun ω => a j * Y j ω) := by
      dsimp [e, X]
      rw [smul_smul]
      have hc : a j * Real.sqrt 2 * (Real.sqrt 2)⁻¹ = a j := by
        field_simp
      rw [hc]
      exact (MemLp.toLp_const_smul (a j) (hY j)).symm
    simp_rw [hsame] at hsumm
    exact ⟨hm, _, hsumm.hasSum⟩
  choose hmem Q hQ using fun n => hrow (G n) (a n) (hG n) (hind n) (ha n)
  have hsingle (G : Ω → ℝ) (hG : HasLaw G (gaussianReal 0 1) P) (u : ℝ) :
      charFun (P.map (fun ω => (G ω) ^ 2 - 1)) u =
        cexp (-(u : ℂ) * I - Complex.log (1 - 2 * (u : ℂ) * I) / 2) := by
    have hcf : charFun (P.map (fun ω => (G ω) ^ 2 - 1)) u =
      (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ *
        (Real.pi / (1 / 2 - (u : ℂ) * I)) ^ (1 / 2 : ℂ) * cexp (-(u : ℂ) * I) := by
      rw [charFun_apply_real, integral_map ((hG.aemeasurable.pow_const 2).sub_const 1)
        (by fun_prop)]
      calc
        _ = ∫ x : ℝ, cexp ((u : ℂ) * I * ((x : ℂ) ^ 2 - 1)) ∂gaussianReal 0 1 := by
          convert hG.integral_comp (f := fun x : ℝ => cexp ((u : ℂ) * I * ((x : ℂ) ^ 2-1)))
            (by fun_prop) using 1
          congr 1
          ext ω
          simp only [Function.comp_apply]
          push_cast
          congr 1
          ring
        _ = (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ *
            ∫ x : ℝ, cexp (((u : ℂ) * I - 1 / 2) * x ^ 2 + 0 * x + (-(u : ℂ) * I)) := by
          simp_rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0),
            Complex.real_smul, gaussianPDFReal]
          push_cast
          simp only [sub_zero, mul_one]
          simp_rw [mul_assoc, integral_const_mul, ← Complex.exp_add]
          congr 1
          congr with x
          congr 1
          ring
        _ = _ := by
          rw [integral_cexp_quadratic (by simp), ← mul_assoc]
          congr 2 <;> congr 1 <;> ring
    rw [hcf]
    let z : ℂ := 1 - 2 * (u : ℂ) * I
    have hzre : z.re = 1 := by simp [z]
    have hz : z ≠ 0 := by intro h; simp [h] at hzre
    have hbranch : z.arg ≠ Real.pi := by
      apply Complex.slitPlane_arg_ne_pi
      exact Or.inl (by simp [hzre] : (0 : ℝ) < z.re)
    have hpi : (0 : ℝ) < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
    have hb : (1 / 2 - (u : ℂ) * I) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      norm_num at this
    have hratio : (Real.pi / (1 / 2 - (u : ℂ) * I)) = (2 * Real.pi : ℝ) * z⁻¹ := by
      dsimp [z]
      push_cast
      field_simp
    have hpz : (↑(2 * Real.pi) : ℂ) * z⁻¹ ≠ 0 :=
      mul_ne_zero (Complex.ofReal_ne_zero.mpr hpi.ne') (inv_ne_zero hz)
    rw [hratio, Complex.cpow_def_of_ne_zero hpz,
      Complex.log_ofReal_mul hpi (inv_ne_zero hz), Complex.log_inv z hbranch]
    have heq : ((Real.log (2 * Real.pi) : ℂ) + -Complex.log z) * (1 / 2 : ℂ) =
        (Real.log (2 * Real.pi) : ℂ) / 2 - Complex.log z / 2 := by ring
    rw [heq, sub_eq_add_neg, Complex.exp_add]
    have hsqrt : cexp ((Real.log (2 * Real.pi) : ℂ) / 2) = (Real.sqrt (2 * Real.pi) : ℂ) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hpi]
      push_cast
      congr 1
      ring
    rw [hsqrt]
    have hs0 : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hpi).ne'
    rw [← mul_assoc, inv_mul_cancel₀ hs0, one_mul, ← Complex.exp_add]
    congr 1
    dsimp [z]
    ring
  have hlocal (t a M : ℝ) (ha : |a| ≤ M) (hM : 2 * |t| * M ≤ 1 / 2) :
      ‖-(t : ℂ) * (a : ℂ) * I - log (1-2 * (t : ℂ) * (a : ℂ) * I) / 2 + (t : ℂ) ^ 2 * (a : ℂ) ^ 2‖ ≤
        (8 / 3 : ℝ) * |t| ^ 3 * M * a ^ 2 := by
    let z : ℂ := -2 * (t : ℂ) * (a : ℂ) * I
    have hz : ‖z‖ = 2 * |t| * |a| := by simp [z]
    have hzhalf : ‖z‖ ≤ 1 / 2 := by
      rw [hz]
      exact (mul_le_mul_of_nonneg_left ha (by positivity)).trans hM
    have hzlt : ‖z‖ < 1 := lt_of_le_of_lt hzhalf (by norm_num)
    have htaylor : logTaylor 3 z = z-z ^ 2 / 2 := by
      norm_num [logTaylor_succ, logTaylor_zero]
      ring
    have hid : -(t : ℂ) * (a : ℂ) * I - log (1-2 * (t : ℂ) * (a : ℂ) * I) / 2 +
        (t : ℂ) ^ 2 * (a : ℂ) ^ 2 =
        -(log (1+z) - logTaylor 3 z) / 2 := by
      rw [htaylor]
      dsimp [z]
      have harg : (1 - 2 * (t : ℂ) * (a : ℂ) * I) = (1 + -2 * (t : ℂ) * (a : ℂ) * I) := by ring
      rw [harg]
      ring_nf
      simp [I_sq]
    rw [hid, norm_div, norm_neg]
    norm_num only [norm_ofNat]
    have hbound := Complex.norm_log_sub_logTaylor_le 2 hzlt
    norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hbound
    have hinv : (1-‖z‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith : 0 < 1-‖z‖) (by norm_num : (0 : ℝ) < 2)]
      linarith
    calc
      ‖log (1+z)-logTaylor 3 z‖ / 2 ≤ (‖z‖ ^ 3 * (1-‖z‖)⁻¹ / 3) / 2 := by gcongr
      _ ≤ ‖z‖ ^ 3 / 3 := by
        have := mul_le_mul_of_nonneg_left hinv (pow_nonneg (norm_nonneg z) 3)
        linarith
      _ = (8 / 3 : ℝ) * |t| ^ 3 * |a| * a ^ 2 := by rw [hz]; rw [← sq_abs a]; ring
      _ ≤ _ := by gcongr
  let M (n : ℕ) := ⨆ j, |a n j|
  let S (n : ℕ) := ∑' j, (a n j) ^ 2
  let k (t : ℝ) (n j : ℕ) : ℂ :=
    -(t : ℂ) * (a n j : ℂ) * I - log (1-2 * (t : ℂ) * (a n j : ℂ) * I) / 2
  have hmax (n j : ℕ) : |a n j| ≤ M n := by
    have hb : BddAbove (Set.range (fun j => |a n j|)) := by
      refine ⟨Real.sqrt (S n), ?_⟩
      rintro _ ⟨j, rfl⟩
      have hsq : (a n j) ^ 2 ≤ S n := (ha n).le_tsum j (fun k _ => sq_nonneg (a n k))
      simpa only [Real.sqrt_sq_eq_abs] using Real.sqrt_le_sqrt hsq
    exact le_ciSup hb j
  have hquad (t : ℝ) (n : ℕ) : Summable (fun j => (t : ℂ) ^ 2 * (a n j : ℂ) ^ 2) := by
    have hc' := Complex.summable_ofReal.mpr (ha n)
    simpa only [Complex.ofReal_pow] using hc'.mul_left ((t : ℂ) ^ 2)
  have hquad_sum (t : ℝ) (n : ℕ) :
      (∑' j, (t : ℂ) ^ 2 * (a n j : ℂ) ^ 2) = (t : ℂ) ^ 2 * (S n : ℂ) := by
    rw [tsum_mul_left, Complex.ofReal_tsum]
    simp only [Complex.ofReal_pow]
  have hk (t : ℝ) (n : ℕ) : Summable (k t n) := by
    have haz : Tendsto (fun j => |a n j|) atTop (𝓝 0) := by
      have hh := Real.continuous_sqrt.continuousAt.tendsto.comp (ha n).tendsto_atTop_zero
      change Tendsto (fun j => Real.sqrt ((a n j) ^ 2)) atTop (𝓝 (Real.sqrt 0)) at hh
      simpa only [Real.sqrt_sq_eq_abs, Real.sqrt_zero] using hh
    have haz' : Tendsto (fun j => 2 * |t| * |a n j|) atTop (𝓝 0) := by
      simpa using haz.const_mul (2 * |t|)
    have hsmall := haz'.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)
    have hone := haz.eventually_lt_const (by norm_num : (0 : ℝ) < 1)
    have hr : Summable (fun j => k t n j+(t : ℂ) ^ 2 * (a n j : ℂ) ^ 2) := by
      apply ((ha n).mul_left ((8 / 3 : ℝ) * |t| ^ 3)).of_norm_bounded_eventually_nat
      filter_upwards [hsmall, hone] with j hj hj1
      calc
        _ ≤ (8 / 3 : ℝ) * |t| ^ 3 * |a n j| * (a n j) ^ 2 :=
          hlocal t (a n j) |a n j| le_rfl hj.le
        _ ≤ ((8 / 3 : ℝ) * |t| ^ 3) * (a n j) ^ 2 := by
          calc
            _ ≤ (8 / 3 : ℝ) * |t| ^ 3 * 1 * (a n j) ^ 2 := by gcongr
            _ = _ := by ring
    simpa using hr.sub (hquad t n)
  have hcf (t : ℝ) (n : ℕ) : charFun (P.map (Q n)) t = exp (∑' j, k t n j) := by
    let F (j : ℕ) (ω : Ω) := a n j * ((G n j ω) ^ 2-1)
    have hm (j : ℕ) : MemLp (F j) 2 P := hmem n j
    have hindF : iIndepFun F P := (hind n).comp (fun j x => a n j * (x ^ 2-1))
      (fun _ => by fun_prop)
    have hs (j : ℕ) : charFun (P.map (F j)) t = exp (k t n j) := by
      rw [charFun_map_mul_comp ((hG n j).aemeasurable.pow_const 2 |>.sub_const 1),
        hsingle (G n j) (hG n j)]
      congr 1
      dsimp [k]
      push_cast
      ring_nf
    let Z (m : ℕ) : Lp ℝ 2 P := ∑ j ∈ Finset.range m, (hm j).toLp (F j)
    have hZ : Tendsto Z atTop (𝓝 (Q n)) := (hQ n).tendsto_sum_nat
    have hd : TendstoInDistribution (fun m => ⇑(Z m)) atTop ⇑(Q n) (fun _ => P) P :=
      (tendstoInMeasure_of_tendsto_Lp hZ).tendstoInDistribution
        (fun m => (Lp.aestronglyMeasurable (Z m)).aemeasurable)
    have hlim := (ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hd.tendsto) t
    have hrepr (m : ℕ) : ⇑(Z m) =ᵐ[P] (fun ω => ∑ j ∈ Finset.range m, F j ω) := by
      refine (Lp.coeFn_fun_finsetSum _ _).trans ?_
      filter_upwards [ae_all_iff.mpr (fun j => (hm j).coeFn_toLp)] with ω hω
      exact Finset.sum_congr rfl (fun j _ => hω j)
    have hprod (m : ℕ) : charFun (P.map (Z m)) t = exp (∑ j ∈ Finset.range m, k t n j) := by
      rw [Measure.map_congr (hrepr m),
        (hindF.restrict (Finset.range m)).charFun_map_fun_finsetSum_eq_prod
          (fun j _ => (hm j).aemeasurable)]
      simp only [Finset.prod_apply, hs, Complex.exp_sum]
    have hexp : Tendsto (fun m => exp (∑ j ∈ Finset.range m, k t n j)) atTop
        (𝓝 (exp (∑' j, k t n j))) :=
      Complex.continuous_exp.continuousAt.tendsto.comp (hk t n).hasSum.tendsto_sum_nat
    exact tendsto_nhds_unique hlim (hexp.congr (fun m => (hprod m).symm))
  have hlimit (t : ℝ) : Tendsto (fun n => ∑' j, k t n j) atTop
      (𝓝 (-((v : ℂ) * (t : ℂ) ^ 2 / 2))) := by
    have hsmall : ∀ᶠ n in atTop, 2 * |t| * M n ≤ 1 / 2 := by
      have hlim : Tendsto (fun n => 2 * |t| * M n) atTop (𝓝 0) := by
        simpa using hM.const_mul (2 * |t|)
      exact (hlim.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)).mono (fun _ h => h.le)
    have hrem (n : ℕ) (hn : 2 * |t| * M n ≤ 1 / 2) :
        Summable (fun j => k t n j + (t : ℂ) ^ 2 * (a n j : ℂ) ^ 2) ∧
        ‖(∑' j, k t n j) + (t : ℂ) ^ 2 * (S n : ℂ)‖ ≤ (8 / 3 : ℝ) * |t| ^ 3 * M n * S n := by
      have hb (j : ℕ) : ‖k t n j + (t : ℂ) ^ 2 * (a n j : ℂ) ^ 2‖ ≤
          ((8 / 3 : ℝ) * |t| ^ 3 * M n) * (a n j) ^ 2 := hlocal t (a n j) (M n) (hmax n j) hn
      have hs := (ha n).mul_left ((8 / 3 : ℝ) * |t| ^ 3 * M n)
      have hsrem := hs.of_norm_bounded hb
      have hsk : Summable (k t n) := by
        simpa using hsrem.sub (hquad t n)
      refine ⟨hsrem, ?_⟩
      have hnorm := tsum_of_norm_bounded hs.hasSum hb
      rw [hsk.tsum_add (hquad t n), hquad_sum t, tsum_mul_left] at hnorm
      exact hnorm
    have hR : Tendsto (fun n => (8 / 3 : ℝ) * |t| ^ 3 * M n * S n) atTop (𝓝 0) := by
      simpa using (hM.const_mul ((8 / 3 : ℝ) * |t| ^ 3)).mul hS
    have herror : Tendsto (fun n => (∑' j, k t n j)+(t : ℂ) ^ 2 * (S n : ℂ)) atTop (𝓝 0) := by
      apply squeeze_zero_norm' _ hR
      filter_upwards [hsmall] with n hn
      exact (hrem n hn).2
    have hq : Tendsto (fun n => (t : ℂ) ^ 2 * (S n : ℂ)) atTop
        (𝓝 ((t : ℂ) ^ 2 * ((v : ℂ) / 2))) := by
      have hc := (Complex.continuous_ofReal.tendsto ((v : ℝ) / 2)).comp hS
      convert hc.const_mul ((t : ℂ) ^ 2) using 1 <;> push_cast <;> rfl
    have hh := herror.sub hq
    convert hh using 1
    · funext n
      dsimp [k]
      ring
    · congr 1
      ring
  refine ⟨hmem, Q, hQ, ?_⟩
  refine ⟨(fun n => (Lp.aestronglyMeasurable (Q n)).aemeasurable), aemeasurable_id, ?_⟩
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro t
  have hh := Complex.continuous_exp.continuousAt.tendsto.comp (hlimit t)
  change Tendsto (fun n => charFun (P.map (Q n)) t) atTop
    (𝓝 (charFun ((gaussianReal 0 v).map id) t))
  simpa [Function.comp_def, hcf, charFun_gaussianReal] using hh

end D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit
