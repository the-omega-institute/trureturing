/- GID: D5/S3/Zeros/Jensen/OriginalPrimalTailResponse
   generality: I
   mirror-B: D5/B/S3/Zeros/Jensen/OriginalPrimalTailResponse
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cancelled differential residual for the complete original primal theta tail. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Zeros.Jensen.OriginalPrimalTailProjection
import D5.S3.Zeros.Jensen.SourceJensenIntegralExtension
import D5.S3.Analytic.Fourier.XiThetaTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Zeros.Jensen.OriginalPrimalTailResponse
open Real Set MeasureTheory Filter Polynomial
open scoped Topology
open OriginalPrimalTailProjection
open private primalJet_zero primalJet_deriv shiftedBudget shifted_summable scale_summable full_shifted_comparison flux_summable tailJet_summable_ray tailJet_deriv
  tailJet_endpoint tailJet_integral tailJet_continuous tailJet_eq_iterated adjoint_formula
  adjoint_deriv adjoint_second_deriv adjoint_square flux_eq from D5.S3.Zeros.Jensen.OriginalPrimalTailProjection
open private source_map from D5.S3.Zeros.Jensen.SourceJensenIntegralExtension
private theorem jet_one (z : ℝ) : (jetPolynomial 1).eval z = -8*z^3+30*z^2-15*z := by
  norm_num [jetPolynomial, derivative_sub, derivative_mul, derivative_pow]
  <;> ring
private theorem jet_two (z : ℝ) : (jetPolynomial 2).eval z = 16*z^4-112*z^3+165*z^2-(75/2)*z := by
  norm_num [jetPolynomial, derivative_sub, derivative_mul, derivative_pow]
  <;> ring
private theorem cancelled_polynomial {A z : ℝ} (hA : 12 ≤ A) (hAz : A ≤ z) : |4*A^2*(4*z^2-6*z)-(16*z^4-112*z^3+165*z^2-(75/2)*z)| ≤
      16*z^2*(z^2-A^2)+151*z^3 := by
  have hz : 12 ≤ z := hA.trans hAz
  have hz0 : 0 ≤ z := by linarith
  have hA0 : 0 ≤ A := by linarith
  have hsq : A^2 ≤ z^2 := pow_le_pow_left₀ hA0 hAz 2
  have hlead := mul_nonneg (sq_nonneg z) (sub_nonneg.mpr hsq)
  have h24 := mul_le_mul_of_nonneg_right hsq hz0
  have h165 := mul_nonneg (sq_nonneg z) (show 0 ≤ 14*z-165 by linarith)
  have h75 := mul_nonneg hz0 (show 0 ≤ z^2-75/2 by nlinarith)
  have hz3 : 0 ≤ z^3 := pow_nonneg hz0 3
  have hz2 : 0 ≤ z^2 := sq_nonneg z
  have hAz0 := mul_nonneg (sq_nonneg A) hz0
  apply abs_le.mpr
  constructor <;> nlinarith
private theorem weighted_exponent {a s L x : ℝ}
    (hs : 12 ≤ s) (has : a ≤ s) (hL : L ≤ 12) (hx : 0 ≤ x) : a*x^2/2+L*x-s*(exp (2*x)-1) ≤ -s*x := by
  have he := quadratic_le_exp_of_nonneg (show 0 ≤ 2*x by linarith)
  have hs0 : 0 ≤ s := by linarith
  have he' := mul_le_mul_of_nonneg_left he hs0
  have hq := mul_nonneg (sq_nonneg x) (show 0 ≤ 2*s-a/2 by linarith)
  have hl := mul_nonneg hx (show 0 ≤ s-L by linarith)
  nlinarith
private theorem exp_increment {x : ℝ} (_hx : 0 ≤ x) : exp (4*x)-1 ≤ 4*x*exp (4*x) := by
  have h := mul_le_mul_of_nonneg_right (add_one_le_exp (-4*x)) (exp_pos (4*x)).le
  have he : exp (-4*x)*exp (4*x) = 1 := by rw [← exp_add]; ring_nf; exact exp_zero
  rw [he] at h
  nlinarith
private theorem leading_split {A s x : ℝ} (hx : 0 ≤ x) (hs : 0 ≤ s) : (s*exp (2*x))^2*((s*exp (2*x))^2-A^2) ≤
      4*x*s^4*exp (8*x)+(s^2-A^2)*s^2*exp (4*x) := by
  have h := mul_le_mul_of_nonneg_left (exp_increment hx) (show 0 ≤ s^4*exp (4*x) by positivity)
  have he4 : exp (4*x) = exp (2*x)^2 := by rw [← exp_nat_mul]; congr 1; ring
  have he8 : exp (8*x) = exp (4*x)^2 := by rw [← exp_nat_mul]; congr 1; ring
  rw [he8, he4]
  rw [he4] at h
  linear_combination h
private theorem weighted_mode_exp {a s L x : ℝ}
    (hs : 12 ≤ s) (has : a ≤ s) (hL : L+1/2 ≤ 12) (hx : 0 ≤ x) : exp (a*x^2/2)*exp (x/2)*exp (-s*exp (2*x))*exp (L*x) ≤
      exp (-s)*exp (-s*x) := by
  simp only [← exp_add]
  apply exp_le_exp.mpr
  have h := weighted_exponent hs has hL hx
  nlinarith
private theorem primal_polynomial_bounds {z : ℝ} (hz : 12 ≤ z) : |4*z^2-6*z| ≤ 4*z^2 ∧ |-8*z^3+30*z^2-15*z| ≤ 11*z^3 := by
  have hz0 : 0 ≤ z := by linarith
  have h0 : 0 ≤ 4*z^2-6*z := by nlinarith
  constructor
  · rw [abs_of_nonneg h0]; nlinarith
  · have h30 := mul_nonneg (sq_nonneg z) (show 0 ≤ (5/2)*z-30 by linarith)
    have h15 := mul_nonneg hz0 (show 0 ≤ z^2/2-15 by nlinarith)
    apply abs_le.mpr
    constructor <;> nlinarith [pow_nonneg hz0 3]
private theorem mode_residual_majorant {A a α : ℝ} {m : ℕ}
    (hA : 12 ≤ A) (hAs : A ≤ modeScale m) (has : a ≤ modeScale m)
    (hα : 0 ≤ α) {x : ℝ} (hx : 0 ≤ x) : exp (a*x^2/2)*|4*A^2*primalMode m x-primalJet 2 m x-
      α*(primalMode m x+x*primalJet 1 m x)| ≤ exp (-modeScale m)*
      ((64*(modeScale m)^4+11*α*(modeScale m)^3)*x+ 151*(modeScale m)^3+16*((modeScale m)^2-A^2)*(modeScale m)^2+
        4*α*(modeScale m)^2)*exp (-modeScale m*x) := by
  let s := modeScale m
  let z := s*exp (2*x)
  let e := exp (x/2)*exp (-s*exp (2*x))
  let w := exp (a*x^2/2)
  have hs : 12 ≤ s := hA.trans hAs
  have hs0 : 0 ≤ s := by linarith
  have he : 0 < e := by dsimp [e]; positivity
  have hw : 0 < w := exp_pos _
  have hxexp : 1 ≤ exp (2*x) := one_le_exp_iff.mpr (by linarith)
  have hsz : s ≤ z := by dsimp [z]; nlinarith
  have hz : 12 ≤ z := hs.trans hsz
  have hp := primal_polynomial_bounds hz
  have hD := cancelled_polynomial hA (hAs.trans hsz)
  have hsplit := leading_split (A := A) hx hs0
  have hq0 : primalMode m x = e*(4*z^2-6*z) := by
    rw [← primalJet_zero]
    simp only [primalJet, jetPolynomial, eval_sub, eval_mul, eval_C, eval_pow, eval_X]
    rfl
  have hq1 : primalJet 1 m x = e*(-8*z^3+30*z^2-15*z) := by
    rw [primalJet, jet_one]
  have hq2 : primalJet 2 m x = e*(16*z^4-112*z^3+165*z^2-(75/2)*z) := by
    rw [primalJet, jet_two]
  have hres : |4*A^2*primalMode m x-primalJet 2 m x- α*(primalMode m x+x*primalJet 1 m x)| ≤
      e*(64*x*s^4*exp (8*x)+16*(s^2-A^2)*s^2*exp (4*x)+151*z^3+ α*(4*z^2+11*x*z^3)) := by
    rw [hq0, hq1, hq2]
    have hid : 4*A^2*(e*(4*z^2-6*z))-e*(16*z^4-112*z^3+165*z^2-(75/2)*z)- α*(e*(4*z^2-6*z)+x*(e*(-8*z^3+30*z^2-15*z))) =
        e*((4*A^2*(4*z^2-6*z)-(16*z^4-112*z^3+165*z^2-(75/2)*z))- α*((4*z^2-6*z)+x*(-8*z^3+30*z^2-15*z))) := by ring
    rw [hid, abs_mul, abs_of_pos he]
    apply mul_le_mul_of_nonneg_left _ he.le
    have hb : |(4*z^2-6*z)+x*(-8*z^3+30*z^2-15*z)| ≤ 4*z^2+11*x*z^3 := by
      calc
        _ ≤ |4*z^2-6*z|+|x*(-8*z^3+30*z^2-15*z)| := abs_add_le _ _
        _ = |4*z^2-6*z|+x*|-8*z^3+30*z^2-15*z| := by rw [abs_mul, abs_of_nonneg hx]
        _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hp.2 hx]
    calc
      _ ≤ |4*A^2*(4*z^2-6*z)-(16*z^4-112*z^3+165*z^2-(75/2)*z)|+
          |α*((4*z^2-6*z)+x*(-8*z^3+30*z^2-15*z))| := by
            simpa only [sub_zero, zero_sub, abs_neg] using
              (abs_sub_le (4*A^2*(4*z^2-6*z)-(16*z^4-112*z^3+165*z^2-(75/2)*z))
                (0 : ℝ) (α*((4*z^2-6*z)+x*(-8*z^3+30*z^2-15*z))))
      _ ≤ 16*z^2*(z^2-A^2)+151*z^3+α*(4*z^2+11*x*z^3) := by
        rw [abs_mul, abs_of_nonneg hα]
        exact add_le_add hD (mul_le_mul_of_nonneg_left hb hα)
      _ ≤ _ := by dsimp [z] at *; nlinarith
  have he8 := weighted_mode_exp (a := a) (L := 8) hs has (by norm_num) hx
  have he6 := weighted_mode_exp (a := a) (L := 6) hs has (by norm_num) hx
  have he4 := weighted_mode_exp (a := a) (L := 4) hs has (by norm_num) hx
  have he6' : w*e*z^3 ≤ s^3*(exp (-s)*exp (-s*x)) := by
    have hid : w*e*z^3 = s^3*(w*e*exp (6*x)) := by
      dsimp [z]
      rw [mul_pow, show exp (2*x)^3 = exp (6*x) by rw [← exp_nat_mul]; congr 1; ring]
      ring
    rw [hid]
    simpa only [w,e,mul_assoc] using mul_le_mul_of_nonneg_left he6 (pow_nonneg hs0 3)
  have he4' : w*e*z^2 ≤ s^2*(exp (-s)*exp (-s*x)) := by
    have hid : w*e*z^2 = s^2*(w*e*exp (4*x)) := by
      dsimp [z]
      rw [mul_pow, show exp (2*x)^2 = exp (4*x) by rw [← exp_nat_mul]; congr 1; ring]
      ring
    rw [hid]
    simpa only [w,e,mul_assoc] using mul_le_mul_of_nonneg_left he4 (sq_nonneg s)
  have hmis : 0 ≤ s^2-A^2 := by
    have := pow_le_pow_left₀ (show 0 ≤ A by linarith) hAs 2
    linarith
  have h8 := mul_le_mul_of_nonneg_left he8 (show 0 ≤ 64*x*s^4 by positivity)
  have h4 := mul_le_mul_of_nonneg_left he4 (show 0 ≤ 16*(s^2-A^2)*s^2 by positivity)
  have h6 := mul_le_mul_of_nonneg_left he6' (show (0:ℝ) ≤ 151 by norm_num)
  have hα4 := mul_le_mul_of_nonneg_left he4' (show 0 ≤ 4*α by positivity)
  have hα6 := mul_le_mul_of_nonneg_left he6' (show 0 ≤ 11*α*x by positivity)
  have hresw := mul_le_mul_of_nonneg_left hres hw.le
  change w*|_| ≤ _
  dsimp only [w,e,s] at hresw h8 h4 h6 hα4 hα6 ⊢
  linear_combination hresw+h8+h4+h6+hα4+hα6
private theorem linear_exp_integrable {s : ℝ} (hs : 0 < s) : IntegrableOn (fun x : ℝ => x*exp (-s*x)) (Ioi 0) := by
  simpa using (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (b := s) (by norm_num) (by norm_num) hs)
private theorem linear_exp_integral {s : ℝ} (hs : 0 < s) : (∫ x in Ioi (0 : ℝ), x*exp (-s*x)) = 1/s^2 := by
  have h := integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := s) (by norm_num) hs
  norm_num [show Gamma (2:ℝ) = 1 by simpa using Gamma_nat_eq_factorial 1] at h
  simpa [one_div_pow] using h
private theorem mode_residual_integral {A a α : ℝ} {m : ℕ}
    (hA : 12 ≤ A) (hAs : A ≤ modeScale m) (has : a ≤ modeScale m)
    (hα : 0 ≤ α) (hαs : α ≤ modeScale m) : IntegrableOn (fun x : ℝ => exp (a*x^2/2)*
      |4*A^2*primalMode m x-primalJet 2 m x- α*(primalMode m x+x*primalJet 1 m x)|) (Ioi 0) ∧
    (∫ x in Ioi (0 : ℝ), exp (a*x^2/2)* |4*A^2*primalMode m x-primalJet 2 m x-
        α*(primalMode m x+x*primalJet 1 m x)|) ≤ 230*(modeScale m)^2*exp (-modeScale m)+
        16*((modeScale m)^2-A^2)*modeScale m*exp (-modeScale m) := by
  let s := modeScale m
  let c := 64*s^4+11*α*s^3
  let d := 151*s^3+16*(s^2-A^2)*s^2+4*α*s^2
  let f := fun x : ℝ => exp (a*x^2/2)* |4*A^2*primalMode m x-primalJet 2 m x-α*(primalMode m x+x*primalJet 1 m x)|
  let g := fun x : ℝ => exp (-s)*(c*x+d)*exp (-s*x)
  have hs : 0 < s := lt_of_lt_of_le (by norm_num : (0:ℝ) < 12) (hA.trans hAs)
  have hi0 := integrableOn_exp_mul_Ioi (show -s < 0 by linarith) 0
  have hi1 := linear_exp_integrable hs
  have hgi : IntegrableOn g (Ioi 0) := by
    change Integrable g (volume.restrict (Ioi (0 : ℝ)))
    have hg : g = fun x => exp (-s)*(c*(x*exp (-s*x))+d*exp (-s*x)) := by
      ext x; dsimp [g]; ring
    rw [hg]
    exact ((hi1.const_mul c).add (hi0.const_mul d)).const_mul (exp (-s))
  have hcont : Continuous f := by
    have h0 := (show ∀ x, HasDerivAt (primalJet 0 m) (primalJet 1 m x) x from fun x => primalJet_deriv 0 m x)
    have h1 : Continuous (primalJet 1 m) := continuous_iff_continuousAt.mpr
      (fun x => (primalJet_deriv 1 m x).continuousAt)
    have h2 : Continuous (primalJet 2 m) := continuous_iff_continuousAt.mpr
      (fun x => (primalJet_deriv 2 m x).continuousAt)
    have hq : Continuous (primalMode m) := by
      exact (continuous_iff_continuousAt.mpr (fun x => (h0 x).continuousAt)).congr
        (fun x => primalJet_zero m x)
    exact (by fun_prop : Continuous (fun x : ℝ => exp (a*x^2/2))).mul
      ((((hq.const_mul (4*A^2)).sub h2).sub ((hq.add (continuous_id.mul h1)).const_mul α)).abs)
  have hbound : ∀ x ∈ Ioi (0:ℝ), f x ≤ g x := by
    intro x hx
    convert! mode_residual_majorant hA hAs has hα hx.le using 1 <;> dsimp [f,g,c,d,s] <;> ring
  have hfi : IntegrableOn f (Ioi 0) := by
    apply hgi.mono' hcont.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [f]; positivity)]
    exact hbound x hx
  refine ⟨hfi, ?_⟩
  have hgint : (∫ x in Ioi (0:ℝ), g x) = exp (-s)*(c/s^2+d/s) := by
    have hg : g = fun x => exp (-s)*(c*(x*exp (-s*x))+d*exp (-s*x)) := by
      ext x; dsimp [g]; ring
    rw [hg, integral_const_mul, integral_add (hi1.const_mul c) (hi0.const_mul d), integral_const_mul, integral_const_mul, linear_exp_integral hs,
      integral_exp_mul_Ioi (by linarith)]
    simp [div_eq_mul_inv]
  have hcalc : exp (-s)*(c/s^2+d/s) ≤ 230*s^2*exp (-s)+16*(s^2-A^2)*s*exp (-s) := by
    have hid : c/s^2+d/s = 215*s^2+15*α*s+16*(s^2-A^2)*s := by
      dsimp [c,d]; field_simp [hs.ne']; ring
    rw [hid]
    have hh := mul_le_mul_of_nonneg_right hαs hs.le
    nlinarith [mul_le_mul_of_nonneg_left hh (exp_pos (-s)).le]
  exact (integral_mono_ae hfi hgi (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact hbound x hx)).trans (hgint.trans_le hcalc)
private theorem later_mode_comparison {N : ℕ} (hN : 1 ≤ N) (k j : ℕ) (hj : 1 ≤ j) : (modeScale (N+j+1))^k*exp (-modeScale (N+j+1)) ≤
      (modeScale (N+1))^k*exp (-modeScale (N+1))* exp (-2*Real.pi*((N+1:ℕ):ℝ))*
          (((j+1:ℕ):ℝ)^(2*k)*exp (-Real.pi*(j:ℝ))) := by
  let M : ℝ := ((N+1:ℕ):ℝ)
  let z : ℝ := j
  have hM : 2 ≤ M := by dsimp [M]; exact_mod_cast (show 2 ≤ N+1 by omega)
  have hz : 1 ≤ z := by dsimp [z]; exact_mod_cast hj
  have hm : ((N+j+1:ℕ):ℝ) = M+z := by dsimp [M,z]; push_cast; ring
  have hscale : modeScale (N+j+1) ≤ modeScale (N+1)*(z+1)^2 := by
    have hh := pow_le_pow_left₀ (show 0 ≤ M+z by linarith) (show M+z ≤ M*(z+1) by nlinarith) 2
    dsimp [modeScale]; rw [hm]
    change Real.pi*(M+z)^2 ≤ Real.pi*M^2*(z+1)^2
    nlinarith [mul_le_mul_of_nonneg_left hh pi_pos.le]
  have hex : exp (-modeScale (N+j+1)) ≤ exp (-modeScale (N+1))*exp (-2*Real.pi*M)*exp (-Real.pi*z) := by
    simp only [← exp_add]
    apply exp_le_exp.mpr
    have hh : 0 ≤ 2*M*(z-1)+z*(z-1) := by positivity
    have h := mul_nonneg pi_pos.le hh
    dsimp [modeScale]; rw [hm]
    change -(Real.pi*(M+z)^2) ≤ -(Real.pi*M^2)+-2*Real.pi*M+-Real.pi*z
    nlinarith
  calc
    _ ≤ (modeScale (N+1)*(z+1)^2)^k*
        (exp (-modeScale (N+1))*exp (-2*Real.pi*M)*exp (-Real.pi*z)) := mul_le_mul (pow_le_pow_left₀ (by dsimp [modeScale]; positivity) hscale k)
        hex (exp_pos _).le (by dsimp [modeScale]; positivity)
    _ = _ := by simp only [mul_pow, ← pow_mul]; dsimp [M,z]; push_cast; ring
private theorem later_mode_sum {N : ℕ} (hN : 1 ≤ N) (k : ℕ) : (∑' j : ℕ, (modeScale (N+(j+1)+1))^k*exp (-modeScale (N+(j+1)+1))) ≤
      (modeScale (N+1))^k*exp (-modeScale (N+1))* exp (-2*Real.pi*((N+1:ℕ):ℝ))*(shiftedBudget k-1) := by
  have hs := (scale_summable N k).comp_injective Nat.succ_injective
  have ht := (shifted_summable k).comp_injective Nat.succ_injective
  have hsplit : (∑' j : ℕ, (((j+1+1:ℕ):ℝ)^(2*k)*exp (-Real.pi*((j+1:ℕ):ℝ)))) = shiftedBudget k-1 := by
    have h := (shifted_summable k).sum_add_tsum_nat_add 1
    simpa [shiftedBudget] using (eq_sub_iff_add_eq.mpr (by simpa [add_comm] using h))
  have h := hs.tsum_le_tsum (fun j => later_mode_comparison hN k (j+1) (by omega))
    (ht.mul_left ((modeScale (N+1))^k*exp (-modeScale (N+1))* exp (-2*Real.pi*((N+1:ℕ):ℝ))))
  simpa only [Function.comp_def, Nat.succ_eq_add_one, tsum_mul_left, hsplit] using h
private theorem scale_gap {N : ℕ} (hN : 1 ≤ N) : exp (-2*Real.pi*((N+1:ℕ):ℝ)) ≤ 1/(2*Real.pi*modeScale (N+1)) := by
  let M : ℝ := ((N+1:ℕ):ℝ)
  have hM : 0 < M := by dsimp [M]; positivity
  have he := quadratic_le_exp_of_nonneg (show 0 ≤ 2*Real.pi*M by positivity)
  have hden : 0 < 2*Real.pi*modeScale (N+1) := by dsimp [modeScale]; positivity
  calc
    _ = 1/exp (2*Real.pi*M) := by
      rw [one_div, ← exp_neg]
      congr 1
      dsimp [M]
      ring
    _ ≤ _ := by
      apply one_div_le_one_div_of_le hden
      dsimp [modeScale]
      change 2*Real.pi*(Real.pi*M^2) ≤ exp (2*Real.pi*M)
      nlinarith [mul_pos pi_pos hM]
private theorem full_flux_lower {N : ℕ} (hN : 1 ≤ N)
    (hA : 12 ≤ modeScale (N+1)) : (11/2)*(modeScale (N+1))^3*exp (-modeScale (N+1)) ≤ originalFlux N := by
  have hterm (j : ℕ) : (11/2)*(modeScale (N+j+1))^3*exp (-modeScale (N+j+1)) ≤ exp (-modeScale (N+j+1))*(8*(modeScale (N+j+1))^3-
        30*(modeScale (N+j+1))^2+15*modeScale (N+j+1)) := by
    have hsc : modeScale (N+1) ≤ modeScale (N+j+1) := by
      apply mul_le_mul_of_nonneg_left _ pi_pos.le
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast (by omega : N+1 ≤ N+j+1)) 2
    have hs : 12 ≤ modeScale (N+j+1) := hA.trans hsc
    have hp := mul_nonneg (sq_nonneg (modeScale (N+j+1)))
      (show 0 ≤ (5/2)*modeScale (N+j+1)-30 by linarith)
    nlinarith [mul_nonneg (show 0 ≤ (5/2)*(modeScale (N+j+1))^3- 30*(modeScale (N+j+1))^2+15*modeScale (N+j+1) by nlinarith)
      (exp_pos (-modeScale (N+j+1))).le]
  apply le_trans (by simpa using hterm 0)
  exact (flux_summable N).le_tsum 0 (fun j _ =>
    le_trans (by have := hA; have h := sq_nonneg ((N+j+1:ℕ):ℝ)
                 dsimp [modeScale]; positivity) (hterm j))
private theorem residual_series {N : ℕ} (hN : 1 ≤ N) (A α : ℝ)
    {x : ℝ} (hx : 0 ≤ x) : HasSum (fun j : ℕ => 4*A^2*primalMode (N+j+1) x-primalJet 2 (N+j+1) x-
      α*(primalMode (N+j+1) x+x*primalJet 1 (N+j+1) x))
      (4*A^2*originalTail N x-densityAdjoint α (originalTail N) x) := by
  have h0 := (tailJet_summable_ray 0 N hN hx).hasSum
  have h1 := (tailJet_summable_ray 1 N hN hx).hasSum
  have h2 := (tailJet_summable_ray 2 N hN hx).hasSum
  have h := ((h0.mul_left (4*A^2)).sub h2).sub ((h0.add (h1.mul_left x)).mul_left α)
  have hz : tailJet 0 N x = originalTail N x := by
    simpa using congrFun (tailJet_eq_iterated 0 N hN) x
  rw [adjoint_formula N hN α x]
  change HasSum _ (4*A^2*tailJet 0 N x-tailJet 2 N x- α*(tailJet 0 N x+x*tailJet 1 N x)) at h
  rw [hz] at h
  rw [hz]
  simpa only [primalJet_zero, sub_add_eq_sub_sub] using h
private def residualConstant : ℝ := 230*shiftedBudget 2+(8/Real.pi)*(shiftedBudget 3-1)
private theorem residual_budget_sum {N : ℕ} (hN : 1 ≤ N) : (∑' j : ℕ, (230*(modeScale (N+j+1))^2*exp (-modeScale (N+j+1))+
      16*((modeScale (N+j+1))^2-(modeScale (N+1))^2)* modeScale (N+j+1)*exp (-modeScale (N+j+1)))) ≤
      residualConstant*(modeScale (N+1))^2*exp (-modeScale (N+1)) := by
  let A := modeScale (N+1)
  let f := fun j : ℕ => ((modeScale (N+j+1))^2-A^2)* modeScale (N+j+1)*exp (-modeScale (N+j+1))
  have hA : 0 < A := by dsimp [A,modeScale]; positivity
  have hf : Summable f := by
    convert! (scale_summable N 3).sub ((scale_summable N 1).mul_left (A^2)) using 1
    ext j; dsimp [f]; ring
  have hf0 : f 0 = 0 := by simp [f,A]
  have hfsplit : (∑' j, f j) = ∑' j, f (j+1) := by
    have h := hf.sum_add_tsum_nat_add 1
    simpa [hf0] using h.symm
  have hsm : Summable (fun j : ℕ => (modeScale (N+(j+1)+1))^3* exp (-modeScale (N+(j+1)+1))) :=
    (scale_summable N 3).comp_injective Nat.succ_injective
  have hmajor : (∑' j, f j) ≤ A^3*exp (-A)*exp (-2*Real.pi*((N+1:ℕ):ℝ))*(shiftedBudget 3-1) := by
    rw [hfsplit]
    apply le_trans ((hf.comp_injective Nat.succ_injective).tsum_le_tsum (fun j => ?_) hsm) (later_mode_sum hN 3)
    dsimp [f]
    have h := mul_nonneg (sq_nonneg A) (show 0 ≤ modeScale (N+(j+1)+1)* exp (-modeScale (N+(j+1)+1)) by dsimp [modeScale]; positivity)
    nlinarith
  have hS : 0 ≤ shiftedBudget 3-1 := by
    have h := (shifted_summable 3).le_tsum 0 (fun j _ => by positivity)
    simpa [shiftedBudget] using sub_nonneg.mpr h
  have hmis : (∑' j, f j) ≤ (1/(2*Real.pi))*(shiftedBudget 3-1)*A^2*exp (-A) := by
    apply hmajor.trans
    have h := mul_le_mul_of_nonneg_left (scale_gap hN)
      (show 0 ≤ A^3*exp (-A)*(shiftedBudget 3-1) by positivity)
    calc
      A^3*exp (-A)*exp (-2*Real.pi*((N+1:ℕ):ℝ))*(shiftedBudget 3-1) = (A^3*exp (-A)*(shiftedBudget 3-1))*exp (-2*Real.pi*((N+1:ℕ):ℝ)) := by ring
      _ ≤ (A^3*exp (-A)*(shiftedBudget 3-1))*(1/(2*Real.pi*A)) := h
      _ = _ := by field_simp [hA.ne', pi_ne_zero] <;> ring
  have hsum := ((scale_summable N 2).mul_left 230).tsum_add (hf.mul_left 16)
  have hsum' : (∑' j : ℕ, (230*(modeScale (N+j+1))^2*exp (-modeScale (N+j+1))+
        16*((modeScale (N+j+1))^2-A^2)*modeScale (N+j+1)*exp (-modeScale (N+j+1)))) = 230*(∑' j : ℕ, (modeScale (N+j+1))^2*exp (-modeScale (N+j+1)))+
        16*(∑' j, f j) := by
    calc
      _ = ∑' j : ℕ, (230*((modeScale (N+j+1))^2*exp (-modeScale (N+j+1)))+16*f j) :=
        tsum_congr (fun j => by dsimp [f]; ring)
      _ = _ := by rw [hsum, tsum_mul_left, tsum_mul_left]
  rw [hsum']
  have hmain := full_shifted_comparison hN 2
  change (∑' j : ℕ, (modeScale (N+j+1))^2*exp (-modeScale (N+j+1))) ≤ A^2*exp (-A)*shiftedBudget 2 at hmain
  calc
    _ ≤ 230*(A^2*exp (-A)*shiftedBudget 2)+
        16*((1/(2*Real.pi))*(shiftedBudget 3-1)*A^2*exp (-A)) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hmain (by norm_num))
        (mul_le_mul_of_nonneg_left hmis (by norm_num))
    _ = _ := by
      dsimp [residualConstant,A]
      field_simp [pi_ne_zero] <;> ring
private theorem full_residual_integral {N : ℕ} (hN : 1 ≤ N) {a α : ℝ}
    (hA : max 12 a ≤ modeScale (N+1)) (hα : 0 ≤ α) (hαa : α ≤ a) : IntegrableOn (fun x : ℝ => exp (a*x^2/2)*
      |4*(modeScale (N+1))^2*originalTail N x-densityAdjoint α (originalTail N) x|) (Ioi 0) ∧ (∫ x in Ioi (0:ℝ), exp (a*x^2/2)*
      |4*(modeScale (N+1))^2*originalTail N x-densityAdjoint α (originalTail N) x|) ≤ residualConstant*(modeScale (N+1))^2*exp (-modeScale (N+1)) := by
  let A := modeScale (N+1)
  let r := fun j : ℕ => fun x : ℝ => 4*A^2*primalMode (N+j+1) x-primalJet 2 (N+j+1) x-
      α*(primalMode (N+j+1) x+x*primalJet 1 (N+j+1) x)
  let F := fun j : ℕ => fun x : ℝ => exp (a*x^2/2)*|r j x|
  let f := fun x : ℝ => exp (a*x^2/2)* |4*A^2*originalTail N x-densityAdjoint α (originalTail N) x|
  let μ := volume.restrict (Ioi (0:ℝ))
  have hscale (j : ℕ) : A ≤ modeScale (N+j+1) := by
    apply mul_le_mul_of_nonneg_left _ pi_pos.le
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast (by omega : N+1 ≤ N+j+1)) 2
  have hm (j : ℕ) := mode_residual_integral (le_max_left 12 a |>.trans hA) (hscale j)
    ((le_max_right 12 a).trans (hA.trans (hscale j))) hα
    (hαa.trans ((le_max_right 12 a).trans (hA.trans (hscale j))))
  have hFi (j : ℕ) : Integrable (F j) μ := (hm j).1
  have hFn (j : ℕ) (x : ℝ) : 0 ≤ F j x := by dsimp [F]; positivity
  have hsum : Summable (fun j : ℕ => ∫ x, F j x ∂μ) := by
    apply (((scale_summable N 2).mul_left 230).add ((scale_summable N 3).mul_left 16)).of_nonneg_of_le
      (fun j => integral_nonneg (hFn j))
    intro j
    apply (hm j).2.trans
    have hh := mul_nonneg (sq_nonneg A)
      (show 0 ≤ modeScale (N+j+1)*exp (-modeScale (N+j+1)) by dsimp [modeScale]; positivity)
    nlinarith
  have hnormsum : Summable (fun j : ℕ => ∫ x, ‖F j x‖ ∂μ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hFn _ _)] using hsum
  have hlin (j : ℕ) : (∫⁻ x, ‖F j x‖ₑ ∂μ) = ENNReal.ofReal (∫ x, ‖F j x‖ ∂μ) := (ofReal_integral_norm_eq_lintegral_enorm (hFi j)).symm
  have hsumint : Integrable (fun x => ∑' j, F j x) μ := by
    refine ⟨AEStronglyMeasurable.tsum (fun j => (hFi j).aestronglyMeasurable), ?_⟩
    apply hasFiniteIntegral_iff_enorm.mpr
    apply lt_of_le_of_lt (lintegral_mono (fun x => enorm_tsum_le_tsum_enorm))
    rw [lintegral_tsum (fun j => (hFi j).aestronglyMeasurable.enorm)]
    simp_rw [hlin]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => integral_nonneg (fun x => norm_nonneg _)) hnormsum]
    exact ENNReal.ofReal_lt_top
  have hsigned {x : ℝ} (hx : 0 ≤ x) := residual_series hN A α hx
  have hfbound : ∀ x ∈ Ioi (0:ℝ), f x ≤ ∑' j, F j x := by
    intro x hx
    have h := (hsigned hx.le).mul_left (exp (a*x^2/2))
    have hn := norm_tsum_le_tsum_norm (f := fun j => exp (a*x^2/2)*r j x) h.summable.norm
    rw [h.tsum_eq] at hn
    simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _)] using hn
  have hfmeas : AEStronglyMeasurable f μ := by
    have hc0 := tailJet_continuous 0 N hN
    have hc1 := tailJet_continuous 1 N hN
    have hc2 := tailJet_continuous 2 N hN
    have h0 : originalTail N = tailJet 0 N := by simpa using (tailJet_eq_iterated 0 N hN).symm
    dsimp [f]
    simp_rw [adjoint_formula N hN α, h0]
    fun_prop
  have hfi : Integrable f μ := by
    apply hsumint.mono' hfmeas
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [f]; positivity)]
    exact hfbound x hx
  refine ⟨hfi, ?_⟩
  calc
    (∫ x, f x ∂μ) ≤ ∫ x, ∑' j, F j x ∂μ := integral_mono_ae hfi hsumint (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact hfbound x hx)
    _ = ∑' j, ∫ x, F j x ∂μ := (integral_tsum_of_summable_integral_norm hFi hnormsum).symm
    _ ≤ ∑' j : ℕ, (230*(modeScale (N+j+1))^2*exp (-modeScale (N+j+1))+ 16*((modeScale (N+j+1))^2-A^2)*modeScale (N+j+1)*exp (-modeScale (N+j+1))) := by
      apply hsum.tsum_le_tsum (fun j => (hm j).2)
      convert! (((scale_summable N 2).mul_left 230).add (((scale_summable N 3).sub ((scale_summable N 1).mul_left (A^2))).mul_left 16)) using 1
      ext j
      ring
    _ ≤ _ := residual_budget_sum hN
private theorem relative_residual : ∃ K:ℝ, 0<K ∧ ∀ a:ℝ, ∀ N:ℕ, 1≤N → max 12 a ≤ modeScale (N+1) →
      ∀ α:ℝ, 0≤α → α≤a → IntegrableOn (fun x:ℝ => exp (a*x^2/2)*
        |4*(modeScale (N+1))^2*originalTail N x-densityAdjoint α (originalTail N) x|) (Ioi 0) ∧ (∫ x in Ioi (0:ℝ), exp (a*x^2/2)*
        |4*(modeScale (N+1))^2*originalTail N x-densityAdjoint α (originalTail N) x|) ≤ (K/modeScale (N+1))*originalFlux N := by
  have hS (k:ℕ) : 1≤shiftedBudget k := by
    have h := (shifted_summable k).le_tsum 0 (fun j _ => by positivity)
    simpa [shiftedBudget] using h
  have hL : 0<residualConstant := by
    dsimp [residualConstant]
    have h2 := hS 2
    have h3 : 0≤shiftedBudget 3-1 := sub_nonneg.mpr (hS 3)
    have h := mul_nonneg (show 0≤8/Real.pi by positivity) h3
    linarith
  refine ⟨(2/11)*residualConstant, by positivity, ?_⟩
  intro a N hN hA α hα hαa
  have hAi : 12≤modeScale (N+1) := (le_max_left 12 a).trans hA
  have hpos : 0<modeScale (N+1) := by linarith
  have hb := full_residual_integral hN hA hα hαa
  refine ⟨hb.1, hb.2.trans ?_⟩
  have h := mul_le_mul_of_nonneg_left (full_flux_lower hN hAi)
    (show 0≤((2/11)*residualConstant)/modeScale (N+1) by positivity)
  calc
    residualConstant*(modeScale (N+1))^2*exp (-modeScale (N+1)) = (((2/11)*residualConstant)/modeScale (N+1))*
        ((11/2)*(modeScale (N+1))^3*exp (-modeScale (N+1))) := by
      field_simp [hpos.ne'] <;> ring
    _ ≤ _ := h
open NormalizedJensenDegreeLowering SourceJensenIntegralExtension SourceThetaMomentBounds
open D5.S3.Zeros.CompletedZeta
/-- The literal finite original polynomial, with its original factorial convention. -/
def originalB (n : ℕ) (t x : ℝ) : ℝ := ∑ j ∈ Finset.range (n+1), (-1:ℝ)^j*(n.descFactorial j:ℝ)*t^j*x^(2*j)/
    ((n:ℝ)^j*((2*j).factorial:ℝ))
/-- Every retained positive mode. -/
def originalHead (N : ℕ) (x : ℝ) : ℝ := ∑ m ∈ Finset.Icc 1 N, primalMode m x
/-- The unchanged canonical xi denominator. -/
def fullZ : ℝ := (xiReading (1/2:ℂ)).re
/-- Expectation against the actual full normalized theta density. -/
def originalJ (n : ℕ) (t : ℝ) : ℝ := ∫ x:ℝ, originalB n t x*sourceThetaDensity x
private def originalCoefficient (n : ℕ) (t : ℝ) (j : ℕ) : ℝ := (-1:ℝ)^j*(n.descFactorial j:ℝ)*t^j/((n:ℝ)^j*((2*j).factorial:ℝ))
private theorem original_coefficient_recurrence {n : ℕ} (hn : 1 ≤ n) (t : ℝ) (j : ℕ) : ((2*j:ℕ):ℝ)+2 ≠ 0 ∧
    (((2*j:ℕ):ℝ)+2)*(((2*j:ℕ):ℝ)+1)*originalCoefficient n t (j+1)+ (t-2*(t/(2*(n:ℝ)))*(j:ℝ))*originalCoefficient n t j = 0 := by
  refine ⟨by positivity, ?_⟩
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  by_cases hj : j ≤ n
  · have hf : (((2*(j+1)).factorial:ℕ):ℝ) = (((2*j:ℕ):ℝ)+2)*(((2*j:ℕ):ℝ)+1)*((2*j).factorial:ℝ) := by
      rw [show 2*(j+1) = (2*j+1)+1 by omega, Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      ring
    have hfac0 : ((2*j).factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2*j)
    simp only [originalCoefficient, Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub hj, pow_succ]
    rw [hf]
    field_simp [hn0,hfac0]
    push_cast
    ring
  · have hj' : n < j := by omega
    simp only [originalCoefficient, Nat.descFactorial_of_lt hj', Nat.descFactorial_of_lt (show n < j+1 by omega), Nat.cast_zero, mul_zero,
      zero_mul, zero_div, zero_add]
private def originalPolynomial (n : ℕ) (t : ℝ) : ℝ[X] := ∑ j ∈ Finset.range (n+1), C (originalCoefficient n t j)*X^(2*j)
private theorem original_polynomial_coeff_even (n j : ℕ) (t : ℝ) : (originalPolynomial n t).coeff (2*j) = originalCoefficient n t j := by
  simp only [originalPolynomial, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    have hk : 2*k ≠ 2*j := by omega
    simp [Ne.symm hkj]
  · intro hj
    have hjn : n < j := by simpa using hj
    simp [originalCoefficient, Nat.descFactorial_of_lt hjn]
private theorem original_polynomial_coeff_odd (n j : ℕ) (t : ℝ) : (originalPolynomial n t).coeff (2*j+1) = 0 := by
  simp only [originalPolynomial, finsetSum_coeff, coeff_C_mul_X_pow]
  apply Finset.sum_eq_zero
  intro k _
  have hk : 2*k ≠ 2*j+1 := by omega
  simp [Ne.symm hk]
private theorem original_polynomial_ode {n : ℕ} (hn : 1 ≤ n) (t : ℝ) : (originalPolynomial n t).derivative.derivative-
      C (t/(2*(n:ℝ)))*(X*(originalPolynomial n t).derivative)+ C t*originalPolynomial n t = 0 := by
  let p := originalPolynomial n t
  have hxd (k : ℕ) : (X*p.derivative).coeff k = p.coeff k*(k:ℝ) := by
    cases k <;> simp [coeff_X_mul, coeff_derivative]
  ext k
  simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_derivative, coeff_zero]
  change p.coeff (k+1+1)*(((k+1:ℕ):ℝ)+1)*((k:ℝ)+1)- t/(2*(n:ℝ))*(X*p.derivative).coeff k+t*p.coeff k = 0
  rw [hxd]
  have hk : k%2=0 ∨ k%2=1 := by omega
  rcases hk with hk|hk
  · have he : k=2*(k/2) := by omega
    rw [he]
    have he' : 2*(k/2)+1+1=2*(k/2+1) := by omega
    rw [he']
    dsimp [p]
    rw [original_polynomial_coeff_even, original_polynomial_coeff_even]
    have h := (original_coefficient_recurrence hn t (k/2)).2
    push_cast at *
    linear_combination h
  · have he : k=2*(k/2)+1 := by omega
    rw [he]
    have he' : 2*(k/2)+1+1+1=2*(k/2+1)+1 := by omega
    rw [he']
    dsimp [p]
    rw [original_polynomial_coeff_odd, original_polynomial_coeff_odd]
    ring
private theorem original_polynomial_eval (n : ℕ) (t x : ℝ) : (originalPolynomial n t).eval x = originalB n t x := by
  simp only [originalPolynomial, originalB, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  apply Finset.sum_congr rfl
  intro j _
  dsimp [originalCoefficient]
  ring
private theorem original_polynomial_origin (n : ℕ) (t : ℝ) : (originalPolynomial n t).eval 0 = 1 ∧
      (originalPolynomial n t).derivative.eval 0 = 0 := by
  constructor
  · rw [← coeff_zero_eq_eval_zero, show 0=2*0 by omega, original_polynomial_coeff_even]
    simp [originalCoefficient]
  · rw [← coeff_zero_eq_eval_zero, coeff_derivative]
    simp only [zero_add, Nat.cast_one, mul_one]
    simpa using original_polynomial_coeff_odd n 0 t
private theorem original_polynomial_energy {n : ℕ} (hn : 1≤n) {t : ℝ} (ht : 0<t)
    {x : ℝ} (hx : 0≤x) : |(originalPolynomial n t).eval x| ≤ exp ((t/(2*(n:ℝ)))*x^2/2) := by
  let p := originalPolynomial n t
  let α := t/(2*(n:ℝ))
  let B := fun x : ℝ => p.eval x
  let D := fun x : ℝ => p.derivative.eval x
  let G := fun x : ℝ => exp (-α*x^2)*((B x)^2+(D x)^2/t)
  have hα : 0≤α := by dsimp [α]; positivity
  have hode (y : ℝ) : p.derivative.derivative.eval y = α*y*D y-t*B y := by
    have h := congrArg (fun q : ℝ[X] => q.eval y) (original_polynomial_ode hn t)
    simp only [eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_zero] at h
    dsimp [p,α,B,D] at *
    linarith
  have hdG (y : ℝ) : HasDerivAt G (-2*α*y*exp (-α*y^2)*(B y)^2) y := by
    have he : HasDerivAt (fun x : ℝ => exp (-α*x^2)) ((-α*(2*y))*exp (-α*y^2)) y := by
      convert! (((hasDerivAt_id y).pow 2).const_mul (-α)).exp using 1 <;>
        simp only [id_eq,Pi.pow_apply] <;> ring
    have hb := p.hasDerivAt y
    have hd := p.derivative.hasDerivAt y
    rw [hode y] at hd
    convert! he.mul ((hb.pow 2).add ((hd.pow 2).div_const t)) using 1 <;>
      dsimp [G,B,D] <;> field_simp [ht.ne'] <;> ring
  have hmono : AntitoneOn G (Ici 0) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
      (continuous_iff_continuousAt.mpr (fun y => (hdG y).continuousAt)).continuousOn
      (fun y _ => (hdG y).hasDerivWithinAt)
    intro y hy
    have hy0 : 0≤y := le_of_lt (by simpa only [interior_Ici, mem_Ioi] using hy)
    have h : 0≤2*α*y*exp (-α*y^2)*(B y)^2 := by positivity
    nlinarith
  have hzero : G 0=1 := by
    dsimp [G,B,D,p]
    rw [(original_polynomial_origin n t).1, (original_polynomial_origin n t).2]
    simp
  have hG : G x≤1 := by simpa only [hzero] using hmono (by simp) hx hx
  have heprod : exp (α*x^2)*G x = (B x)^2+(D x)^2/t := by
    dsimp [G]
    rw [← mul_assoc, ← exp_add]
    simp
  have hs : (B x)^2 ≤ exp (α*x^2) := by
    have h := mul_le_mul_of_nonneg_left hG (exp_pos (α*x^2)).le
    rw [heprod, mul_one] at h
    have hd : 0≤(D x)^2/t := by positivity
    linarith
  have he : exp (α*x^2/2)^2=exp (α*x^2) := by
    rw [← exp_nat_mul]
    congr 1
    ring
  change |B x| ≤ exp (α*x^2/2)
  apply (sq_le_sq₀ (abs_nonneg _) (exp_pos _).le).mp
  rw [sq_abs,he]
  exact hs
open private jetSize endpointConstant from D5.S3.Zeros.Jensen.OriginalPrimalTailProjection
private theorem monomial_jet {N : ℕ} (hN : 1≤N) (r k : ℕ) : IntegrableOn (fun x : ℝ => x^k*tailJet r N x) (Ioi 0) ∧
    Tendsto (fun x : ℝ => x^k*tailJet r N x) atTop (𝓝 0) := by
  have hbound {x : ℝ} (hx : 0≤x) : ‖x^k*tailJet r N x‖ ≤ (1+x)^k*|tailJet r N x| := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hx k)]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx (by linarith) k) (abs_nonneg _)
  have hi : IntegrableOn (fun x : ℝ => (1+x)^k*|tailJet r N x|) (Ioi 0) := by
    simpa using (tailJet_integral 0 r k N hN).1
  refine ⟨hi.mono' ((continuous_id.pow k).mul (tailJet_continuous r N hN)).aestronglyMeasurable (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact hbound hx.le), ?_⟩
  let A := modeScale (N+1)
  let c := jetSize r*endpointConstant 0 r k*A^(r+2)*exp (-A)*shiftedBudget (r+2)
  have hA : 0<A := by dsimp [A,modeScale]; positivity
  apply squeeze_zero_norm' (a := fun x : ℝ => c*exp (-A*x))
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    apply (hbound hx).trans
    simpa [c,A] using tailJet_endpoint 0 r k N hN hx
  · simpa using (tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (show -A<0 by linarith))).const_mul c
private theorem polynomial_jet {N : ℕ} (hN : 1≤N) (r : ℕ) (p : ℝ[X]) : IntegrableOn (fun x : ℝ => p.eval x*tailJet r N x) (Ioi 0) ∧
    Tendsto (fun x : ℝ => p.eval x*tailJet r N x) atTop (𝓝 0) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    constructor
    · convert! hp.1.add hq.1 using 1 <;> first | rfl | (ext x; simp [eval_add,add_mul])
    · simpa only [eval_add, add_mul, add_zero] using hp.2.add hq.2
  | monomial k c =>
    have h := monomial_jet hN r k
    constructor
    · change Integrable (fun x : ℝ => (monomial k c).eval x*tailJet r N x)
        (volume.restrict (Ioi (0:ℝ)))
      have hc : Integrable (fun x : ℝ => c*(x^k*tailJet r N x))
          (volume.restrict (Ioi (0:ℝ))) := h.1.const_mul c
      simpa only [eval_monomial,mul_assoc] using hc
    · simpa only [eval_monomial, mul_assoc, mul_zero] using h.2.const_mul c
private theorem polynomial_adjoint {N : ℕ} (hN : 1≤N) (α : ℝ) (p : ℝ[X]) : IntegrableOn (fun x : ℝ => p.eval x*densityAdjoint α (originalTail N) x) (Ioi 0) ∧
    Tendsto (fun x : ℝ => p.eval x*densityAdjoint α (originalTail N) x) atTop (𝓝 0) := by
  have h2 := polynomial_jet hN 2 p
  have h0 := polynomial_jet hN 0 (p*C α)
  have h1 := polynomial_jet hN 1 (p*C α*X)
  have he : (fun x : ℝ => p.eval x*densityAdjoint α (originalTail N) x) = fun x => p.eval x*tailJet 2 N x+(p*C α).eval x*tailJet 0 N x+
        (p*C α*X).eval x*tailJet 1 N x := by
    ext x
    rw [adjoint_formula N hN α x]
    simp only [eval_mul,eval_C,eval_X]
    ring
  rw [he]
  exact ⟨h2.1.add h0.1 |>.add h1.1, by simpa using h2.2.add h0.2 |>.add h1.2⟩
private theorem polynomial_adjoint_deriv_limit {N : ℕ} (hN : 1≤N) (α : ℝ) (p : ℝ[X]) : Tendsto (fun x : ℝ => p.eval x*deriv (densityAdjoint α (originalTail N)) x)
      atTop (𝓝 0) := by
  have h3 := (polynomial_jet hN 3 p).2
  have h1 := (polynomial_jet hN 1 (p*C (2*α))).2
  have h2 := (polynomial_jet hN 2 (p*C α*X)).2
  have he : (fun x : ℝ => p.eval x*deriv (densityAdjoint α (originalTail N)) x) = fun x => p.eval x*tailJet 3 N x+(p*C (2*α)).eval x*tailJet 1 N x+
        (p*C α*X).eval x*tailJet 2 N x := by
    ext x
    rw [(adjoint_deriv N hN α x).deriv]
    simp only [eval_mul,eval_C,eval_X]
    ring
  rw [he]
  simpa using (h3.add h1).add h2
private theorem polynomial_adjoint_square_integrable {N : ℕ} (hN : 1≤N)
    (α : ℝ) (p : ℝ[X]) : IntegrableOn (fun x : ℝ => p.eval x*
      densityAdjoint α (densityAdjoint α (originalTail N)) x) (Ioi 0) := by
  have h4 := (polynomial_jet hN 4 p).1
  have h3 := (polynomial_jet hN 3 (p*C (2*α)*X)).1
  have h2 := (polynomial_jet hN 2 (p*(C (4*α)+C (α^2)*X^2))).1
  have h1 := (polynomial_jet hN 1 (p*C (3*α^2)*X)).1
  have h0 := (polynomial_jet hN 0 (p*C (α^2))).1
  convert! (((h4.add h3).add h2).add h1).add h0 using 1
  ext x
  rw [adjoint_square N hN α x]
  simp only [Pi.add_apply,eval_mul,eval_C,eval_X,eval_add,eval_pow]
  ring
private theorem original_green {n : ℕ} (hn : 1≤n) (t : ℝ)
    (F : ℝ→ℝ) (hdF : Differentiable ℝ F) (hddF : Differentiable ℝ (deriv F))
    (hiF : IntegrableOn (fun x => (originalPolynomial n t).eval x*F x) (Ioi 0))
    (hiA : IntegrableOn (fun x => (originalPolynomial n t).eval x* densityAdjoint (t/(2*(n:ℝ))) F x) (Ioi 0))
    (hl0 : Tendsto (fun x => (originalPolynomial n t).eval x*deriv F x) atTop (𝓝 0))
    (hl1 : Tendsto (fun x => (originalPolynomial n t).derivative.eval x*F x) atTop (𝓝 0))
    (hl2 : Tendsto (fun x => (C (t/(2*(n:ℝ)))*X*originalPolynomial n t).eval x*F x) atTop (𝓝 0)) :
    (∫ x in Ioi (0:ℝ), (originalPolynomial n t).eval x* densityAdjoint (t/(2*(n:ℝ))) F x)+
      t*(∫ x in Ioi (0:ℝ), (originalPolynomial n t).eval x*F x) = -deriv F 0 := by
  let p := originalPolynomial n t
  let α := t/(2*(n:ℝ))
  let B := fun x : ℝ => p.eval x
  let D := fun x : ℝ => p.derivative.eval x
  let K := fun x : ℝ => B x*deriv F x-D x*F x+α*x*B x*F x
  have hode (x : ℝ) : p.derivative.derivative.eval x=α*x*D x-t*B x := by
    have h := congrArg (fun q : ℝ[X] => q.eval x) (original_polynomial_ode hn t)
    simp only [eval_add,eval_sub,eval_mul,eval_C,eval_X,eval_zero] at h
    dsimp [p,α,B,D] at *
    linarith
  have hdK (x : ℝ) : HasDerivAt K (B x*densityAdjoint α F x+t*(B x*F x)) x := by
    have hb := p.hasDerivAt x
    have hd := p.derivative.hasDerivAt x
    rw [hode x] at hd
    convert! ((hb.mul (hddF x).hasDerivAt).sub (hd.mul (hdF x).hasDerivAt)).add
      (((((hasDerivAt_id x).const_mul α).mul hb).mul (hdF x).hasDerivAt)) using 1 <;>
      dsimp [K,B,D,densityAdjoint] <;> ring
  have hlim : Tendsto K atTop (𝓝 0) := by
    have hl2' : Tendsto (fun x : ℝ => α*x*B x*F x) atTop (𝓝 0) := by
      simpa only [eval_mul,eval_C,eval_X] using hl2
    simpa [K,B,D] using (hl0.sub hl1).add hl2'
  have hi := hiA.add (hiF.const_mul t)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hdK x) hi hlim
  rw [integral_add hiA (hiF.const_mul t), integral_const_mul] at h
  have hzero : K 0=deriv F 0 := by
    dsimp [K,B,D,p]
    rw [(original_polynomial_origin n t).1,(original_polynomial_origin n t).2]
    ring
  simpa only [hzero,zero_sub] using h
private theorem original_moment_bridge (n : ℕ) (t : ℝ) : Integrable (fun x:ℝ => originalB n t x*sourceThetaDensity x) ∧
    originalJ n t = (sourceP n).eval (-t) ∧ (sourceJensenPolynomial n).eval (((-t:ℝ):ℂ)) = (originalJ n t:ℂ) ∧
    ((sourceJensenPolynomial n).eval (((-t:ℝ):ℂ)) = 0 ↔ originalJ n t = 0) := by
  let c := fun j:ℕ => (-1:ℝ)^j*(n.descFactorial j:ℝ)*t^j/ ((n:ℝ)^j*((2*j).factorial:ℝ))
  have hi (j:ℕ) : Integrable (fun x:ℝ => x^(2*j)*sourceThetaDensity x) := by
    simpa only [sourceThetaDensity, fullZ, mul_div_assoc] using
      (source_theta_raw_moments j).1.div_const fullZ
  have he (x:ℝ) : originalB n t x*sourceThetaDensity x = ∑ j ∈ Finset.range (n+1), c j*(x^(2*j)*sourceThetaDensity x) := by
    simp only [originalB, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [c]
    ring
  have hfi : Integrable (fun x:ℝ => originalB n t x*sourceThetaDensity x) := by
    simp_rw [he]
    exact integrable_finsetSum _ (fun j _ => (hi j).const_mul (c j))
  have hreal : originalJ n t = (sourceP n).eval (-t) := by
    dsimp [originalJ]
    simp_rw [he]
    rw [integral_finsetSum _ (fun j _ => (hi j).const_mul (c j))]
    simp only [sourceP, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, integral_const_mul]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [c,sourceThetaCoefficient,sourceThetaMoment]
    rw [neg_pow]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hcomplex : (sourceJensenPolynomial n).eval (((-t:ℝ):ℂ)) = (originalJ n t:ℂ) := by
    rw [← source_map]
    change ((sourceP n).map (algebraMap ℝ ℂ)).eval ((algebraMap ℝ ℂ) (-t)) = (algebraMap ℝ ℂ) (originalJ n t)
    rw [eval_map_apply, hreal]
  refine ⟨hfi, hreal, hcomplex, ?_⟩
  rw [hcomplex]
  exact Complex.ofReal_eq_zero
private theorem primal_source_mode (j : ℕ) (x : ℝ) : primalMode (j+1) |x| = thetaSummand j x := by
  have h9 : exp (|x|/2)*exp (4*|x|)=exp (9*|x|/2) := by
    rw [← exp_add]
    congr 1
    ring
  have h5 : exp (|x|/2)*exp (2*|x|)=exp (5*|x|/2) := by
    rw [← exp_add]
    congr 1
    ring
  dsimp [primalMode,modeScale,thetaSummand]
  simp only [neg_mul] at *
  linear_combination
    (4*Real.pi^2*((j+1:ℕ):ℝ)^4*exp (-(Real.pi*((j+1:ℕ):ℝ)^2*exp (2*|x|))))*h9- (6*Real.pi*((j+1:ℕ):ℝ)^2*exp (-(Real.pi*((j+1:ℕ):ℝ)^2*exp (2*|x|))))*h5
private theorem original_source_split (N : ℕ) {x : ℝ} (hx : 0≤x) : sourceThetaKernel x=originalHead N x+originalTail N x := by
  have hs : Summable (fun j : ℕ => primalMode (j+1) x) := by
    simpa only [← primal_source_mode,abs_of_nonneg hx] using source_theta_summable x
  have hsource : sourceThetaKernel x=∑' j : ℕ, primalMode (j+1) x := by
    unfold sourceThetaKernel
    apply tsum_congr
    intro j
    simpa only [abs_of_nonneg hx,thetaSummand] using (primal_source_mode j x).symm
  have hhead : originalHead N x=∑ j ∈ Finset.range N, primalMode (j+1) x := by
    dsimp [originalHead]
    rw [← Finset.Ico_add_one_right_eq_Icc,Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro j _
    rw [Nat.add_comm 1 j]
  rw [hsource,hhead]
  have h := hs.sum_add_tsum_nat_add N
  simpa only [originalTail,Nat.add_comm] using h.symm
private theorem original_full_source {N n : ℕ} (hN : 1≤N) (t : ℝ) : IntegrableOn (fun x : ℝ => originalB n t x*originalHead N x) (Ioi 0) ∧
    originalJ n t=(2/fullZ)* ((∫ x in Ioi (0:ℝ), originalB n t x*originalHead N x)+
        ∫ x in Ioi (0:ℝ), originalB n t x*originalTail N x) := by
  have hz : fullZ≠0 := ne_of_gt
    D5.S3.Analytic.Fourier.XiThetaTransform.source_theta_normalized.2.1
  dsimp [fullZ] at hz
  have hq : tailJet 0 N=originalTail N := by simpa using tailJet_eq_iterated 0 N hN
  have hiQ : IntegrableOn (fun x : ℝ => originalB n t x*originalTail N x) (Ioi 0) := by
    simpa only [original_polynomial_eval,hq] using (polynomial_jet hN 0 (originalPolynomial n t)).1
  have hraw : Integrable (fun x : ℝ => originalB n t x*sourceThetaKernel x) := by
    convert! (original_moment_bridge n t).1.mul_const fullZ using 1
    ext x
    dsimp [sourceThetaDensity,fullZ]
    field_simp [hz]
  have hhead : IntegrableOn (fun x : ℝ => originalB n t x*originalHead N x) (Ioi 0) := by
    apply (hraw.integrableOn.sub hiQ).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change originalB n t x*sourceThetaKernel x-originalB n t x*originalTail N x= originalB n t x*originalHead N x
    rw [original_source_split N hx.le]
    ring
  refine ⟨hhead,?_⟩
  have heven (x : ℝ) : originalB n t |x|=originalB n t x := by
    simp only [originalB,Even.pow_abs (even_two_mul _) x]
  have hkernel (x : ℝ) : sourceThetaKernel |x|=sourceThetaKernel x := by
    simp only [sourceThetaKernel,abs_abs]
  have hfull : (∫ x : ℝ, originalB n t x*sourceThetaKernel x)= 2*(∫ x in Ioi (0:ℝ), originalB n t x*sourceThetaKernel x) := by
    calc
      _ = ∫ x : ℝ, originalB n t |x| * sourceThetaKernel |x| := by
        simp only [heven,hkernel]
      _ = _ := integral_comp_abs (f := fun x : ℝ => originalB n t x*sourceThetaKernel x)
  dsimp [originalJ]
  simp only [sourceThetaDensity,← mul_div_assoc,integral_div]
  rw [hfull]
  have hray : (∫ x in Ioi (0:ℝ), originalB n t x*sourceThetaKernel x)= (∫ x in Ioi (0:ℝ), originalB n t x*originalHead N x)+
        ∫ x in Ioi (0:ℝ), originalB n t x*originalTail N x := by
    rw [← integral_add hhead hiQ]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [original_source_split N hx.le]
    ring
  rw [hray]
  dsimp [fullZ]
  ring
theorem original_primal_tail_response : 0 < fullZ ∧ (∫ x:ℝ, sourceThetaDensity x) = 1 ∧
  ∃ K:ℝ, 0<K ∧ ∀ a:ℝ, 0<a → ∃ C:ℝ, 0<C ∧ ∀ N n:ℕ, 1≤N → 1≤n → ∀ t:ℝ, 0<t → t/(2*(n:ℝ))≤a →
      let A := modeScale (N+1)
      let I := ∫ x in Set.Ioi (0:ℝ), originalB n t x*originalTail N x
      let H := ∫ x in Set.Ioi (0:ℝ), originalB n t x*originalHead N x
      0<originalFlux N ∧ MeasureTheory.IntegrableOn (fun x:ℝ => originalB n t x*originalTail N x) (Set.Ioi 0) ∧
      MeasureTheory.IntegrableOn (fun x:ℝ => originalB n t x*originalHead N x) (Set.Ioi 0) ∧ MeasureTheory.Integrable (fun x:ℝ => originalB n t x*sourceThetaDensity x) ∧
      originalJ n t = (sourceP n).eval (-t) ∧ originalJ n t = (2/fullZ)*(H+I) ∧
      (sourceJensenPolynomial n).eval (((-t:ℝ):ℂ)) = (originalJ n t:ℂ) ∧ sourceJensenPolynomial n = normalizedJensen sourceThetaCoefficient n ∧
      ((sourceJensenPolynomial n).eval (((-t:ℝ):ℂ)) = 0 ↔ originalJ n t = 0) ∧ |t*I/originalFlux N-1| ≤ C*((N:ℝ)+1)^4/t ∧
      (2*C*((N:ℝ)+1)^4 ≤ t → (originalJ n t=0 ∨ (sourceJensenPolynomial n).eval (((-t:ℝ):ℂ))=0) →
        (2/fullZ)*H ≤ -originalFlux N/(fullZ*t)) ∧ (max 12 a ≤ A → |(t+4*A^2)*I/originalFlux N-1| ≤ K/A) ∧
      (max (max 12 a) (2*K) ≤ A → originalFlux N/(2*(t+4*A^2)) ≤ I ∧
        0<originalFlux N/(2*(t+4*A^2)) ∧ ((originalJ n t=0 ∨ (sourceJensenPolynomial n).eval (((-t:ℝ):ℂ))=0) →
          (2/fullZ)*H ≤ -originalFlux N/(fullZ*(t+4*A^2)) ∧ -originalFlux N/(fullZ*(t+4*A^2))<0)) := by
  have hz := D5.S3.Analytic.Fourier.XiThetaTransform.source_theta_normalized
  obtain ⟨K,hK,hres⟩ := relative_residual
  refine ⟨hz.2.1,hz.2.2.1,K,hK,?_⟩
  intro a ha
  obtain ⟨C,hC,hW⟩ := original_primal_tail_budget a ha
  refine ⟨C,hC,?_⟩
  intro N n hN hn t ht hαa
  dsimp only
  let α := t/(2*(n:ℝ))
  let A := modeScale (N+1)
  let p := originalPolynomial n t
  let I := ∫ x in Ioi (0:ℝ), originalB n t x*originalTail N x
  let D := ∫ x in Ioi (0:ℝ), originalB n t x*densityAdjoint α (originalTail N) x
  let E := ∫ x in Ioi (0:ℝ), originalB n t x*densityAdjoint α (densityAdjoint α (originalTail N)) x
  let H := ∫ x in Ioi (0:ℝ), originalB n t x*originalHead N x
  have hα : 0≤α := by dsimp [α]; positivity
  have hw := hW N hN α hα hαa
  have hk := hw.2.2.1
  have hq0 : tailJet 0 N=originalTail N := by simpa using tailJet_eq_iterated 0 N hN
  have hq1 : deriv (originalTail N)=tailJet 1 N := by
    rw [← hq0]
    exact funext (fun x => (tailJet_deriv 0 N hN x).deriv)
  have hdQ : Differentiable ℝ (originalTail N) := by
    rw [← hq0]
    exact fun x => (tailJet_deriv 0 N hN x).differentiableAt
  have hddQ : Differentiable ℝ (deriv (originalTail N)) := by
    rw [hq1]
    exact fun x => (tailJet_deriv 1 N hN x).differentiableAt
  have hiQ : IntegrableOn (fun x : ℝ => originalB n t x*originalTail N x) (Ioi 0) := by
    convert! (polynomial_jet hN 0 p).1 using 1 <;>
      first | rfl | (ext x; simp [p,original_polynomial_eval,hq0])
  have hiD : IntegrableOn (fun x : ℝ => originalB n t x*densityAdjoint α (originalTail N) x) (Ioi 0) := by
    simpa only [p,original_polynomial_eval] using (polynomial_adjoint hN α p).1
  have hiE : IntegrableOn (fun x : ℝ => originalB n t x* densityAdjoint α (densityAdjoint α (originalTail N)) x) (Ioi 0) := by
    simpa only [p,original_polynomial_eval] using polynomial_adjoint_square_integrable hN α p
  have g1 : D+t*I=originalFlux N := by
    have hl0 : Tendsto (fun x : ℝ => p.eval x*deriv (originalTail N) x) atTop (𝓝 0) := by
      rw [hq1]
      exact (polynomial_jet hN 1 p).2
    have hl1 : Tendsto (fun x : ℝ => p.derivative.eval x*originalTail N x) atTop (𝓝 0) := by
      rw [← hq0]
      exact (polynomial_jet hN 0 p.derivative).2
    have hl2 : Tendsto (fun x : ℝ => (Polynomial.C α*X*p).eval x*originalTail N x) atTop (𝓝 0) := by
      rw [← hq0]
      exact (polynomial_jet hN 0 (Polynomial.C α*X*p)).2
    have h := original_green hn t (originalTail N) hdQ hddQ
      (by simpa only [original_polynomial_eval] using hiQ)
      (by simpa only [original_polynomial_eval] using hiD) hl0 hl1 hl2
    rw [← hw.2.1] at h
    simpa only [original_polynomial_eval] using h
  have g2 : E+t*D= -deriv (densityAdjoint α (originalTail N)) 0 := by
    have hdAQ : Differentiable ℝ (densityAdjoint α (originalTail N)) := fun x => (adjoint_deriv N hN α x).differentiableAt
    have hddAQ : Differentiable ℝ (deriv (densityAdjoint α (originalTail N))) := fun x => (adjoint_second_deriv N hN α x).differentiableAt
    have h := original_green hn t (densityAdjoint α (originalTail N)) hdAQ hddAQ
      (polynomial_adjoint hN α p).1
      (polynomial_adjoint_square_integrable hN α p)
      (polynomial_adjoint_deriv_limit hN α p)
      (polynomial_adjoint hN α p.derivative).2
      (polynomial_adjoint hN α (Polynomial.C α*X*p)).2
    simpa only [original_polynomial_eval] using h
  have hB {x : ℝ} (hx : 0≤x) : |originalB n t x|≤exp (a*x^2/2) := by
    rw [← original_polynomial_eval]
    apply (original_polynomial_energy hn ht hx).trans
    apply exp_le_exp.mpr
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hαa (sq_nonneg x)) (by norm_num)
  have hE : |E|≤∫ x in Ioi (0:ℝ), exp (a*x^2/2)* |densityAdjoint α (densityAdjoint α (originalTail N)) x| := by
    apply (abs_integral_le_integral_abs).trans
    apply integral_mono_ae hiE.abs hw.2.2.2.1
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hB hx.le) (abs_nonneg _)
  have hP : |t*I/originalFlux N-1|≤C*((N:ℝ)+1)^4/t := by
    apply (le_div_iff₀ ht).mpr
    have hid : (t*I/originalFlux N-1)*t= (deriv (densityAdjoint α (originalTail N)) 0+E)/originalFlux N := by
      apply (eq_div_iff hk.ne').mpr
      field_simp [hk.ne']
      nlinarith [congrArg (fun x : ℝ => t*x) g1]
    calc
      _ = |(t*I/originalFlux N-1)*t| := by rw [abs_mul,abs_of_pos ht]
      _ = |deriv (densityAdjoint α (originalTail N)) 0+E|/originalFlux N := by
        rw [hid,abs_div,abs_of_pos hk]
      _ ≤ _ := by
        apply (div_le_iff₀ hk).mpr
        exact (abs_add_le _ _).trans
          ((add_le_add_right hE _).trans (by simpa only [add_comm] using hw.2.2.2.2))
  have hm := original_moment_bridge n t
  have hs := original_full_source (n := n) hN t
  have hzero (h : originalJ n t=0 ∨ (sourceJensenPolynomial n).eval (((-t:ℝ):ℂ))=0) : H= -I := by
    have hj : originalJ n t=0 := h.elim id hm.2.2.2.mp
    have hz0 : 2/fullZ≠0 := div_ne_zero (by norm_num) (ne_of_gt hz.2.1)
    have hh := hs.2
    change originalJ n t=(2/fullZ)*(H+I) at hh
    rw [hj] at hh
    have hh' : H+I=0 := (mul_eq_zero.mp hh.symm).resolve_left hz0
    linarith
  have hnode_old : 2*C*((N:ℝ)+1)^4≤t → (originalJ n t=0 ∨ (sourceJensenPolynomial n).eval (((-t:ℝ):ℂ))=0) →
      (2/fullZ)*H≤ -originalFlux N/(fullZ*t) := by
    intro hth hnode
    rw [hzero hnode]
    have hhalf : C*((N:ℝ)+1)^4/t≤1/2 := by
      apply (div_le_iff₀ ht).mpr
      linarith
    have hlo : 1/2≤t*I/originalFlux N := by
      have h := (abs_le.mp (hP.trans hhalf)).1
      linarith
    have hI : originalFlux N/(2*t)≤I := by
      apply (div_le_iff₀ (by positivity : 0<2*t)).mpr
      have h := (le_div_iff₀ hk).mp hlo
      nlinarith
    have h := mul_le_mul_of_nonneg_left (neg_le_neg hI)
      (show 0≤2/fullZ from (div_pos (by norm_num) hz.2.1).le)
    convert! h using 1 <;> field_simp [ht.ne',ne_of_gt hz.2.1] <;> ring
  have hR : max 12 a≤A → |(t+4*A^2)*I/originalFlux N-1|≤K/A := by
    intro hA
    have hb := hres a N hN hA α hα hαa
    have hiR : IntegrableOn (fun x : ℝ => originalB n t x* (4*A^2*originalTail N x-densityAdjoint α (originalTail N) x)) (Ioi 0) := by
      change Integrable (fun x : ℝ => originalB n t x* (4*A^2*originalTail N x-densityAdjoint α (originalTail N) x))
        (volume.restrict (Ioi (0:ℝ)))
      have hq : Integrable (fun x : ℝ => originalB n t x*originalTail N x)
          (volume.restrict (Ioi (0:ℝ))) := hiQ
      have hd : Integrable (fun x : ℝ => originalB n t x*densityAdjoint α (originalTail N) x)
          (volume.restrict (Ioi (0:ℝ))) := hiD
      convert! (hq.const_mul (4*A^2)).sub hd using 1 <;>
        first | rfl | (ext x; simp only [Pi.sub_apply]; ring)
    have hRint : (∫ x in Ioi (0:ℝ), originalB n t x* (4*A^2*originalTail N x-densityAdjoint α (originalTail N) x)) = (t+4*A^2)*I-originalFlux N := by
      have he : (fun x : ℝ => originalB n t x* (4*A^2*originalTail N x-densityAdjoint α (originalTail N) x)) =
          fun x => (4*A^2)*(originalB n t x*originalTail N x)- originalB n t x*densityAdjoint α (originalTail N) x := by ext x; ring
      rw [he,integral_sub (hiQ.const_mul (4*A^2)) hiD,integral_const_mul]
      change 4*A^2*I-D=(t+4*A^2)*I-originalFlux N
      nlinarith [g1]
    have hbint : |(t+4*A^2)*I-originalFlux N|≤(K/A)*originalFlux N := by
      rw [← hRint]
      apply (abs_integral_le_integral_abs).trans
      apply le_trans (integral_mono_ae hiR.abs hb.1 ?_) hb.2
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hB hx.le) (abs_nonneg _)
    have hid : (t+4*A^2)*I/originalFlux N-1= ((t+4*A^2)*I-originalFlux N)/originalFlux N := by field_simp <;> ring
    rw [hid,abs_div,abs_of_pos hk]
    exact (div_le_iff₀ hk).mpr hbint
  refine ⟨hk,hiQ,hs.1,hm.1,hm.2.1,hs.2,hm.2.2.1, sourceJensenPolynomial_eq_normalizedJensen n hn,hm.2.2.2,hP,hnode_old,hR,?_⟩
  intro hA
  have hA0 : 0<A := lt_of_lt_of_le (by norm_num : (0:ℝ)<12)
    ((le_max_left 12 a).trans ((le_max_left (max 12 a) (2*K)).trans hA))
  have hKA : K/A≤1/2 := by
    apply (div_le_iff₀ hA0).mpr
    have h := (le_max_right (max 12 a) (2*K)).trans hA
    linarith
  have hr := hR ((le_max_left (max 12 a) (2*K)).trans hA)
  have htA : 0<t+4*A^2 := by positivity
  have hI : originalFlux N/(2*(t+4*A^2))≤I := by
    apply (div_le_iff₀ (by positivity : 0<2*(t+4*A^2))).mpr
    have hh := (abs_le.mp (hr.trans hKA)).1
    have hrat : 1/2≤(t+4*A^2)*I/originalFlux N := by linarith
    have h := (le_div_iff₀ hk).mp hrat
    nlinarith
  refine ⟨hI,by positivity,?_⟩
  intro hnode
  change (2/fullZ)*H≤ -originalFlux N/(fullZ*(t+4*A^2)) ∧ -originalFlux N/(fullZ*(t+4*A^2))<0
  rw [hzero hnode]
  constructor
  · have h := mul_le_mul_of_nonneg_left (neg_le_neg hI)
      (show 0≤2/fullZ from (div_pos (by norm_num) hz.2.1).le)
    convert! h using 1 <;> field_simp [htA.ne',ne_of_gt hz.2.1] <;> ring
  · exact div_neg_of_neg_of_pos (neg_neg_of_pos hk)
      (mul_pos (show 0<fullZ from hz.2.1) htA)
#print axioms original_primal_tail_response
#print axioms mode_residual_integral
#print axioms full_residual_integral
#print axioms original_moment_bridge
end D5.S3.Zeros.Jensen.OriginalPrimalTailResponse
