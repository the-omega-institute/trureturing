/- GID: D5/S3/Zeros/Jensen/OriginalTailDerivativeVectorResiduals
   generality: I
   mirror-B: D5/B/S3/Zeros/Jensen/OriginalTailDerivativeVectorResiduals
   mirror-E: none(waiver:universal-infinite-analytic-estimate)
   anchors: []
   utility: none
   digest: Weighted first and second residual budgets for the original primal theta tail. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Zeros.Jensen.OriginalPrimalTailResponse
import D5.S3.Zeros.Jensen.SourceJensenPositiveExtension

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Zeros.Jensen.OriginalTailDerivativeVector
open Real Set MeasureTheory Filter Polynomial
open scoped Topology
open OriginalPrimalTailProjection OriginalPrimalTailResponse
open NormalizedJensenDegreeLowering SourceJensenIntegralExtension
open private primalJet_zero primalJet_deriv shiftedBudget shifted_summable scale_summable
  flux_summable tailJet_summable_ray tailJet_deriv tailJet_continuous tailJet_eq_iterated
  adjoint_formula adjoint_deriv adjoint_second_deriv adjoint_square flux_eq from
  D5.S3.Zeros.Jensen.OriginalPrimalTailProjection
open private mode_residual_integral residual_series later_mode_sum scale_gap full_flux_lower
  originalCoefficient originalPolynomial original_coefficient_recurrence
  original_polynomial_eval original_polynomial_origin original_polynomial_ode
  original_polynomial_energy polynomial_jet polynomial_adjoint
  polynomial_adjoint_deriv_limit polynomial_adjoint_square_integrable original_green
  original_moment_bridge original_source_split original_full_source exp_increment jet_one jet_two from
  D5.S3.Zeros.Jensen.OriginalPrimalTailResponse

private theorem exp_pi_small : exp (-Real.pi) ≤ (1/16:ℝ) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ)≤3) 6
  norm_num [Finset.sum_range_succ] at h
  have hp : (16:ℝ) ≤ exp Real.pi := by
    have := exp_le_exp.mpr Real.pi_gt_three.le
    linarith
  rw [exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<16) hp

private theorem shifted_geometric (k l : ℕ) (r : ℝ) (hr : 0≤r)
    (hstep : ∀ j:ℕ, ((j+l+2:ℕ):ℝ) ≤ r*((j+l+1:ℕ):ℝ))
    (hq : ‖r^(2*k)/16‖<1) :
    (∑' j:ℕ, ((j+l+1:ℕ):ℝ)^(2*k)*exp (-Real.pi*((j+l:ℕ):ℝ))) ≤
      (((l+1:ℕ):ℝ)^(2*k)*(1/16:ℝ)^l)/(1-r^(2*k)/16) := by
  let q : ℝ := r^(2*k)/16
  have hq0 : 0≤q := by dsimp [q]; positivity
  have hex (j:ℕ) : exp (-Real.pi*(j:ℝ)) ≤ (1/16:ℝ)^j := by
    rw [show -Real.pi*(j:ℝ)=(j:ℝ)*(-Real.pi) by ring, exp_nat_mul]
    exact pow_le_pow_left₀ (exp_pos _).le exp_pi_small j
  have hb (j:ℕ) : ((j+l+1:ℕ):ℝ)^(2*k)*(1/16:ℝ)^(j+l) ≤
      (((l+1:ℕ):ℝ)^(2*k)*(1/16:ℝ)^l)*q^j := by
    induction j with
    | zero => simp
    | succ j ih =>
      have h := pow_le_pow_left₀ (Nat.cast_nonneg _) (hstep j) (2*k)
      rw [mul_pow] at h
      have hh := mul_le_mul_of_nonneg_right h
        (show 0≤(1/16:ℝ)^(j+1+l) by positivity)
      have he : (1/16:ℝ)^(j+1+l) = (1/16:ℝ)^(j+l)*(1/16) := by
        rw [show j+1+l=(j+l)+1 by omega,pow_succ]
      rw [he] at hh
      calc
        _ ≤ r^(2*k)*(((j+l+1:ℕ):ℝ)^(2*k)*(1/16:ℝ)^(j+l))*(1/16) := by
          rw [show j+1+l+1=j+l+2 by omega, show j+1+l=j+l+1 by omega, pow_succ]
          simpa only [mul_assoc] using hh
        _ ≤ r^(2*k)*((((l+1:ℕ):ℝ)^(2*k)*(1/16:ℝ)^l)*q^j)*(1/16) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left ih (pow_nonneg hr _)) (by norm_num)
        _ = _ := by dsimp [q]; rw [pow_succ]; ring
  have hs := (shifted_summable k).comp_injective (add_left_injective l)
  have hg := (summable_geometric_of_norm_lt_one hq).mul_left
    (((l+1:ℕ):ℝ)^(2*k)*(1/16:ℝ)^l)
  have h := hs.tsum_le_tsum (fun j =>
    (mul_le_mul_of_nonneg_left (hex (j+l)) (by positivity)).trans (hb j)) hg
  simp only [tsum_mul_left] at h
  rw [tsum_geometric_of_norm_lt_one hq] at h
  simpa only [Function.comp_def,q,div_eq_mul_inv] using h

private theorem shifted_explicit : shiftedBudget 2-1≤2 ∧ shiftedBudget 3-1≤9 := by
  have hs2 := shifted_geometric 2 1 (3/2) (by norm_num) (by
    intro j; push_cast; linarith [Nat.cast_nonneg (α := ℝ) j]) (by norm_num)
  have hs3 := shifted_geometric 3 2 (4/3) (by norm_num) (by
    intro j; push_cast; linarith [Nat.cast_nonneg (α := ℝ) j]) (by norm_num)
  have he2 := (shifted_summable 2).sum_add_tsum_nat_add 1
  have he3 := (shifted_summable 3).sum_add_tsum_nat_add 2
  norm_num [Finset.sum_range_succ] at he2 he3
  have h1 : (2:ℝ)^6*exp (-Real.pi)≤4 := by
    nlinarith [exp_pi_small]
  norm_num at hs2 hs3
  constructor
  · dsimp [shiftedBudget]
    push_cast
    simp only [neg_mul]
    norm_num at h1
    linarith
  · dsimp [shiftedBudget]
    push_cast
    simp only [neg_mul]
    norm_num at h1
    linarith

private theorem weighted_monomial_pointwise {a s x:ℝ} (k:ℕ)
    (hs:64≤s) (has:a≤s) (hk:k≤6) (hx:0≤x) :
    exp (a*x^2/2)*exp (x/2)*exp (-s*exp (2*x))*(s*exp (2*x))^k ≤
      s^k*exp (-s)*exp (-s*x) := by
  have hc : (k:ℝ)≤6 := by exact_mod_cast hk
  have he := quadratic_le_exp_of_nonneg (show 0≤2*x by linarith)
  have he' := mul_le_mul_of_nonneg_left he (show 0≤s by linarith)
  have hq := mul_nonneg (sq_nonneg x) (show 0≤2*s-a/2 by linarith)
  have hl := mul_nonneg hx (show 0≤s-(2*(k:ℝ)+1/2) by linarith)
  have hpow : exp (2*x)^k=exp ((2*(k:ℝ))*x) := by
    rw [←exp_nat_mul]; congr 1; ring
  rw [mul_pow,hpow]
  have hex : exp (a*x^2/2)*exp (x/2)*exp (-s*exp (2*x))*
      exp ((2*(k:ℝ))*x) ≤ exp (-s)*exp (-s*x) := by
    simp only [←exp_add]
    apply exp_le_exp.mpr
    nlinarith
  convert! mul_le_mul_of_nonneg_left hex (pow_nonneg (show 0≤s by linarith) k)
    using 1 <;> ring

private theorem monomial_exp_integral (p:ℕ) {s:ℝ} (hs:0<s) :
    IntegrableOn (fun x:ℝ => x^p*exp (-s*x)) (Ioi 0) ∧
      (∫ x in Ioi (0:ℝ), x^p*exp (-s*x))=(p.factorial:ℝ)/s^(p+1) := by
  have hi := integrableOn_rpow_mul_exp_neg_mul_rpow (p:=1) (s:=(p:ℝ))
    (b:=s) (by linarith [Nat.cast_nonneg (α:=ℝ) p]) (by norm_num) hs
  have he := integral_rpow_mul_exp_neg_mul_Ioi (a:=(p:ℝ)+1) (r:=s)
    (by positivity) hs
  simp only [show (p:ℝ)+1-1=(p:ℝ) by ring, rpow_natCast] at he
  rw [Gamma_nat_eq_factorial, show (p:ℝ)+1=((p+1:ℕ):ℝ) by push_cast; ring,
    rpow_natCast] at he
  refine ⟨by simpa using hi,?_⟩
  simpa [one_div_pow,div_eq_mul_inv,mul_comm] using he

private theorem weighted_monomial_integral (p k:ℕ) {a s:ℝ}
    (hs:64≤s) (has:a≤s) (hk:k≤6) :
    IntegrableOn (fun x:ℝ => x^p*exp (a*x^2/2)*exp (x/2)*
      exp (-s*exp (2*x))*(s*exp (2*x))^k) (Ioi 0) ∧
    (∫ x in Ioi (0:ℝ), x^p*exp (a*x^2/2)*exp (x/2)*
      exp (-s*exp (2*x))*(s*exp (2*x))^k) ≤
      (p.factorial:ℝ)*s^k/s^(p+1)*exp (-s) := by
  have hs0 : 0<s := by linarith
  have hg := (monomial_exp_integral p hs0).1.const_mul (s^k*exp (-s))
  have hb {x:ℝ} (hx:0≤x) := mul_le_mul_of_nonneg_left
    (weighted_monomial_pointwise k hs has hk hx) (pow_nonneg hx p)
  have hi : IntegrableOn (fun x:ℝ => x^p*exp (a*x^2/2)*exp (x/2)*
      exp (-s*exp (2*x))*(s*exp (2*x))^k) (Ioi 0) := by
    apply hg.mono' (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0≤x := hx.le
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    convert! hb hx.le using 1 <;> ring
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ x in Ioi (0:ℝ), (s^k*exp (-s))*(x^p*exp (-s*x)) := by
      apply integral_mono_ae hi hg
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      convert! hb hx.le using 1 <;> ring
    _ = _ := by
      rw [integral_const_mul,(monomial_exp_integral p hs0).2]
      ring


private theorem jet_three (z : ℝ) :
    (jetPolynomial 3).eval z = -32*z^5+360*z^4-1058*z^3+(1635/2)*z^2-(375/4)*z := by
  norm_num [jetPolynomial, derivative_sub, derivative_mul, derivative_pow]
  <;> ring

private theorem jet_four (z : ℝ) :
    (jetPolynomial 4).eval z = 64*z^6-1056*z^5+5176*z^4-8512*z^3+
      (15465/4)*z^2-(1875/8)*z := by
  norm_num [jetPolynomial, derivative_sub, derivative_mul, derivative_pow]
  <;> ring

private theorem jet_bounds_64 {z : ℝ} (hz : 64≤z) :
    |(jetPolynomial 0).eval z|≤4*z^2 ∧
    |(jetPolynomial 1).eval z|≤9*z^3 ∧
    |(jetPolynomial 2).eval z|≤18*z^4 ∧
    |(jetPolynomial 3).eval z|≤38*z^5 ∧
    |(jetPolynomial 4).eval z|≤82*z^6 ∧
    |(jetPolynomial 2).eval z-4*z^2*(jetPolynomial 0).eval z|≤91*z^3 ∧
    |(jetPolynomial 4).eval z-16*z^4*(jetPolynomial 0).eval z|≤1044*z^5 := by
  let u := z-64
  have hu : 0≤u := by dsimp [u]; linarith
  have he : z=u+64 := by dsimp [u]; ring
  have h0 : (jetPolynomial 0).eval z=4*z^2-6*z := by simp [jetPolynomial]
  rw [h0,jet_one,jet_two,jet_three,jet_four]
  have hH : (16*z^4-112*z^3+165*z^2-(75/2)*z)-4*z^2*(4*z^2-6*z)=
      -88*z^3+165*z^2-(75/2)*z := by ring
  have hJ : (64*z^6-1056*z^5+5176*z^4-8512*z^3+(15465/4)*z^2-(1875/8)*z)-
      16*z^4*(4*z^2-6*z)=
      -960*z^5+5176*z^4-8512*z^3+(15465/4)*z^2-(1875/8)*z := by ring
  rw [hH,hJ]
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  all_goals
    apply abs_le.mpr
    constructor
    · apply neg_le_iff_add_nonneg.mpr
      rw [he]
      ring_nf
      positivity
    · apply sub_nonneg.mp
      rw [he]
      ring_nf
      positivity

private theorem first_mode_pure {A x:ℝ} (hA:64≤A) (hx:0≤x) :
    let z := A*exp (2*x)
    |(jetPolynomial 4).eval z-8*A^2*(jetPolynomial 2).eval z+
      16*A^4*(jetPolynomial 0).eval z| ≤ 1024*x^2*z^6+1772*z^5 := by
  let z := A*exp (2*x)
  have hA0 : 0≤A := by linarith
  have hAz : A≤z := by dsimp [z]; nlinarith [one_le_exp_iff.mpr (show 0≤2*x by linarith)]
  have hz : 64≤z := hA.trans hAz
  have hz0 : 0≤z := by linarith
  have hb := jet_bounds_64 hz
  have hs : A^2≤z^2 := pow_le_pow_left₀ hA0 hAz 2
  have hinc : z^2-A^2≤4*x*z^2 := by
    have h := mul_le_mul_of_nonneg_left (exp_increment hx) (sq_nonneg A)
    dsimp [z]
    rw [mul_pow,show exp (2*x)^2=exp (4*x) by rw [←exp_nat_mul]; congr 1; ring]
    nlinarith
  have hlead : (4*A^2-4*z^2)^2≤256*x^2*z^4 := by
    have h := pow_le_pow_left₀ (show 0≤z^2-A^2 by linarith) hinc 2
    nlinarith
  have h := mul_le_mul hlead hb.1 (abs_nonneg _) (by positivity : 0≤256*x^2*z^4)
  have hlead' : |(4*A^2-4*z^2)^2*(jetPolynomial 0).eval z|≤1024*x^2*z^6 := by
    rw [abs_mul,abs_of_nonneg (sq_nonneg _)]
    convert! h using 1 <;> ring
  have hH := mul_le_mul_of_nonneg_left hb.2.2.2.2.2.1
    (show 0≤8*A^2 by positivity)
  have hH' : |8*A^2*((jetPolynomial 2).eval z-4*z^2*(jetPolynomial 0).eval z)|≤728*z^5 := by
    rw [abs_mul,abs_of_nonneg (by positivity : 0≤8*A^2)]
    apply hH.trans
    have h := mul_le_mul_of_nonneg_right hs (show 0≤728*z^3 by positivity)
    nlinarith
  have hid : (jetPolynomial 4).eval z-8*A^2*(jetPolynomial 2).eval z+
      16*A^4*(jetPolynomial 0).eval z =
      (4*A^2-4*z^2)^2*(jetPolynomial 0).eval z+
        ((jetPolynomial 4).eval z-16*z^4*(jetPolynomial 0).eval z)-
        8*A^2*((jetPolynomial 2).eval z-4*z^2*(jetPolynomial 0).eval z) := by ring
  change |_|≤_
  rw [hid]
  let u := (4*A^2-4*z^2)^2*(jetPolynomial 0).eval z
  let v := (jetPolynomial 4).eval z-16*z^4*(jetPolynomial 0).eval z
  let w := 8*A^2*((jetPolynomial 2).eval z-4*z^2*(jetPolynomial 0).eval z)
  have htri : |(4*A^2-4*z^2)^2*(jetPolynomial 0).eval z+
      ((jetPolynomial 4).eval z-16*z^4*(jetPolynomial 0).eval z)-
      8*A^2*((jetPolynomial 2).eval z-4*z^2*(jetPolynomial 0).eval z)| ≤
      |(4*A^2-4*z^2)^2*(jetPolynomial 0).eval z|+
      |(jetPolynomial 4).eval z-16*z^4*(jetPolynomial 0).eval z|+
      |8*A^2*((jetPolynomial 2).eval z-4*z^2*(jetPolynomial 0).eval z)| := by
    change |u+v-w|≤|u|+|v|+|w|
    simpa only [sub_eq_add_neg,abs_neg] using
      (abs_add_le (u+v) (-w)).trans (add_le_add (abs_add_le u v) (le_refl (abs (-w))))
  convert! htri.trans (add_le_add (add_le_add hlead' hb.2.2.2.2.2.2) hH') using 1
  dsimp [z]
  ring


private def secondPolynomial (A α x z : ℝ) : ℝ :=
  (jetPolynomial 4).eval z-8*A^2*(jetPolynomial 2).eval z+
    16*A^4*(jetPolynomial 0).eval z+2*α*x*(jetPolynomial 3).eval z+
    (4*α+α^2*x^2)*(jetPolynomial 2).eval z+3*α^2*x*(jetPolynomial 1).eval z+
    α^2*(jetPolynomial 0).eval z-8*A^2*α*((jetPolynomial 0).eval z+
      x*(jetPolynomial 1).eval z)

private def secondMode (A α : ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  exp (x/2)*exp (-modeScale m*exp (2*x))*
    secondPolynomial A α x (modeScale m*exp (2*x))

private def driftTerms (A α x z : ℝ) : Fin 7 → ℝ :=
  ![2*α*x*(jetPolynomial 3).eval z,4*α*(jetPolynomial 2).eval z,
    α^2*x^2*(jetPolynomial 2).eval z,3*α^2*x*(jetPolynomial 1).eval z,
    α^2*(jetPolynomial 0).eval z,-8*A^2*α*(jetPolynomial 0).eval z,
    -8*A^2*α*x*(jetPolynomial 1).eval z]

private theorem second_poly_bound {A α x z P : ℝ} (hA : 0≤A) (hα : 0≤α)
    (hx : 0≤x) (hz : 64≤z)
    (hP : |(jetPolynomial 4).eval z-8*A^2*(jetPolynomial 2).eval z+
      16*A^4*(jetPolynomial 0).eval z|≤P) :
    |secondPolynomial A α x z|≤P+76*α*x*z^5+72*α*z^4+18*α^2*x^2*z^4+
      27*α^2*x*z^3+4*α^2*z^2+32*A^2*α*z^2+72*A^2*α*x*z^3 := by
  have hb := jet_bounds_64 hz
  have hz0 : 0≤z := by linarith
  let bd : Fin 7 → ℝ := ![76*α*x*z^5,72*α*z^4,18*α^2*x^2*z^4,
    27*α^2*x*z^3,4*α^2*z^2,32*A^2*α*z^2,72*A^2*α*x*z^3]
  have hd (i : Fin 7) : |driftTerms A α x z i|≤bd i := by
    fin_cases i
    · change |2*α*x*(jetPolynomial 3).eval z|≤76*α*x*z^5
      rw [abs_mul,abs_of_nonneg (by positivity : 0≤2*α*x)]
      convert! mul_le_mul_of_nonneg_left hb.2.2.2.1 (show 0≤2*α*x by positivity) using 1 <;> ring
    · change |4*α*(jetPolynomial 2).eval z|≤72*α*z^4
      rw [abs_mul,abs_of_nonneg (by positivity : 0≤4*α)]
      convert! mul_le_mul_of_nonneg_left hb.2.2.1 (show 0≤4*α by positivity) using 1 <;> ring
    · change |α^2*x^2*(jetPolynomial 2).eval z|≤18*α^2*x^2*z^4
      rw [abs_mul,abs_of_nonneg (by positivity : 0≤α^2*x^2)]
      convert! mul_le_mul_of_nonneg_left hb.2.2.1 (show 0≤α^2*x^2 by positivity) using 1 <;> ring
    · change |3*α^2*x*(jetPolynomial 1).eval z|≤27*α^2*x*z^3
      rw [abs_mul,abs_of_nonneg (by positivity : 0≤3*α^2*x)]
      convert! mul_le_mul_of_nonneg_left hb.2.1 (show 0≤3*α^2*x by positivity) using 1 <;> ring
    · change |α^2*(jetPolynomial 0).eval z|≤4*α^2*z^2
      rw [abs_mul,abs_of_nonneg (by positivity : 0≤α^2)]
      convert! mul_le_mul_of_nonneg_left hb.1 (show 0≤α^2 by positivity) using 1 <;> ring
    · change |-8*A^2*α*(jetPolynomial 0).eval z|≤32*A^2*α*z^2
      rw [show -8*A^2*α*(jetPolynomial 0).eval z= -(8*A^2*α*(jetPolynomial 0).eval z) by ring,abs_neg]
      rw [abs_mul,abs_of_nonneg (by positivity : 0≤8*A^2*α)]
      convert! mul_le_mul_of_nonneg_left hb.1 (show 0≤8*A^2*α by positivity) using 1 <;> ring
    · change |-8*A^2*α*x*(jetPolynomial 1).eval z|≤72*A^2*α*x*z^3
      rw [show -8*A^2*α*x*(jetPolynomial 1).eval z= -(8*A^2*α*x*(jetPolynomial 1).eval z) by ring,abs_neg]
      rw [abs_mul,abs_of_nonneg (by positivity : 0≤8*A^2*α*x)]
      convert! mul_le_mul_of_nonneg_left hb.2.1 (show 0≤8*A^2*α*x by positivity) using 1 <;> ring
  have hid : secondPolynomial A α x z =
      ((jetPolynomial 4).eval z-8*A^2*(jetPolynomial 2).eval z+
        16*A^4*(jetPolynomial 0).eval z)+∑ i:Fin 7, driftTerms A α x z i := by
    simp [secondPolynomial,driftTerms,Fin.sum_univ_succ]
    ring
  rw [hid]
  calc
    _ ≤ |(jetPolynomial 4).eval z-8*A^2*(jetPolynomial 2).eval z+
        16*A^4*(jetPolynomial 0).eval z|+∑ i:Fin 7, |driftTerms A α x z i| :=
      (abs_add_le _ _).trans (add_le_add (le_refl _) (Finset.abs_sum_le_sum_abs _ _))
    _ ≤ P+∑ i:Fin 7,bd i := add_le_add hP (Finset.sum_le_sum (fun i _ => hd i))
    _ = _ := by simp [bd,Fin.sum_univ_succ]; ring

private theorem later_mode_pure {A z:ℝ} (hA:0≤A) (hz:64≤z) :
    |(jetPolynomial 4).eval z-8*A^2*(jetPolynomial 2).eval z+
      16*A^4*(jetPolynomial 0).eval z| ≤82*z^6+144*A^2*z^4+64*A^4*z^2 := by
  have hb := jet_bounds_64 hz
  have h0 := mul_le_mul_of_nonneg_left hb.1 (show 0≤16*A^4 by positivity)
  have h2 := mul_le_mul_of_nonneg_left hb.2.2.1 (show 0≤8*A^2 by positivity)
  have h4 := hb.2.2.2.2.1
  have htri : |(jetPolynomial 4).eval z-8*A^2*(jetPolynomial 2).eval z+
      16*A^4*(jetPolynomial 0).eval z| ≤
      |(jetPolynomial 4).eval z|+|8*A^2*(jetPolynomial 2).eval z|+
      |16*A^4*(jetPolynomial 0).eval z| := by
    simpa only [sub_eq_add_neg,abs_neg] using
      (abs_add_le ((jetPolynomial 4).eval z+-(8*A^2*(jetPolynomial 2).eval z))
        (16*A^4*(jetPolynomial 0).eval z)).trans
        (add_le_add (abs_add_le ((jetPolynomial 4).eval z)
          (-(8*A^2*(jetPolynomial 2).eval z))) (le_refl _))
  simp only [abs_mul] at htri
  simp only [abs_of_nonneg (sq_nonneg A),abs_of_nonneg (pow_nonneg hA 4)] at htri
  norm_num at htri
  nlinarith

private def weightedTerm (p k : ℕ) (a s x : ℝ) : ℝ :=
  x^p*exp (a*x^2/2)*exp (x/2)*exp (-s*exp (2*x))*(s*exp (2*x))^k

private def firstTerms (A α : ℝ) : Fin 9 → ℕ×ℕ×ℝ :=
  ![(4,6,1024),(2,5,1772),(3,5,76*α),(2,4,72*α),(4,4,18*α^2),
    (3,3,27*α^2),(2,2,4*α^2),(2,2,32*A^2*α),(3,3,72*A^2*α)]

private def laterTerms (A α : ℝ) : Fin 10 → ℕ×ℕ×ℝ :=
  ![(2,6,82),(2,4,144*A^2),(2,2,64*A^4),(3,5,76*α),(2,4,72*α),
    (4,4,18*α^2),(3,3,27*α^2),(2,2,4*α^2),(2,2,32*A^2*α),(3,3,72*A^2*α)]

private theorem majorant_integral {l:ℕ} (d:Fin l→ℕ×ℕ×ℝ) {a s:ℝ}
    (hs:64≤s) (has:a≤s) (hc:∀ i,0≤(d i).2.2) (hk:∀ i,(d i).2.1≤6) :
    IntegrableOn (fun x:ℝ => ∑ i:Fin l,(d i).2.2*weightedTerm (d i).1 (d i).2.1 a s x)
      (Ioi 0) ∧
    (∫ x in Ioi (0:ℝ), ∑ i:Fin l,(d i).2.2*weightedTerm (d i).1 (d i).2.1 a s x) ≤
      ∑ i:Fin l,(d i).2.2*((((d i).1).factorial:ℝ)*s^((d i).2.1)/s^((d i).1+1)*exp (-s)) := by
  have hi (i:Fin l) : IntegrableOn (weightedTerm (d i).1 (d i).2.1 a s) (Ioi 0) :=
    (weighted_monomial_integral (d i).1 (d i).2.1 hs has (hk i)).1
  have hci (i:Fin l) : IntegrableOn
      (fun x => (d i).2.2*weightedTerm (d i).1 (d i).2.1 a s x) (Ioi 0) :=
    (hi i).const_mul _
  refine ⟨integrable_finsetSum _ (fun i _ => hci i),?_⟩
  rw [integral_finsetSum _ (fun i _ => hci i)]
  apply Finset.sum_le_sum
  intro i _
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left
    (weighted_monomial_integral (d i).1 (d i).2.1 hs has (hk i)).2 (hc i)

private theorem second_mode_first {a α:ℝ} {m:ℕ}
    (hs:64≤modeScale m) (has:a≤modeScale m) (hα:0≤α) (hαs:α≤modeScale m) :
    IntegrableOn (fun x:ℝ => x^2*exp (a*x^2/2)*|secondMode (modeScale m) α m x|) (Ioi 0) ∧
    (∫ x in Ioi (0:ℝ), x^2*exp (a*x^2/2)*|secondMode (modeScale m) α m x|) ≤
      5100*(modeScale m)^2*exp (-modeScale m) := by
  let s:=modeScale m
  let d:=firstTerms s α
  have hs0:0<s := by dsimp [s]; linarith
  have hg := majorant_integral d hs has (by
    intro i; fin_cases i <;> simp [d,firstTerms] <;> positivity) (by
    intro i; fin_cases i <;> simp [d,firstTerms])
  have hb {x:ℝ} (hx:0≤x) : x^2*exp (a*x^2/2)*|secondMode s α m x|≤
      ∑ i:Fin 9,(d i).2.2*weightedTerm (d i).1 (d i).2.1 a s x := by
    have hsz : s≤s*exp (2*x) := by nlinarith [one_le_exp_iff.mpr (show 0≤2*x by linarith)]
    have h:=second_poly_bound hs0.le hα hx (hs.trans hsz) (first_mode_pure hs hx)
    have hw:=mul_le_mul_of_nonneg_left h
      (show 0≤x^2*exp (a*x^2/2)*(exp (x/2)*exp (-s*exp (2*x))) by positivity)
    dsimp [secondMode]
    rw [abs_mul,abs_of_pos (by positivity : 0<exp (x/2)*exp (-modeScale m*exp (2*x)))]
    convert! hw using 1 <;> simp [d,firstTerms,weightedTerm,Fin.sum_univ_succ,s] <;> ring
  have hi : IntegrableOn (fun x:ℝ => x^2*exp (a*x^2/2)*|secondMode s α m x|) (Ioi 0) := by
    apply hg.1.mono' (by dsimp [secondMode,secondPolynomial]; fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact hb hx.le
  refine ⟨hi,?_⟩
  apply (integral_mono_ae hi hg.1 (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact hb hx.le)).trans (hg.2.trans ?_)
  have he : (∑ i:Fin 9,(d i).2.2*
      ((((d i).1).factorial:ℝ)*s^((d i).2.1)/s^((d i).1+1)*exp (-s)))=
      (3544*s^2+24576*s+1096*α*s+602*α^2/s)*exp (-s) := by
    simp [d,firstTerms,Fin.sum_univ_succ]
    field_simp [hs0.ne']
    ring
  rw [he]
  have h64 : (64:ℝ)≤s := hs
  have hsq : α^2≤s^2 := pow_le_pow_left₀ hα hαs 2
  have hdiv : α^2/s≤s := by apply (div_le_iff₀ hs0).mpr; nlinarith
  have hαmul : α*s≤s*s := mul_le_mul_of_nonneg_right hαs hs0.le
  have hsize : 3544*s^2+24576*s+1096*α*s+602*α^2/s≤5100*s^2 := by
    have h64mul : 64*s≤s^2 := by nlinarith [mul_nonneg hs0.le (show 0≤s-64 by linarith)]
    simp only [div_eq_mul_inv] at hdiv ⊢
    nlinarith only [hαmul,hdiv,h64mul]
  exact mul_le_mul_of_nonneg_right hsize (exp_pos _).le

private theorem second_mode_later {A a α:ℝ} {m:ℕ}
    (hA:64≤A) (hAs:A≤modeScale m) (has:a≤modeScale m)
    (hα:0≤α) (hαA:α≤A) :
    IntegrableOn (fun x:ℝ => x^2*exp (a*x^2/2)*|secondMode A α m x|) (Ioi 0) ∧
    (∫ x in Ioi (0:ℝ), x^2*exp (a*x^2/2)*|secondMode A α m x|) ≤
      600*(modeScale m)^3*exp (-modeScale m) := by
  let s:=modeScale m
  let d:=laterTerms A α
  have hs:64≤s := hA.trans hAs
  have hs0:0<s := by linarith
  have hA0:0≤A := by linarith
  have hg := majorant_integral d hs has (by
    intro i; fin_cases i <;> simp [d,laterTerms] <;> positivity) (by
    intro i; fin_cases i <;> simp [d,laterTerms])
  have hb {x:ℝ} (hx:0≤x) : x^2*exp (a*x^2/2)*|secondMode A α m x|≤
      ∑ i:Fin 10,(d i).2.2*weightedTerm (d i).1 (d i).2.1 a s x := by
    have hsz : s≤s*exp (2*x) := by nlinarith [one_le_exp_iff.mpr (show 0≤2*x by linarith)]
    have hz:64≤s*exp (2*x) := hs.trans hsz
    have h:=second_poly_bound hA0 hα hx hz (later_mode_pure hA0 hz)
    have hw:=mul_le_mul_of_nonneg_left h
      (show 0≤x^2*exp (a*x^2/2)*(exp (x/2)*exp (-s*exp (2*x))) by positivity)
    dsimp [secondMode]
    rw [abs_mul,abs_of_pos (by positivity : 0<exp (x/2)*exp (-modeScale m*exp (2*x)))]
    convert! hw using 1 <;> simp [d,laterTerms,weightedTerm,Fin.sum_univ_succ,s] <;> ring
  have hi : IntegrableOn (fun x:ℝ => x^2*exp (a*x^2/2)*|secondMode A α m x|) (Ioi 0) := by
    apply hg.1.mono' (by dsimp [secondMode,secondPolynomial]; fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact hb hx.le
  refine ⟨hi,?_⟩
  apply (integral_mono_ae hi hg.1 (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact hb hx.le)).trans (hg.2.trans ?_)
  have he : (∑ i:Fin 10,(d i).2.2*
      ((((d i).1).factorial:ℝ)*s^((d i).2.1)/s^((d i).1+1)*exp (-s)))=
      (164*s^3+288*A^2*s+128*A^4/s+600*α*s+496*A^2*α/s+602*α^2/s)*exp (-s) := by
    simp [d,laterTerms,Fin.sum_univ_succ]
    field_simp [hs0.ne']
    ring
  rw [he]
  have hsq : A^2≤s^2 := pow_le_pow_left₀ hA0 hAs 2
  have h4 : A^4≤s^4 := pow_le_pow_left₀ hA0 hAs 4
  have hαs : α≤s := hαA.trans hAs
  have hα2:=pow_le_pow_left₀ hα hαs 2
  have hd1:A^4/s≤s^3 := by apply (div_le_iff₀ hs0).mpr; nlinarith [h4]
  have hd2:A^2*α/s≤s^2 := by
    apply (div_le_iff₀ hs0).mpr
    have h:=mul_le_mul hsq hαs hα (sq_nonneg s)
    nlinarith
  have hd3:α^2/s≤s := by apply (div_le_iff₀ hs0).mpr; nlinarith
  have h1:=mul_le_mul_of_nonneg_right hsq hs0.le
  have h2:=mul_le_mul_of_nonneg_right hαs hs0.le
  have hsize : 164*s^3+288*A^2*s+128*A^4/s+600*α*s+496*A^2*α/s+602*α^2/s≤600*s^3 := by
    have h64:=mul_nonneg (show 0≤s-64 by linarith) (sq_nonneg s)
    have h64':=mul_nonneg (show 0≤s-64 by linarith) hs0.le
    simp only [div_eq_mul_inv] at hd1 hd2 hd3 ⊢
    nlinarith only [h1,h2,hd1,hd2,hd3,h64,h64']
  exact mul_le_mul_of_nonneg_right hsize (exp_pos _).le


/-- The first residual uses the actual spatial adjoint with fixed alpha. -/
def tailResidual (N : ℕ) (A α x : ℝ) : ℝ :=
  4*A^2*originalTail N x-densityAdjoint α (originalTail N) x

/-- The second residual applies the same spatial adjoint to the first residual. -/
def tailSecondResidual (N : ℕ) (A α x : ℝ) : ℝ :=
  4*A^2*tailResidual N A α x-densityAdjoint α (tailResidual N A α) x

private theorem adjoint_linear (c α : ℝ) (f g : ℝ→ℝ)
    (hf : Differentiable ℝ f) (hff : Differentiable ℝ (deriv f))
    (hg : Differentiable ℝ g) (hgg : Differentiable ℝ (deriv g)) :
    densityAdjoint α (fun x => c*f x-g x)=
      fun x => c*densityAdjoint α f x-densityAdjoint α g x := by
  have hd : deriv (fun x => c*f x-g x)=fun x => c*deriv f x-deriv g x := by
    ext x
    exact (((hf x).hasDerivAt.const_mul c).sub (hg x).hasDerivAt).deriv
  have hdd : deriv (fun x => c*deriv f x-deriv g x)=
      fun x => c*deriv (deriv f) x-deriv (deriv g) x := by
    ext x
    exact (((hff x).hasDerivAt.const_mul c).sub (hgg x).hasDerivAt).deriv
  ext x
  simp only [densityAdjoint,hd,hdd]
  ring

private theorem residual_expansion {N:ℕ} (hN:1≤N) (A α x:ℝ) :
    tailSecondResidual N A α x=
      16*A^4*tailJet 0 N x-8*A^2*tailJet 2 N x-
        8*A^2*α*(tailJet 0 N x+x*tailJet 1 N x)+
        tailJet 4 N x+2*α*x*tailJet 3 N x+(4*α+α^2*x^2)*tailJet 2 N x+
        3*α^2*x*tailJet 1 N x+α^2*tailJet 0 N x := by
  have hq : originalTail N=tailJet 0 N := by simpa using (tailJet_eq_iterated 0 N hN).symm
  have hdq : Differentiable ℝ (originalTail N) := by
    rw [hq]; exact fun x => (tailJet_deriv 0 N hN x).differentiableAt
  have hddq : Differentiable ℝ (deriv (originalTail N)) := by
    have he : deriv (originalTail N)=tailJet 1 N := by
      ext x; rw [hq]; exact (tailJet_deriv 0 N hN x).deriv
    rw [he]; exact fun x => (tailJet_deriv 1 N hN x).differentiableAt
  have hda : Differentiable ℝ (densityAdjoint α (originalTail N)) :=
    fun x => (adjoint_deriv N hN α x).differentiableAt
  have hdda : Differentiable ℝ (deriv (densityAdjoint α (originalTail N))) :=
    fun x => (adjoint_second_deriv N hN α x).differentiableAt
  have hlin := congrFun (adjoint_linear (4*A^2) α _ _ hdq hddq hda hdda) x
  unfold tailSecondResidual
  change 4*A^2*(4*A^2*originalTail N x-densityAdjoint α (originalTail N) x)-
    densityAdjoint α (fun y => 4*A^2*originalTail N y-densityAdjoint α (originalTail N) y) x=_
  rw [hlin,adjoint_square N hN α x,adjoint_formula N hN α x,hq]
  ring

private theorem second_residual_series {N:ℕ} (hN:1≤N) (A α:ℝ)
    {x:ℝ} (hx:0≤x) :
    HasSum (fun j:ℕ => secondMode A α (N+j+1) x) (tailSecondResidual N A α x) := by
  have h0 := (tailJet_summable_ray 0 N hN hx).hasSum
  have h1 := (tailJet_summable_ray 1 N hN hx).hasSum
  have h2 := (tailJet_summable_ray 2 N hN hx).hasSum
  have h3 := (tailJet_summable_ray 3 N hN hx).hasSum
  have h4 := (tailJet_summable_ray 4 N hN hx).hasSum
  have h := (((((((h0.mul_left (16*A^4)).sub (h2.mul_left (8*A^2))).sub
    ((h0.add (h1.mul_left x)).mul_left (8*A^2*α))).add h4).add
    (h3.mul_left (2*α*x))).add (h2.mul_left (4*α+α^2*x^2))).add
    (h1.mul_left (3*α^2*x))).add (h0.mul_left (α^2))
  rw [residual_expansion hN A α x]
  convert! h using 1
  ext j
  dsimp [secondMode,secondPolynomial,primalJet]
  ring

private theorem summation_integral {f:ℝ→ℝ} {F:ℕ→ℝ→ℝ} {c:ℕ→ℝ}
    (hi:∀ j,IntegrableOn (F j) (Ioi 0))
    (hn:∀ j x,0≤F j x) (hc:Summable c)
    (hb:∀ j,(∫ x in Ioi (0:ℝ),F j x)≤c j)
    (hm:AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hf:∀ x∈Ioi (0:ℝ),‖f x‖≤∑' j,F j x) :
    IntegrableOn f (Ioi 0) ∧ (∫ x in Ioi (0:ℝ), f x)≤∑' j,c j := by
  let μ:=volume.restrict (Ioi (0:ℝ))
  have hs:Summable (fun j => ∫ x,F j x ∂μ) :=
    hc.of_nonneg_of_le (fun j => integral_nonneg (hn j)) hb
  have hns:Summable (fun j => ∫ x,‖F j x‖ ∂μ) := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hn _ _)] using hs
  have hli (j:ℕ) : (∫⁻ x,‖F j x‖ₑ ∂μ)=ENNReal.ofReal (∫ x,‖F j x‖ ∂μ) :=
    (ofReal_integral_norm_eq_lintegral_enorm (hi j)).symm
  have hsi:Integrable (fun x => ∑' j,F j x) μ := by
    refine ⟨AEStronglyMeasurable.tsum (fun j => (hi j).aestronglyMeasurable),?_⟩
    apply hasFiniteIntegral_iff_enorm.mpr
    apply lt_of_le_of_lt (lintegral_mono (fun x => enorm_tsum_le_tsum_enorm (f:=fun j => F j x)))
    rw [lintegral_tsum (fun j => (hi j).aestronglyMeasurable.enorm)]
    dsimp only [μ] at hli
    simp_rw [hli]
    rw [←ENNReal.ofReal_tsum_of_nonneg (fun j => integral_nonneg (fun x => norm_nonneg _)) hns]
    exact ENNReal.ofReal_lt_top
  have hfi:Integrable f μ := hsi.mono' hm (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact hf x hx)
  refine ⟨hfi,?_⟩
  calc
    _ ≤ ∫ x,∑' j,F j x ∂μ := integral_mono_ae hfi hsi (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact (le_abs_self _).trans (hf x hx))
    _ = ∑' j,∫ x,F j x ∂μ := (integral_tsum_of_summable_integral_norm hi hns).symm
    _ ≤ _ := hs.tsum_le_tsum hb hc

private theorem later_power_budget {N:ℕ} (hN:1≤N) (k:ℕ) {C:ℝ}
    (hC:shiftedBudget k-1≤C) :
    (∑' j:ℕ,(modeScale (N+(j+1)+1))^k*exp (-modeScale (N+(j+1)+1))) ≤
      C/(6*modeScale (N+1))*(modeScale (N+1))^k*exp (-modeScale (N+1)) := by
  let A:=modeScale (N+1)
  have hA:0<A := by dsimp [A,modeScale]; positivity
  have hS:0≤shiftedBudget k-1 := by
    have h:1≤shiftedBudget k := by
      simpa [shiftedBudget] using (shifted_summable k).le_tsum 0 (fun j _ => by positivity)
    linarith
  have hg:exp (-2*Real.pi*((N+1:ℕ):ℝ))≤1/(6*A) := by
    apply (scale_gap hN).trans
    apply one_div_le_one_div_of_le (by positivity : 0<6*A)
    nlinarith [Real.pi_gt_three,mul_nonneg hA.le (sub_nonneg.mpr Real.pi_gt_three.le)]
  have h:=mul_le_mul hg hC hS (by positivity : 0≤1/(6*A))
  have h':=mul_le_mul_of_nonneg_left h (show 0≤A^k*exp (-A) by positivity)
  apply (later_mode_sum hN k).trans
  convert! h' using 1 <;> dsimp [A] <;> ring

private theorem residual_budget_256 {N:ℕ} (hN:1≤N) (hA:64≤modeScale (N+1)) :
    (∑' j:ℕ,(230*(modeScale (N+j+1))^2*exp (-modeScale (N+j+1))+
      16*((modeScale (N+j+1))^2-(modeScale (N+1))^2)*modeScale (N+j+1)*
        exp (-modeScale (N+j+1)))) ≤256*(modeScale (N+1))^2*exp (-modeScale (N+1)) := by
  let A:=modeScale (N+1)
  let c:=fun j:ℕ => 230*(modeScale (N+j+1))^2*exp (-modeScale (N+j+1))+
    16*((modeScale (N+j+1))^2-A^2)*modeScale (N+j+1)*exp (-modeScale (N+j+1))
  have hc:Summable c := by
    convert! ((scale_summable N 2).mul_left 230).add
      (((scale_summable N 3).sub ((scale_summable N 1).mul_left (A^2))).mul_left 16) using 1
    ext j; dsimp [c]; ring
  have hlater: (∑' j,c (j+1)) ≤
      230*(∑' j:ℕ,(modeScale (N+(j+1)+1))^2*exp (-modeScale (N+(j+1)+1)))+
      16*(∑' j:ℕ,(modeScale (N+(j+1)+1))^3*exp (-modeScale (N+(j+1)+1))) := by
    have hs2 : Summable (fun j:ℕ => (modeScale (N+(j+1)+1))^2*exp (-modeScale (N+(j+1)+1))) :=
      (scale_summable N 2).comp_injective Nat.succ_injective
    have hs3 : Summable (fun j:ℕ => (modeScale (N+(j+1)+1))^3*exp (-modeScale (N+(j+1)+1))) :=
      (scale_summable N 3).comp_injective Nat.succ_injective
    rw [←tsum_mul_left,←tsum_mul_left,←(hs2.mul_left 230).tsum_add (hs3.mul_left 16)]
    apply (hc.comp_injective Nat.succ_injective).tsum_le_tsum (fun j => ?_)
      ((hs2.mul_left 230).add (hs3.mul_left 16))
    dsimp [c]
    have h:=mul_nonneg (sq_nonneg A) (show 0≤modeScale (N+(j+1)+1)*
      exp (-modeScale (N+(j+1)+1)) by dsimp [modeScale]; positivity)
    nlinarith
  have h2:=later_power_budget hN 2 shifted_explicit.1
  have h3:=later_power_budget hN 3 shifted_explicit.2
  have hsplit:=hc.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one,Nat.add_zero] at hsplit
  have hc0:c 0=230*A^2*exp (-A) := by simp [c,A]
  rw [hc0] at hsplit
  have hA0:0<A := by dsimp [A]; linarith
  have hnum:230*A^2*exp (-A)+230*(2/(6*A)*A^2*exp (-A))+
      16*(9/(6*A)*A^3*exp (-A))≤256*A^2*exp (-A) := by
    have he:230*A^2*exp (-A)+230*(2/(6*A)*A^2*exp (-A))+
        16*(9/(6*A)*A^3*exp (-A))=(254*A^2+(230/3)*A)*exp (-A) := by
      field_simp [hA0.ne']; ring
    rw [he]
    apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
    nlinarith [mul_nonneg hA0.le (show 0≤A-64 by dsimp [A]; linarith)]
  change (∑' j,c j)≤_
  rw [←hsplit]
  dsimp only [A] at hnum
  linarith


private theorem first_residual_64 {N:ℕ} (hN:1≤N) {a α:ℝ}
    (hA:max 64 a≤modeScale (N+1)) (hα:0≤α) (hαa:α≤a) :
    IntegrableOn (fun x:ℝ => exp (a*x^2/2)*|tailResidual N (modeScale (N+1)) α x|) (Ioi 0) ∧
    (∫ x in Ioi (0:ℝ),exp (a*x^2/2)*|tailResidual N (modeScale (N+1)) α x|) ≤
      64*originalFlux N/modeScale (N+1) := by
  let A:=modeScale (N+1)
  let r:=fun j:ℕ => fun x:ℝ => 4*A^2*primalMode (N+j+1) x-primalJet 2 (N+j+1) x-
    α*(primalMode (N+j+1) x+x*primalJet 1 (N+j+1) x)
  let F:=fun j:ℕ => fun x:ℝ => exp (a*x^2/2)*|r j x|
  let c:=fun j:ℕ =>230*(modeScale (N+j+1))^2*exp (-modeScale (N+j+1))+
    16*((modeScale (N+j+1))^2-A^2)*modeScale (N+j+1)*exp (-modeScale (N+j+1))
  have h64:64≤A := (le_max_left 64 a).trans hA
  have haA:a≤A := (le_max_right 64 a).trans hA
  have hscale (j:ℕ):A≤modeScale (N+j+1) := by
    apply mul_le_mul_of_nonneg_left _ pi_pos.le
    exact pow_le_pow_left₀ (Nat.cast_nonneg _)
      (by exact_mod_cast (show N+1≤N+j+1 by omega)) 2
  have hm (j:ℕ) := mode_residual_integral (show 12≤A by linarith) (hscale j)
    (haA.trans (hscale j)) hα (hαa.trans (haA.trans (hscale j)))
  have hc:Summable c := by
    convert! ((scale_summable N 2).mul_left 230).add
      (((scale_summable N 3).sub ((scale_summable N 1).mul_left (A^2))).mul_left 16) using 1
    ext j; dsimp [c]; ring
  have hmeas:AEStronglyMeasurable
      (fun x:ℝ => exp (a*x^2/2)*|tailResidual N A α x|) (volume.restrict (Ioi 0)) := by
    have hq:originalTail N=tailJet 0 N := by simpa using (tailJet_eq_iterated 0 N hN).symm
    dsimp [tailResidual]
    simp_rw [adjoint_formula N hN α,hq]
    have h0:=tailJet_continuous 0 N hN
    have h1:=tailJet_continuous 1 N hN
    have h2:=tailJet_continuous 2 N hN
    fun_prop
  have hbound (x:ℝ) (hx:x∈Ioi (0:ℝ)) :
      ‖exp (a*x^2/2)*|tailResidual N A α x|‖≤∑' j,F j x := by
    have h:=(residual_series hN A α hx.le).mul_left (exp (a*x^2/2))
    have hh:=norm_tsum_le_tsum_norm h.summable.norm
    rw [h.tsum_eq] at hh
    simpa only [tailResidual,F,r,Real.norm_eq_abs,abs_mul,abs_abs,
      abs_of_pos (exp_pos _)] using hh
  have h:=summation_integral (fun j => (hm j).1) (fun j x => by positivity)
    hc (fun j => (hm j).2) hmeas hbound
  refine ⟨h.1,h.2.trans ((residual_budget_256 hN h64).trans ?_)⟩
  have hA0:0<A := by linarith
  have hk:=full_flux_lower hN (show 12≤A by linarith)
  apply (le_div_iff₀ hA0).mpr
  change (11/2)*A^3*exp (-A)≤originalFlux N at hk
  change _*A≤_
  change 256*A^2*exp (-A)*A≤_
  nlinarith only [hk,mul_nonneg (pow_nonneg hA0.le 3) (exp_pos (-A)).le]

-- The finite jet expansion and norm-summable series require a larger elaboration budget.
set_option maxHeartbeats 800000 in
private theorem second_residual_1100 {N:ℕ} (hN:1≤N) {a α:ℝ}
    (hA:max 64 a≤modeScale (N+1)) (hα:0≤α) (hαa:α≤a) :
    IntegrableOn (fun x:ℝ => x^2*exp (a*x^2/2)*
      |tailSecondResidual N (modeScale (N+1)) α x|) (Ioi 0) ∧
    (∫ x in Ioi (0:ℝ),x^2*exp (a*x^2/2)*
      |tailSecondResidual N (modeScale (N+1)) α x|) ≤1100*originalFlux N/modeScale (N+1) := by
  let A:=modeScale (N+1)
  let F:=fun j:ℕ => fun x:ℝ => x^2*exp (a*x^2/2)*|secondMode A α (N+j+1) x|
  let c:=fun j:ℕ => if j=0 then 5100*A^2*exp (-A)
    else 600*(modeScale (N+j+1))^3*exp (-modeScale (N+j+1))
  have h64:64≤A := (le_max_left 64 a).trans hA
  have haA:a≤A := (le_max_right 64 a).trans hA
  have hscale (j:ℕ):A≤modeScale (N+j+1) := by
    apply mul_le_mul_of_nonneg_left _ pi_pos.le
    exact pow_le_pow_left₀ (Nat.cast_nonneg _)
      (by exact_mod_cast (show N+1≤N+j+1 by omega)) 2
  have hfirst:=second_mode_first h64 haA hα (hαa.trans haA)
  have hm (j:ℕ):IntegrableOn (F j) (Ioi 0) ∧ (∫ x in Ioi (0:ℝ),F j x)≤c j := by
    cases j with
    | zero => simpa only [F,c,Nat.add_zero,if_pos rfl,A] using hfirst
    | succ j =>
      have h:=second_mode_later h64 (hscale (j+1)) (haA.trans (hscale (j+1))) hα (hαa.trans haA)
      simpa only [F,c,Nat.succ_eq_add_one,Nat.add_one_ne_zero,if_false] using h
  have hc:Summable c := by
    apply (summable_nat_add_iff 1).mp
    simpa only [c,Nat.add_one_ne_zero,if_false,mul_assoc,Function.comp_def,Nat.succ_eq_add_one] using
      ((scale_summable N 3).comp_injective Nat.succ_injective).mul_left 600
  have hmeas:AEStronglyMeasurable (fun x:ℝ => x^2*exp (a*x^2/2)*
      |tailSecondResidual N A α x|) (volume.restrict (Ioi 0)) := by
    have h0:=tailJet_continuous 0 N hN
    have h1:=tailJet_continuous 1 N hN
    have h2:=tailJet_continuous 2 N hN
    have h3:=tailJet_continuous 3 N hN
    have h4:=tailJet_continuous 4 N hN
    have hc : Continuous (tailSecondResidual N A α) := by
      have h : Continuous (fun x:ℝ =>
          16*A^4*tailJet 0 N x-8*A^2*tailJet 2 N x-
          8*A^2*α*(tailJet 0 N x+x*tailJet 1 N x)+tailJet 4 N x+
          2*α*x*tailJet 3 N x+(4*α+α^2*x^2)*tailJet 2 N x+
          3*α^2*x*tailJet 1 N x+α^2*tailJet 0 N x) := ((((((((h0.const_mul (16*A^4)).sub (h2.const_mul (8*A^2))).sub
        ((h0.add (continuous_id.mul h1)).const_mul (8*A^2*α))).add h4).add
        (((continuous_id.const_mul (2*α)).mul h3))).add
        (((continuous_const.add ((continuous_id.pow 2).const_mul (α^2))).mul h2))).add
        (((continuous_id.const_mul (3*α^2)).mul h1))).add (h0.const_mul (α^2)))
      convert! h using 1
      ext x
      exact residual_expansion hN A α x
    exact (((continuous_id.pow 2).mul (Real.continuous_exp.comp (((continuous_id.pow 2).const_mul a).div_const 2))).mul hc.abs).aestronglyMeasurable
  have hbound (x:ℝ) (hx:x∈Ioi (0:ℝ)) :
      ‖x^2*exp (a*x^2/2)*|tailSecondResidual N A α x|‖≤∑' j,F j x := by
    have h:=(second_residual_series hN A α hx.le).mul_left (x^2*exp (a*x^2/2))
    have hh:=norm_tsum_le_tsum_norm h.summable.norm
    rw [h.tsum_eq] at hh
    simpa only [F,Real.norm_eq_abs,abs_mul,abs_abs,
      abs_of_nonneg (sq_nonneg x),abs_of_pos (exp_pos _)] using hh
  have h:=summation_integral (fun j => (hm j).1) (fun j x => by positivity)
    hc (fun j => (hm j).2) hmeas hbound
  have hsplit:=hc.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one] at hsplit
  have hc0:c 0=5100*A^2*exp (-A) := by simp [c]
  rw [hc0] at hsplit
  have hcs:(∑' j,c (j+1))=600*(∑' j:ℕ,(modeScale (N+(j+1)+1))^3*exp (-modeScale (N+(j+1)+1))) := by
    simp only [c,Nat.add_one_ne_zero,if_false,mul_assoc,tsum_mul_left]
  have hlater:=later_power_budget hN 3 shifted_explicit.2
  have htotal:(∑' j,c j)≤6000*A^2*exp (-A) := by
    rw [←hsplit,hcs]
    have hA0:0<A := by linarith
    have h:=mul_le_mul_of_nonneg_left hlater (show (0:ℝ)≤600 by norm_num)
    have he:5100*A^2*exp (-A)+600*(9/(6*A)*A^3*exp (-A))=6000*A^2*exp (-A) := by
      field_simp [hA0.ne']; ring
    rw [←he]
    exact add_le_add (le_refl _) h
  refine ⟨h.1,h.2.trans (htotal.trans ?_)⟩
  have hA0:0<A := by linarith
  have hk:=full_flux_lower hN (show 12≤A by linarith)
  apply (le_div_iff₀ hA0).mpr
  change (11/2)*A^3*exp (-A)≤originalFlux N at hk
  change 6000*A^2*exp (-A)*A≤_
  nlinarith only [hk,mul_nonneg (pow_nonneg hA0.le 3) (exp_pos (-A)).le]


end D5.S3.Zeros.Jensen.OriginalTailDerivativeVector
