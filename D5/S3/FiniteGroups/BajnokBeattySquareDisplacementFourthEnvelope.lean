/- GID: D5/S3/FiniteGroups/BajnokBeattySquareDisplacementFourthEnvelope
   generality: I
   mirror-B: D5/B/S3/FiniteGroups/BajnokBeattySquareDisplacementFourthEnvelope
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Actual square-displacement quotient counts have a uniform finite fourth-order envelope. -/

import D5.S3.FiniteGroups.BajnokBeattySquareDisplacementThresholdBracket
import D5.S3.FiniteGroups.BajnokBeattySquareDisplacementFourthCoefficient
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace D5.S3.FiniteGroups.BajnokBeattySquareDisplacementFourthEnvelope
open Set Finset
open BajnokBeattySquareDisplacementSingleCrossing
open BajnokBeattyOddWrapPositiveCone BajnokBeattyOddWrapGaussianEnvelope
open BajnokBeattyOddWrapGaussianUpperEnvelope BajnokBeattyOddWrapGaussianSecondOrder

private def C (v : ℝ) : ℝ := 2*(v+1)/(3*(v-1)^2)
private def E (v : ℝ) : ℝ := 4/(3*(v-1)^2)
private def B (v : ℝ) : ℝ := 16*(v^2+v+1)/(15*(v-1)^4)
private def U (v : ℝ) : ℝ := 16*(v+1)/(3*(v-1)^4)
private def V (v : ℝ) : ℝ := 112/(15*(v-1)^4)

/-- A generic AP identity, consumed by both finite log blocks. -/
private theorem sum_fifth (a : ℝ) (r : ℕ) :
    (∑ i ∈ range r, (a+2*(i : ℝ)+1)^5) =
      (((a+2*r)^6-5*(a+2*r)^4+7*(a+2*r)^2)-(a^6-5*a^4+7*a^2))/12 := by
  induction r with
  | zero => simp
  | succ r ih => rw [sum_range_succ,ih]; push_cast; ring

/-- Unlike a positive Taylor estimate, this has no upper bound on u. -/
theorem negative_cubic {u : ℝ} (hu : 0 ≤ u) :
    |Real.exp (-u)-1+u-u^2/2| ≤ u^3/6 := by
  let f : ℝ → ℝ := fun x => (1-x+x^2/2-x^3/6)*Real.exp x
  have hd (x : ℝ) : HasDerivAt f (-(x^3/6)*Real.exp x) x := by
    have hp := (((hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)).add
      (((hasDerivAt_id x).pow 2).div_const 2)).sub
      (((hasDerivAt_id x).pow 3).div_const 6)
    convert hp.mul (Real.hasDerivAt_exp x) using 1 <;>
      (try funext y) <;> dsimp [f] <;> ring
  have hdiff : Differentiable ℝ f := fun x => (hd x).differentiableAt
  have hanti : AntitoneOn f (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
      hdiff.continuous.continuousOn hdiff.differentiableOn
    intro x hx
    have hx0 : 0 ≤ x := interior_subset hx
    rw [(hd x).deriv]
    exact mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (div_nonneg (pow_nonneg hx0 3) (by norm_num)))
      (Real.exp_pos x).le
  have hf : (1-u+u^2/2-u^3/6)*Real.exp u ≤ 1 := by
    simpa [f] using hanti (show (0:ℝ) ∈ Set.Ici (0:ℝ) by simp) hu hu
  have hlo : 1-u+u^2/2-u^3/6 ≤ Real.exp (-u) := by
    rw [Real.exp_neg,inv_eq_one_div]
    exact (le_div_iff₀ (Real.exp_pos u)).2 hf
  have hhi := (abs_le.mp (exp_negative_quadratic_remainder hu)).2
  exact abs_le.mpr ⟨by linarith only [hlo],by nlinarith [pow_nonneg hu 3]⟩

theorem positive_cubic {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    |Real.exp u-1-u-u^2/2| ≤ u^3 := by
  have hlo := Real.quadratic_le_exp_of_nonneg hu
  have hhi := Real.exp_bound' hu hu1 (n := 3) (by norm_num)
  norm_num [sum_range_succ,Nat.factorial] at hhi
  rw [abs_of_nonneg (by linarith only [hlo])]
  nlinarith [pow_nonneg hu 3]

/-- One quartic supplier gives all lower weighted moments without derivatives. -/
theorem weighted_moments {v s : ℝ} (hv : 9 ≤ v) (hs : 2/3 ≤ s)
    (j : ℕ) (hj1 : 1 ≤ j) (hj3 : j ≤ 3) :
    v^j*Real.exp (-v*s) ≤ (9:ℝ)^j/400 := by
  have hv0 : 0 ≤ v := by linarith
  have h4 : v^4*Real.exp (-v*s) < (6561/400:ℝ) := by
    have he : Real.exp (-v*s) ≤ Real.exp (-2*v/3) :=
      Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hv0 (sub_nonneg.mpr hs)])
    exact (mul_le_mul_of_nonneg_left he (pow_nonneg hv0 4)).trans_lt
      (BajnokBeattySquareDisplacementFourthCoefficient.quartic_tail hv)
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤9) hv (4-j)
  have hm := mul_le_mul_of_nonneg_right hp
    (mul_nonneg (pow_nonneg hv0 j) (Real.exp_pos (-v*s)).le)
  have heq : v^(4-j)*(v^j*Real.exp (-v*s)) = v^4*Real.exp (-v*s) := by
    rw [← mul_assoc,← pow_add,Nat.sub_add_cancel (by omega : j ≤ 4)]
  rw [heq] at hm
  interval_cases j <;> norm_num at hm h4 ⊢ <;> linarith only [hm,h4]

/-- Polynomial certificates in v-9; no monotonicity framework is duplicated. -/
theorem rational_coefficients {v : ℝ} (hv : 9 ≤ v) :
    0 ≤ B v ∧ B v ≤ 91/3840 ∧ v^2*B v ≤ 2457/1280 ∧
    0 ≤ U v ∧ U v ≤ 5/384 ∧ v*U v ≤ 15/128 ∧
    0 ≤ V v ∧ V v ≤ 7/3840 := by
  have hv0 : 0 ≤ v := by linarith
  have hm : 0 < v-1 := by linarith
  have h4 : 0 < (v-1)^4 := pow_pos hm 4
  have hz : 0 ≤ v-9 := by linarith
  have hB : 0 ≤ (v-9)*(91*v^3+455*v^2+545*v+445) := by positivity
  have hVB : 0 ≤ (v-9)*(3275*(v-9)^3+84320*(v-9)^2+
      725120*(v-9)+2082816) := by positivity
  have hU : 0 ≤ (v-9)*(5*v^3+25*v^2+255*v+227) := by positivity
  have hVU : 0 ≤ (v-9)*(3*v+5)*(15*v^2+50*v-1) := by
    have : 0 ≤ 15*v^2+50*v-1 := by nlinarith [sq_nonneg (v-9)]
    positivity
  have hV := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤8) (by linarith : 8 ≤ v-1) 4
  refine ⟨by dsimp [B]; positivity,?_,?_,by dsimp [U]; positivity,?_,?_,
    by dsimp [V]; positivity,?_⟩
  · dsimp [B]; apply (div_le_iff₀ (by positivity : 0 < 15*(v-1)^4)).2
    nlinarith only [hB]
  · dsimp [B]; rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < 15*(v-1)^4)).2
    nlinarith only [hVB]
  · dsimp [U]; apply (div_le_iff₀ (by positivity : 0 < 3*(v-1)^4)).2
    nlinarith only [hU]
  · dsimp [U]; rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < 3*(v-1)^4)).2
    nlinarith only [hVU]
  · dsimp [V]; apply (div_le_iff₀ (by positivity : 0 < 15*(v-1)^4)).2
    norm_num at hV; linarith only [hV]

/-- The seventh-power log tail relative to the cubic sum. -/
private theorem log_fifth_tail {z k e : ℝ} (he : 0 ≤ e) (he25 : e ≤ 1/25)
    (hk : 0 ≤ k) (hk25 : k^2 < 25) (hz : 0 ≤ z) (hze : z^2 ≤ k^2*e) :
    0 ≤ Real.log ((1+z)/(1-z))-2*z-(2/3)*z^3-(2/5)*z^5 ∧
    Real.log ((1+z)/(1-z))-2*z-(2/3)*z^3-(2/5)*z^5 ≤
      (3*k^4/(1-k^2/25))*e^2*((2/3)*z^3) := by
  have hz2 : z^2 ≤ k^2/25 := by nlinarith [mul_le_mul_of_nonneg_left he25 (sq_nonneg k)]
  have hz1 : z < 1 := by nlinarith [sq_nonneg (z-1)]
  have hd : 0 < 1-z^2 := by nlinarith
  have hkden : 0 < 1-k^2/25 := by linarith
  have hz4 : z^4 ≤ k^4*e^2 := by
    have h := pow_le_pow_left₀ (sq_nonneg z) hze 2
    convert h using 1 <;> ring
  have htail : 2*z^7/(1-z^2) ≤ (3*k^4/(1-k^2/25))*e^2*((2/3)*z^3) := by
    have hfrac : z^4/(1-z^2) ≤ (k^4*e^2)/(1-k^2/25) := by
      apply (div_le_div_iff₀ hd hkden).2
      have h₁ := mul_le_mul_of_nonneg_right hz4 hkden.le
      have h₂ := mul_le_mul_of_nonneg_left
        (show 1-k^2/25 ≤ 1-z^2 by linarith only [hz2]) (show 0 ≤ k^4*e^2 by positivity)
      exact h₁.trans h₂
    have h := mul_le_mul_of_nonneg_left hfrac (show 0 ≤ 2*z^3 by positivity)
    convert h using 1 <;> field_simp [hd.ne',hkden.ne'] <;> ring
  have hlo := Real.sum_range_le_log_div hz hz1 3
  have hhi := Real.log_div_le_sum_range_add hz hz1 3
  norm_num [sum_range_succ] at hlo hhi
  rw [mul_div_assoc] at htail
  constructor <;> linarith only [hlo,hhi,htail]

theorem coefficient_sizes {v s : ℝ} (hv : 9 ≤ v)
    (hs : 0 ≤ s) (hs7 : s ≤ 5/7) :
    0 ≤ C v*s^3 ∧ C v*s^3 ≤ 1/20 ∧ |B v*s^5-E v*s^3| ≤ 1/50 ∧
    0 ≤ v^2*C v*s^3 ∧ v^2*C v*s^3 ≤ (7/20)*v ∧
    |v^3*B v*s^5-v*E v*s^3| ≤ (2/5)*v := by
  obtain ⟨hC0,hC,hE0,hE,hvC,_⟩ := BajnokBeattySquareDisplacementEnvelope.coefficient_bounds hv
  change 0 ≤ C v at hC0; change C v ≤ 5/48 at hC
  change 0 ≤ E v at hE0; change E v ≤ 1/48 at hE
  change v^2*C v ≤ (15/16)*v at hvC
  obtain ⟨hB0,hB,hvB,_⟩ := rational_coefficients hv
  have hv0 : 0 ≤ v := by linarith
  have hs3 := pow_le_pow_left₀ hs hs7 3
  have hs5 := pow_le_pow_left₀ hs hs7 5
  norm_num at hs3 hs5
  have ha := mul_le_mul hC hs3 (pow_nonneg hs 3) (by norm_num)
  have hb := mul_le_mul hB hs5 (pow_nonneg hs 5) (by norm_num)
  have hc := mul_le_mul hE hs3 (pow_nonneg hs 3) (by norm_num)
  have hA := mul_le_mul hvC hs3 (pow_nonneg hs 3) (by positivity)
  have hB' := mul_le_mul hvB hs5 (pow_nonneg hs 5) (by norm_num)
  have hbv := mul_le_mul_of_nonneg_left hB' hv0
  have hcv := mul_le_mul_of_nonneg_left hc hv0
  refine ⟨by positivity,by linarith only [ha],?_,by positivity,
    by nlinarith only [hA,hv0],?_⟩
  · have hp : 0 ≤ B v*s^5 := by positivity
    have hn : 0 ≤ E v*s^3 := by positivity
    apply abs_le.mpr
    constructor <;> nlinarith only [hb,hc,hp,hn]
  · have hp : 0 ≤ v^3*B v*s^5 := by positivity
    have hn : 0 ≤ v*E v*s^3 := by positivity
    apply abs_le.mpr
    constructor <;> nlinarith only [hbv,hcv,hp,hn,hv0]

/-- A single arithmetic residual estimate is used for x and normalized y. -/
private theorem residual_size {e s u w T k m d : ℝ}
    (he : 0 ≤ e) (he25 : e ≤ 1/25) (hs : 0 ≤ s) (hs7 : s ≤ 5/7)
    (hu : 0 ≤ u) (hum : u ≤ m) (hw : 0 ≤ w) (hw7 : w ≤ 7/3840)
    (hT0 : 0 ≤ T) (hT : T ≤ k*e^3)
    (hnum : m*(5/7:ℝ)^5+(7/3840)*(5/7:ℝ)^5/25+k ≤ d) :
    |-u*s^5*e^3+w*s^5*e^4+T| ≤ d*e^3 := by
  have hs5 := pow_le_pow_left₀ hs hs7 5
  have he4 : e^4 ≤ e^3/25 := by
    have h := mul_le_mul_of_nonneg_left he25 (pow_nonneg he 3)
    nlinarith only [h]
  have h₁ := mul_le_mul hum hs5 (pow_nonneg hs 5) (by nlinarith only [hu,hum])
  have h₂ := mul_le_mul hw7 hs5 (pow_nonneg hs 5) (by norm_num)
  have h₃ := mul_le_mul_of_nonneg_right h₁ (pow_nonneg he 3)
  have h₄ := mul_le_mul h₂ he4 (pow_nonneg he 4) (by positivity)
  have h₅ := mul_le_mul_of_nonneg_right hnum (pow_nonneg he 3)
  have hu0 : 0 ≤ u*s^5*e^3 := by positivity
  have hw0 : 0 ≤ w*s^5*e^4 := by positivity
  apply abs_le.mpr
  constructor <;> nlinarith only [h₃,h₄,h₅,hT0,hT,hu0,hw0,pow_nonneg he 3]

/-- Finite nonlinear inference; dy is deliberately allowed to be arbitrarily large. -/
theorem nonlinear_blocks {e v a b A B rx ry dx dy : ℝ}
    (he : 0 < e) (he25 : e ≤ 1/25) (hv : 9 ≤ v)
    (ha0 : 0 ≤ a) (ha : a ≤ 1/20) (hb : |b| ≤ 1/50)
    (hrx : |rx| ≤ e^3/50) (hA0 : 0 ≤ A) (hA : A ≤ (7/20)*v)
    (hB : |B| ≤ (2/5)*v) (hry : |ry| ≤ 8*v*e^3)
    (hdx0 : 0 ≤ dx) (hdy0 : 0 ≤ dy)
    (hdx : dx = a*e+b*e^2+rx) (hdy : dy = A*e+B*e^2+ry) :
    |Real.exp dx-1-a*e-(b+a^2/2)*e^2| ≤ (141/6250)*e^3 ∧
    |Real.exp (-dy)-1+A*e-(-B+A^2/2)*e^2| ≤
      (8*v+(27/100)*v^2+(4/375)*v^3)*e^3 := by
  have hv0 : 0 ≤ v := by linarith
  have he2 : e^2 ≤ e/25 := by nlinarith [mul_nonneg he.le (sub_nonneg.mpr he25)]
  have he3 : e^3 ≤ e^2/25 := by
    have h := mul_le_mul_of_nonneg_right he25 (sq_nonneg e); nlinarith only [h]
  have hxerr : |dx-a*e| ≤ (13/625)*e^2 := by
    have hh : |dx-a*e| ≤ |b| * e^2+|rx| := by
      rw [hdx,show a*e+b*e^2+rx-a*e = b*e^2+rx by ring]
      exact (abs_add_le _ _).trans_eq (by rw [abs_mul,abs_of_nonneg (sq_nonneg e)])
    have hm := mul_le_mul_of_nonneg_right hb (sq_nonneg e)
    nlinarith only [hh,hm,hrx,he3]
  have hyerr : |dy-A*e| ≤ (18/25)*v*e^2 := by
    have hh : |dy-A*e| ≤ |B| * e^2+|ry| := by
      rw [hdy,show A*e+B*e^2+ry-A*e = B*e^2+ry by ring]
      exact (abs_add_le _ _).trans_eq (by rw [abs_mul,abs_of_nonneg (sq_nonneg e)])
    have hm := mul_le_mul_of_nonneg_right hB (sq_nonneg e)
    have hn := mul_le_mul_of_nonneg_left he3 (show 0 ≤ 8*v by positivity)
    nlinarith only [hh,hm,hry,hn]
  have hae := mul_le_mul_of_nonneg_right ha he.le
  have hAe := mul_le_mul_of_nonneg_right hA he.le
  have hxhi : dx ≤ e/10 := by
    have hh := (abs_le.mp hxerr).2
    nlinarith only [hh,hae,he2,he.le]
  have hyhi : dy ≤ (2/5)*v*e := by
    have hh := (abs_le.mp hyerr).2
    have hm := mul_le_mul_of_nonneg_left he2 (show 0 ≤ (18/25)*v by positivity)
    nlinarith only [hh,hAe,hm,mul_nonneg hv0 he.le]
  have hxsq : |dx^2-(a*e)^2| ≤ (39/12500)*e^3 := by
    rw [show dx^2-(a*e)^2 = (dx-a*e)*(dx+a*e) by ring,abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ dx+a*e)]
    have hh := mul_le_mul hxerr (show dx+a*e ≤ (3/20)*e by linarith only [hxhi,hae])
      (by positivity : 0 ≤ dx+a*e) (by positivity : 0 ≤ (13/625)*e^2)
    convert hh using 1 <;> ring
  have hysq : |dy^2-(A*e)^2| ≤ (27/50)*v^2*e^3 := by
    rw [show dy^2-(A*e)^2 = (dy-A*e)*(dy+A*e) by ring,abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ dy+A*e)]
    have hh := mul_le_mul hyerr (show dy+A*e ≤ (3/4)*v*e by linarith only [hyhi,hAe])
      (by positivity : 0 ≤ dy+A*e) (by positivity : 0 ≤ (18/25)*v*e^2)
    convert hh using 1 <;> ring
  have hx3 : dx^3 ≤ e^3/1000 := by
    have hh := pow_le_pow_left₀ hdx0 hxhi 3
    convert hh using 1 <;> ring
  have hy3 : dy^3/6 ≤ (4/375)*v^3*e^3 := by
    have hh := pow_le_pow_left₀ hdy0 hyhi 3
    nlinarith only [hh]
  have hxr := positive_cubic hdx0 (show dx ≤ 1 by linarith only [hxhi,he25])
  have hyr := negative_cubic hdy0
  have hidX : Real.exp dx-1-a*e-(b+a^2/2)*e^2 =
      (Real.exp dx-1-dx-dx^2/2)+rx+(dx^2-(a*e)^2)/2 := by rw [hdx]; ring
  have hidY : Real.exp (-dy)-1+A*e-(-B+A^2/2)*e^2 =
      (Real.exp (-dy)-1+dy-dy^2/2)-ry+(dy^2-(A*e)^2)/2 := by rw [hdy]; ring
  have h₁ := (abs_add_le _ _).trans (add_le_add
    ((abs_add_le _ _).trans (add_le_add hxr hrx))
    (show |(dx^2-(a*e)^2)/2| ≤ ((39/12500)*e^3)/2 by
      rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]; exact div_le_div_of_nonneg_right hxsq (by norm_num)))
  have h₂ := (abs_add_le _ _).trans (add_le_add
    ((abs_sub _ _).trans (add_le_add hyr hry))
    (show |(dy^2-(A*e)^2)/2| ≤ ((27/50)*v^2*e^3)/2 by
      rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]; exact div_le_div_of_nonneg_right hysq (by norm_num)))
  rw [← hidX] at h₁
  rw [← hidY] at h₂
  constructor <;> nlinarith only [h₁,h₂,hx3,hy3]

private theorem damped_blocks {P v s L M rx ry : ℝ}
    (hP5 : 5 ≤ P) (hv : 9 ≤ v) (hslo : 2/3 ≤ s) (hshi : s ≤ 5/7)
    (hL0 : 0 ≤ L-s) (hM0 : 0 ≤ M-v*s)
    (hL : L-s = (C v*s^3)/P^2+(B v*s^5-E v*s^3)/P^4+rx)
    (hM : M-v*s = (v^2*C v*s^3)/P^2+(v^3*B v*s^5-v*E v*s^3)/P^4+ry)
    (hrx : |rx| ≤ 1/(50*P^6)) (hry : |ry| ≤ 8*v/P^6) :
    |Real.exp L+Real.exp (-M)-(Real.exp s+Real.exp (-v*s))-
      C v*s^3*(Real.exp s-v^2*Real.exp (-v*s))/P^2-
      (-E v*s^3*(Real.exp s-v*Real.exp (-v*s))+
        B v*s^5*(Real.exp s-v^3*Real.exp (-v*s))+
        ((C v)^2/2)*s^6*(Real.exp s+v^4*Real.exp (-v*s)))/P^4| ≤
      2439/(8000*P^6) := by
  let e := 1/P^2
  let a := C v*s^3
  let b := B v*s^5-E v*s^3
  let A := v^2*C v*s^3
  let BB := v^3*B v*s^5-v*E v*s^3
  have hP : 0 < P := by linarith
  have he : 0 < e := by dsimp [e]; positivity
  have he25 : e ≤ 1/25 := by
    apply (div_le_div_iff₀ (by positivity : 0 < P^2) (by norm_num : (0:ℝ)<25)).2
    nlinarith [sq_nonneg (P-5)]
  have he2 : e^2 = 1/P^4 := by dsimp [e]; field_simp [hP.ne'] <;> ring
  have he3 : e^3 = 1/P^6 := by dsimp [e]; field_simp [hP.ne'] <;> ring
  have hs0 : 0 ≤ s := by linarith
  obtain ⟨ha0,ha,hb,hA0,hA,hB⟩ := coefficient_sizes hv hs0 hshi
  have hrx' : |rx| ≤ e^3/50 := by rw [he3]; convert hrx using 1 <;> ring
  have hry' : |ry| ≤ 8*v*e^3 := by rw [he3]; convert hry using 1 <;> ring
  have hL' : L-s = a*e+b*e^2+rx := by
    rw [he2]; convert hL using 1 <;> dsimp [a,b,e] <;> ring
  have hM' : M-v*s = A*e+BB*e^2+ry := by
    rw [he2]; convert hM using 1 <;> dsimp [A,BB,e] <;> ring
  obtain ⟨hx,hy⟩ := nonlinear_blocks he he25 hv ha0 ha hb hrx' hA0 hA hB hry' hL0 hM0 hL' hM'
  have hfactorX : Real.exp L = Real.exp s*Real.exp (L-s) := by rw [← Real.exp_add]; congr 1; ring
  have hfactorY : Real.exp (-M) = Real.exp (-v*s)*Real.exp (-(M-v*s)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hX : |Real.exp L-Real.exp s*(1+a*e+(b+a^2/2)*e^2)| ≤ (1269/25000)*e^3 := by
    have hh := mul_le_mul_of_nonneg_left hx (Real.exp_pos s).le
    have hexp : Real.exp s ≤ 9/4 :=
      (Real.exp_le_exp.mpr (by linarith : s ≤ 3/4)).trans exp_three_quarters_lt.le
    have hm := mul_le_mul_of_nonneg_right hexp (show 0 ≤ (141/6250)*e^3 by positivity)
    rw [hfactorX,← mul_sub,abs_mul,abs_of_pos (Real.exp_pos s)]
    have hid : Real.exp (L-s)-(1+a*e+(b+a^2/2)*e^2) =
        Real.exp (L-s)-1-a*e-(b+a^2/2)*e^2 := by ring
    rw [hid]; nlinarith only [hh,hm]
  have hY : |Real.exp (-M)-Real.exp (-v*s)*(1-A*e+(-BB+A^2/2)*e^2)| ≤
      (50823/200000)*e^3 := by
    have hh := mul_le_mul_of_nonneg_left hy (Real.exp_pos (-v*s)).le
    have h1 := weighted_moments hv hslo 1 (by omega) (by omega)
    have h2 := weighted_moments hv hslo 2 (by omega) (by omega)
    have h3 := weighted_moments hv hslo 3 (by omega) (by omega)
    have ht : Real.exp (-v*s)*(8*v+(27/100)*v^2+(4/375)*v^3) ≤ 50823/200000 := by
      norm_num at h1 h2 h3 ⊢
      nlinarith only [h1,h2,h3]
    have hm := mul_le_mul_of_nonneg_right ht (pow_nonneg he.le 3)
    rw [hfactorY,← mul_sub,abs_mul,abs_of_pos (Real.exp_pos (-v*s))]
    have hid : Real.exp (-(M-v*s))-(1-A*e+(-BB+A^2/2)*e^2) =
        Real.exp (-(M-v*s))-1+A*e-(-BB+A^2/2)*e^2 := by ring
    rw [hid]; nlinarith only [hh,hm]
  have hid : Real.exp L+Real.exp (-M)-(Real.exp s+Real.exp (-v*s))-
      C v*s^3*(Real.exp s-v^2*Real.exp (-v*s))/P^2-
      (-E v*s^3*(Real.exp s-v*Real.exp (-v*s))+B v*s^5*(Real.exp s-v^3*Real.exp (-v*s))+
        ((C v)^2/2)*s^6*(Real.exp s+v^4*Real.exp (-v*s)))/P^4 =
      (Real.exp L-Real.exp s*(1+a*e+(b+a^2/2)*e^2))+
      (Real.exp (-M)-Real.exp (-v*s)*(1-A*e+(-BB+A^2/2)*e^2)) := by
    dsimp [a,b,A,BB,e]; ring
  rw [hid]
  have hh := (abs_add_le _ _).trans (add_le_add hX hY)
  rw [he3] at hh
  convert hh using 1 <;> ring

/-- Shared finite logarithmic data. Both finite envelopes consume this same
product/moment proof; every scalar coefficient is explicit in the interface. -/
theorem finite_log_data (p q n a r : ℕ) (hp5 : 5 ≤ p) (hq3 : 3 ≤ q)
    (hr : 2*r = (q-1)*p) (hna : n+p = 2*a) (hfit : a+(q+1)*r ≤ n) :
    let P : ℝ := p
    let v : ℝ := (q : ℝ)^2
    let s : ℝ := (v-1)*P^2/(2*((n : ℝ)+1))
    let C : ℝ := 2*(v+1)/(3*(v-1)^2)
    let E : ℝ := 4/(3*(v-1)^2)
    let B : ℝ := 16*(v^2+v+1)/(15*(v-1)^4)
    let U : ℝ := 16*(v+1)/(3*(v-1)^4)
    let V : ℝ := 112/(15*(v-1)^4)
    let e : ℝ := 1/P^2
    let k : ℝ := 10*(q : ℝ)/(7*(v-1))
    (2/3 : ℝ) ≤ s → s ≤ 5/7 →
    ∃ L M rx ry Tx : ℝ,
      Real.exp L = (Nat.choose n a : ℝ)/(Nat.choose n (a+r) : ℝ) ∧
      Real.exp (-M) = (Nat.choose n (a+(q+1)*r) : ℝ)/(Nat.choose n (a+r) : ℝ) ∧
      0 ≤ L-s ∧ 0 ≤ M-v*s ∧
      L-s = C*s^3/P^2+(B*s^5-E*s^3)/P^4+rx ∧
      M-v*s = v^2*C*s^3/P^2+(v^3*B*s^5-v*E*s^3)/P^4+ry ∧
      |rx| ≤ 1/(50*P^6) ∧ |ry| ≤ 8*v/P^6 ∧
      rx = -U*s^5*e^3+V*s^5*e^4+Tx ∧ 0 ≤ Tx ∧
      Tx ≤ (3*k^4/(1-k^2/25))*(C*s^3)*e^3 := by
  dsimp only
  let P : ℝ := p
  let Q : ℝ := q
  let R : ℝ := (n : ℝ)+1
  let v := Q^2
  let s := (Q^2-1)*P^2/(2*R)
  let A : ℝ := Nat.choose n a
  let BB : ℝ := Nat.choose n (a+r)
  let D : ℝ := Nat.choose n (a+(q+1)*r)
  intro hslo hshi
  change (2/3:ℝ) ≤ s at hslo
  change s ≤ 5/7 at hshi
  have hP5 : 5 ≤ P := by dsimp only [P]; exact_mod_cast hp5
  have hQ3 : 3 ≤ Q := by dsimp only [Q]; exact_mod_cast hq3
  have hP : 0 < P := by linarith
  have hQ : 0 < Q := by linarith
  have hQsq : 9 ≤ Q^2 := by nlinarith only [hQ3,sq_nonneg (Q-3)]
  have hv : 9 ≤ v := hQsq
  have hQm : 0 < Q^2-1 := by linarith only [hQsq]
  have hR : 0 < R := by dsimp [R]; positivity
  have hrR : (r : ℝ) = (Q-1)*P/2 := by
    have hh : 2*(r : ℝ) = (Q-1)*P := by
      have hc := congrArg (fun j : ℕ => (j : ℝ)) hr
      rw [Nat.cast_mul,Nat.cast_mul,Nat.cast_sub (by omega : 1 ≤ q)] at hc
      norm_num at hc
      exact hc
    linarith only [hh]
  have hnaR : (n : ℝ)+P = 2*(a : ℝ) := by dsimp only [P]; exact_mod_cast hna
  have hqrR : ((q*r : ℕ) : ℝ) = Q*(r : ℝ) := by push_cast; rfl
  have hBR : 2*((a+r : ℕ) : ℝ)-(n : ℝ) = Q*P := by
    push_cast
    nlinarith only [hrR,hnaR]
  have hfitB : a+r ≤ n := by
    have h : r ≤ (q+1)*r := by rw [add_mul,one_mul]; omega
    omega
  have hApos : 0 < A := by dsimp [A]; exact_mod_cast Nat.choose_pos (by omega : a ≤ n)
  have hBBpos : 0 < BB := by dsimp [BB]; exact_mod_cast Nat.choose_pos hfitB
  have hD : 0 < D := by dsimp [D]; exact_mod_cast Nat.choose_pos hfit
  have hsR : 2*s*R = (Q^2-1)*P^2 := by
    dsimp only [s]; field_simp [hR.ne'] <;> ring
  have hbandR : 7*(Q^2-1)*P^2 ≤ 10*R := by
    have hh := mul_le_mul_of_nonneg_right hshi hR.le
    nlinarith only [hsR,hh]
  have hqratio : 8*Q ≤ 3*(Q^2-1) := by
    have hh := mul_nonneg (show 0 ≤ Q-3 by linarith) (show 0 ≤ 3*Q+1 by linarith)
    nlinarith only [hh]
  have hq2ratio : 8*Q^2 ≤ 9*(Q^2-1) := by linarith only [hQsq]
  let x (i : ℕ) : ℝ := (P+2*(i : ℝ)+1)/R
  let y (i : ℕ) : ℝ := (Q*P+2*(i : ℝ)+1)/R
  have hxP (i : ℕ) (hi : i ∈ range r) : x i ≤ (15/28)/P := by
    have hiR : (i : ℝ)+1 ≤ (r : ℝ) := by exact_mod_cast Nat.succ_le_of_lt (mem_range.mp hi)
    have hnum : P+2*(i : ℝ)+1 ≤ Q*P := by nlinarith only [hiR,hrR]
    have hh := mul_le_mul_of_nonneg_right hqratio (pow_nonneg hP.le 2)
    have hm := mul_le_mul_of_nonneg_right hnum (show 0 ≤ 28*P by positivity)
    dsimp only [x]
    apply (div_le_div_iff₀ hR hP).2
    nlinarith only [hh,hm,hbandR]
  have hyP (i : ℕ) (hi : i ∈ range (q*r)) : y i ≤ (45/28)/P := by
    have hiR : (i : ℝ)+1 ≤ Q*(r : ℝ) := by
      rw [← hqrR]; exact_mod_cast Nat.succ_le_of_lt (mem_range.mp hi)
    have hnum : Q*P+2*(i : ℝ)+1 ≤ Q^2*P := by
      have hh := congrArg (fun z : ℝ => Q*z) hrR
      nlinarith only [hiR,hh]
    have hh := mul_le_mul_of_nonneg_right hq2ratio (pow_nonneg hP.le 2)
    have hm := mul_le_mul_of_nonneg_right hnum (show 0 ≤ 28*P by positivity)
    dsimp only [y]
    apply (div_le_div_iff₀ hR hP).2
    nlinarith only [hh,hm,hbandR]
  have hx (i : ℕ) (hi : i ∈ range r) : 0 ≤ x i ∧ x i < 1 := by
    have hsmall : (15/28 : ℝ)/P ≤ 3/28 := by
      apply (div_le_iff₀ hP).2; linarith only [hP5]
    exact ⟨by dsimp [x]; positivity, lt_of_le_of_lt ((hxP i hi).trans hsmall) (by norm_num)⟩
  have hy (i : ℕ) (hi : i ∈ range (q*r)) : 0 ≤ y i ∧ y i < 1 := by
    have hsmall : (45/28 : ℝ)/P ≤ 9/28 := by
      apply (div_le_iff₀ hP).2; linarith only [hP5]
    exact ⟨by dsimp [y]; positivity, lt_of_le_of_lt ((hyP i hi).trans hsmall) (by norm_num)⟩
  let e := 1/P^2
  have he : 0 < e := by dsimp [e]; positivity
  have he25 : e ≤ 1/25 := by
    apply (div_le_div_iff₀ (by positivity : 0 < P^2) (by norm_num : (0:ℝ)<25)).2
    nlinarith [sq_nonneg (P-5)]
  have he2 : e^2 = 1/P^4 := by dsimp [e]; field_simp [hP.ne'] <;> ring
  have he3 : e^3 = 1/P^6 := by dsimp [e]; field_simp [hP.ne'] <;> ring
  have he4 : e^4 = 1/P^8 := by dsimp [e]; field_simp [hP.ne'] <;> ring
  have hvm : 0 < v-1 := hQm
  let k : ℝ := 10*Q/(7*(v-1))
  have hk0 : 0 ≤ k := by dsimp [k]; positivity
  have hkcap : k ≤ 15/28 := by
    apply (div_le_iff₀ (show 0 < 7*(v-1) by positivity)).2
    change 10*Q ≤ (15/28)*(7*(Q^2-1))
    linarith only [hqratio]
  have hk25 : k^2 < 25 := by
    have hh := pow_le_pow_left₀ hk0 hkcap 2
    norm_num at hh
    linarith only [hh]
  have hxPk (i : ℕ) (hi : i ∈ range r) : x i ≤ k/P := by
    have hiR : (i : ℝ)+1 ≤ (r : ℝ) := by exact_mod_cast Nat.succ_le_of_lt (mem_range.mp hi)
    have hnum : P+2*(i : ℝ)+1 ≤ Q*P := by nlinarith only [hiR,hrR]
    have hmul := mul_le_mul_of_nonneg_right hnum hP.le
    have hmain : 7*(v-1)*P^2 ≤ 10*R := hbandR
    have hqmul := mul_le_mul_of_nonneg_right hmain hQ.le
    have hprod := mul_le_mul_of_nonneg_right hmul (show 0 ≤ 7*(v-1) by positivity)
    dsimp only [x]
    apply (div_le_div_iff₀ hR hP).2
    have hkeq : k*(7*(v-1)) = 10*Q := by dsimp [k]; field_simp [hvm.ne'] <;> ring
    have hh : ((P+2*(i : ℝ)+1)*P)*(7*(v-1)) ≤ 10*Q*R := by
      nlinarith only [hprod,hqmul]
    have hright : (k*R)*(7*(v-1)) = 10*Q*R := by rw [mul_right_comm,hkeq]
    rw [← hright] at hh
    exact (mul_le_mul_iff_left₀ (show 0 < 7*(v-1) by positivity)).mp hh
  let kx : ℝ := 3*k^4/(1-k^2/25)
  let ky : ℝ := 3*(45/28)^4/(1-(45/28)^2/25)
  have hkden : 0 < 1-k^2/25 := by linarith only [hk25]
  have hkx : 0 ≤ kx := by dsimp [kx]; positivity
  have hkxcap : kx ≤ 3*(15/28)^4/(1-(15/28)^2/25) := by
    have h2 := pow_le_pow_left₀ hk0 hkcap 2
    have h4 := pow_le_pow_left₀ hk0 hkcap 4
    dsimp only [kx]
    apply (div_le_div_iff₀ hkden (by norm_num : (0:ℝ)<1-(15/28)^2/25)).2
    norm_num at h2 h4 ⊢
    nlinarith only [h2,h4]
  have hky : 0 ≤ ky := by norm_num [ky]
  have hxrem (i : ℕ) (hi : i ∈ range r) :
      0 ≤ Real.log ((1+x i)/(1-x i))-2*x i-(2/3)*(x i)^3-(2/5)*(x i)^5 ∧
      Real.log ((1+x i)/(1-x i))-2*x i-(2/3)*(x i)^3-(2/5)*(x i)^5 ≤
        kx*e^2*((2/3)*(x i)^3) := by
    have hz2 := pow_le_pow_left₀ (hx i hi).1 (hxPk i hi) 2
    have hh : (x i)^2 ≤ k^2*e := by
      convert hz2 using 1 <;> dsimp [e] <;> field_simp [hP.ne'] <;> ring
    exact log_fifth_tail he.le he25 hk0 hk25 (hx i hi).1 hh
  have hyrem (i : ℕ) (hi : i ∈ range (q*r)) :
      0 ≤ Real.log ((1+y i)/(1-y i))-2*y i-(2/3)*(y i)^3-(2/5)*(y i)^5 ∧
      Real.log ((1+y i)/(1-y i))-2*y i-(2/3)*(y i)^3-(2/5)*(y i)^5 ≤
        ky*e^2*((2/3)*(y i)^3) := by
    have hz2 := pow_le_pow_left₀ (hy i hi).1 (hyP i hi) 2
    have hh : (y i)^2 ≤ (45/28)^2*e := by
      convert hz2 using 1 <;> dsimp [e] <;> field_simp [hP.ne'] <;> ring
    exact log_fifth_tail he.le he25 (by norm_num : (0:ℝ)≤45/28)
      (by norm_num : (45/28:ℝ)^2<25) (hy i hi).1 hh
  have hxp (i : ℕ) (hi : i ∈ range r) : 0 < (1+x i)/(1-x i) :=
    div_pos (by linarith [(hx i hi).1]) (by linarith [(hx i hi).2])
  have hyp (i : ℕ) (hi : i ∈ range (q*r)) : 0 < (1+y i)/(1-y i) :=
    div_pos (by linarith [(hy i hi).1]) (by linarith [(hy i hi).2])
  have hAB : A/BB = ∏ i ∈ range r, (1+x i)/(1-x i) :=
    choose_ratio_centered_prod n a r P R hfitB rfl (by linarith only [hnaR])
  have hBD : BB/D = ∏ i ∈ range (q*r), (1+y i)/(1-y i) := by
    have hh := choose_ratio_centered_prod n (a+r) (q*r) (Q*P) R
      (by convert hfit using 1 <;> ring) rfl hBR.symm
    simpa only [show a+r+q*r = a+(q+1)*r by ring] using hh
  have hxsum : 2*(∑ i ∈ range r, x i) = s := by
    dsimp [x]; rw [← sum_div,sum_linear,hrR]
    dsimp [s]; field_simp [hR.ne'] <;> ring
  have hysum : 2*(∑ i ∈ range (q*r), y i) = v*s := by
    dsimp [y]; rw [← sum_div,sum_linear,hqrR,hrR]
    dsimp [s,v]; field_simp [hR.ne'] <;> ring
  let Sx := (2/3)*(∑ i ∈ range r, (x i)^3)
  let Sy := (2/3)*(∑ i ∈ range (q*r), (y i)^3)
  have hSx : Sx = C v*s^3/P^2-E v*s^3/P^4 := by
    dsimp [Sx,x]; simp_rw [div_pow]; rw [← sum_div,sum_cubic,hrR]
    dsimp [C,E,v,s]; field_simp [hR.ne',hP.ne',hQm.ne'] <;> ring
  have hSy : Sy = v^2*C v*s^3/P^2-v*E v*s^3/P^4 := by
    dsimp [Sy,y]; simp_rw [div_pow]; rw [← sum_div,sum_cubic,hqrR,hrR]
    dsimp [C,E,v,s]; field_simp [hR.ne',hP.ne',hQm.ne'] <;> ring
  let Fx := (2/5)*(∑ i ∈ range r, (x i)^5)
  let Fy := (2/5)*(∑ i ∈ range (q*r), (y i)^5)
  have hFx : Fx = B v*s^5/P^4-U v*s^5/P^6+V v*s^5/P^8 := by
    dsimp [Fx,x]; simp_rw [div_pow]; rw [← sum_div,sum_fifth,hrR]
    dsimp [B,U,V,v,s]; field_simp [hR.ne',hP.ne',hQm.ne'] <;> ring
  have hFy : Fy = v^3*B v*s^5/P^4-v^2*U v*s^5/P^6+v*V v*s^5/P^8 := by
    dsimp [Fy,y]; simp_rw [div_pow]; rw [← sum_div,sum_fifth,hqrR,hrR]
    dsimp [B,U,V,v,s]; field_simp [hR.ne',hP.ne',hQm.ne'] <;> ring
  let L := Real.log (A/BB)
  let M := Real.log (BB/D)
  have hlogL : L = ∑ i ∈ range r, Real.log ((1+x i)/(1-x i)) := by
    dsimp [L]; rw [hAB,Real.log_prod (fun i hi => (hxp i hi).ne')]
  have hlogM : M = ∑ i ∈ range (q*r), Real.log ((1+y i)/(1-y i)) := by
    dsimp [M]; rw [hBD,Real.log_prod (fun i hi => (hyp i hi).ne')]
  let Tx := ∑ i ∈ range r,
    (Real.log ((1+x i)/(1-x i))-2*x i-(2/3)*(x i)^3-(2/5)*(x i)^5)
  let Ty := ∑ i ∈ range (q*r),
    (Real.log ((1+y i)/(1-y i))-2*y i-(2/3)*(y i)^3-(2/5)*(y i)^5)
  have hTx0 : 0 ≤ Tx := sum_nonneg (fun i hi => (hxrem i hi).1)
  have hTy0 : 0 ≤ Ty := sum_nonneg (fun i hi => (hyrem i hi).1)
  have hTx : Tx ≤ kx*e^2*Sx := by
    calc
      _ ≤ ∑ i ∈ range r, kx*e^2*((2/3)*(x i)^3) := sum_le_sum (fun i hi => (hxrem i hi).2)
      _ = _ := by rw [← mul_sum,← mul_sum]
  have hTy : Ty ≤ ky*e^2*Sy := by
    calc
      _ ≤ ∑ i ∈ range (q*r), ky*e^2*((2/3)*(y i)^3) := sum_le_sum (fun i hi => (hyrem i hi).2)
      _ = _ := by rw [← mul_sum,← mul_sum]
  have hs0 : 0 ≤ s := by linarith
  have hv0 : 0 < v := by linarith
  have hE0 : 0 ≤ E v := by dsimp [E]; positivity
  obtain ⟨ha0,ha,hb,hA0,hA,hby⟩ := coefficient_sizes hv hs0 hshi
  have hSxle : Sx ≤ C v*s^3*e := by
    calc
      Sx = C v*s^3/P^2-E v*s^3/P^4 := hSx
      _ ≤ C v*s^3/P^2 := sub_le_self _ (by positivity)
      _ = C v*s^3*e := by dsimp only [e]; ring
  have hSyle : Sy ≤ v^2*C v*s^3*e := by
    calc
      Sy = v^2*C v*s^3/P^2-v*E v*s^3/P^4 := hSy
      _ ≤ v^2*C v*s^3/P^2 := sub_le_self _ (by positivity)
      _ = v^2*C v*s^3*e := by dsimp only [e]; ring
  have hTxscaled : Tx ≤ kx*(C v*s^3)*e^3 := by
    have hh := mul_le_mul_of_nonneg_left hSxle (show 0 ≤ kx*e^2 by positivity)
    nlinarith only [hTx,hh]
  have hTxb : Tx ≤ ((3*(15/28)^4/(1-(15/28)^2/25))/20)*e^3 := by
    have h₁ := mul_le_mul_of_nonneg_left hSxle (show 0 ≤ kx*e^2 by positivity)
    have h₂ := mul_le_mul_of_nonneg_right ha (show 0 ≤ kx*e^3 by positivity)
    have h₃ := mul_le_mul_of_nonneg_right hkxcap (show 0 ≤ e^3/20 by positivity)
    nlinarith only [hTx,h₁,h₂,h₃]
  have hTyb : Ty/v ≤ (ky*(7/20))*e^3 := by
    apply (div_le_iff₀ hv0).2
    have h₁ := mul_le_mul_of_nonneg_left hSyle (show 0 ≤ ky*e^2 by positivity)
    have h₂ := mul_le_mul_of_nonneg_right hA (show 0 ≤ ky*e^3 by positivity)
    calc
      Ty ≤ ky*e^2*Sy := hTy
      _ ≤ ky*e^2*(v^2*C v*s^3*e) := h₁
      _ = (v^2*C v*s^3)*(ky*e^3) := by ring
      _ ≤ ((7/20)*v)*(ky*e^3) := h₂
      _ = (ky*(7/20))*e^3*v := by ring
  obtain ⟨hB0,hBmax,hvB,hU0,hUmax,hvU,hV0,hVmax⟩ := rational_coefficients hv
  let rx := -U v*s^5*e^3+V v*s^5*e^4+Tx
  let ry := -v^2*U v*s^5*e^3+v*V v*s^5*e^4+Ty
  have hrx : |rx| ≤ e^3/50 := by
    have hh := residual_size he.le he25 hs0 hshi hU0 hUmax hV0 hVmax hTx0 hTxb
      (by norm_num : (5/384:ℝ)*(5/7)^5+(7/3840)*(5/7)^5/25+
        (3*(15/28)^4/(1-(15/28)^2/25))/20 ≤ 1/50)
    convert hh using 1 <;> ring
  have hry : |ry| ≤ 8*v*e^3 := by
    have hh := residual_size he.le he25 hs0 hshi (mul_nonneg hv0.le hU0) hvU
      hV0 hVmax (div_nonneg hTy0 hv0.le) hTyb
      (by norm_num [ky] : (15/128:ℝ)*(5/7)^5+(7/3840)*(5/7)^5/25+ky*(7/20) ≤ 8)
    have hid : ry = v*(-(v*U v)*s^5*e^3+V v*s^5*e^4+Ty/v) := by
      dsimp [ry]; field_simp [hv0.ne'] <;> ring
    rw [hid,abs_mul,abs_of_pos hv0]
    have hm := mul_le_mul_of_nonneg_left hh hv0.le
    nlinarith only [hm]
  have hLexact : L-s = C v*s^3/P^2+(B v*s^5-E v*s^3)/P^4+rx := by
    have hid : Tx = L-2*(∑ i ∈ range r, x i)-Sx-Fx := by
      dsimp [Tx,Sx,Fx]
      rw [sum_sub_distrib,sum_sub_distrib,sum_sub_distrib,← mul_sum,← mul_sum,← mul_sum,← hlogL]
    rw [hxsum,hSx,hFx] at hid
    dsimp [rx]; rw [he3,he4,hid] <;> ring
  have hMexact : M-v*s = v^2*C v*s^3/P^2+(v^3*B v*s^5-v*E v*s^3)/P^4+ry := by
    have hid : Ty = M-2*(∑ i ∈ range (q*r), y i)-Sy-Fy := by
      dsimp [Ty,Sy,Fy]
      rw [sum_sub_distrib,sum_sub_distrib,sum_sub_distrib,← mul_sum,← mul_sum,← mul_sum,← hlogM]
    rw [hysum,hSy,hFy] at hid
    dsimp [ry]; rw [he3,he4,hid] <;> ring
  have hL0 : 0 ≤ L-s := by
    have hh := sum_le_sum (fun i hi => Real.sum_range_le_log_div (hx i hi).1 (hx i hi).2 1)
    norm_num [sum_range_succ] at hh
    rw [← mul_sum,← hlogL] at hh; linarith only [hh,hxsum]
  have hM0 : 0 ≤ M-v*s := by
    have hh := sum_le_sum (fun i hi => Real.sum_range_le_log_div (hy i hi).1 (hy i hi).2 1)
    norm_num [sum_range_succ] at hh
    rw [← mul_sum,← hlogM] at hh; linarith only [hh,hysum]
  have hrx' : |rx| ≤ 1/(50*P^6) := by rw [he3] at hrx; convert hrx using 1 <;> ring
  have hry' : |ry| ≤ 8*v/P^6 := by rw [he3] at hry; convert hry using 1 <;> ring
  have hexpL : Real.exp L = A/BB := Real.exp_log (div_pos hApos hBBpos)
  have hexpM : Real.exp (-M) = D/BB := by
    dsimp [M]; rw [Real.exp_neg,Real.exp_log (div_pos hBBpos hD),inv_div]
  exact ⟨L,M,rx,ry,Tx,hexpL,hexpM,hL0,hM0,hLexact,hMexact,hrx',hry',rfl,hTx0,hTxscaled⟩

/-- The higher finite inference over natural binomial indices; parity enters only
at the final signed actual-count bridge. -/
private theorem finite_binomial (p q n a r : ℕ) (hp5 : 5 ≤ p) (hq3 : 3 ≤ q)
    (hr : 2*r = (q-1)*p) (hna : n+p = 2*a) (hfit : a+(q+1)*r ≤ n) :
    let s : ℝ := (((q : ℝ)^2-1)*(p : ℝ)^2)/(2*((n : ℝ)+1))
    let v : ℝ := (q : ℝ)^2
    (2/3 : ℝ) ≤ s → s ≤ 5/7 →
    |((Nat.choose n a : ℝ)+Nat.choose n (a+(q+1)*r))/(Nat.choose n (a+r) : ℝ)-
      (Real.exp s+Real.exp (-v*s))-C v*s^3*(Real.exp s-v^2*Real.exp (-v*s))/(p : ℝ)^2-
      (-E v*s^3*(Real.exp s-v*Real.exp (-v*s))+B v*s^5*(Real.exp s-v^3*Real.exp (-v*s))+
        ((C v)^2/2)*s^6*(Real.exp s+v^4*Real.exp (-v*s)))/(p : ℝ)^4| ≤
      2439/(8000*(p : ℝ)^6) := by
  dsimp only
  intro hslo hshi
  obtain ⟨L,M,rx,ry,Tx,hexpL,hexpM,hL0,hM0,hL,hM,hrx,hry,_,_,_⟩ :=
    finite_log_data p q n a r hp5 hq3 hr hna hfit hslo hshi
  have hP5 : (5:ℝ) ≤ (p : ℝ) := by exact_mod_cast hp5
  have hv : (9:ℝ) ≤ (q : ℝ)^2 := by
    have hq : (3:ℝ) ≤ (q : ℝ) := by exact_mod_cast hq3
    nlinarith only [hq,sq_nonneg ((q : ℝ)-3)]
  have hh := damped_blocks hP5 hv hslo hshi hL0 hM0 hL hM hrx hry
  rw [hexpL,hexpM,← add_div] at hh
  exact hh

/-- Uniform fourth-order control of the actual complete lattice quotient counts,
for the full signed odd domain, including odd composite p and q. -/
theorem actual_square_displacement_fourth_envelope (p q : ℤ) (t : ℕ)
    (hp5 : 5 ≤ p) (hpo : Odd p) (hq3 : 3 ≤ q) (hqo : Odd q)
    (ht : ((q+1)/2).toNat ≤ t) :
    let nReal : ℝ := (p : ℝ)*(2*(q : ℝ)*(t : ℝ)-1)
    let s : ℝ := (((q : ℝ)^2-1)*(p : ℝ)^2)/(2*(nReal+1))
    let nu : ℝ := (q : ℝ)^2
    let C : ℝ := 2*(nu+1)/(3*(nu-1)^2)
    let E : ℝ := 4/(3*(nu-1)^2)
    let Bcoef : ℝ := 16*(nu^2+nu+1)/(15*(nu-1)^4)
    let G : ℝ := Real.exp s+Real.exp (-nu*s)
    let H : ℝ := C*s^3*(Real.exp s-nu^2*Real.exp (-nu*s))
    let K : ℝ := -E*s^3*(Real.exp s-nu*Real.exp (-nu*s))+
      Bcoef*s^5*(Real.exp s-nu^3*Real.exp (-nu*s))+
      (C^2/2)*s^6*(Real.exp s+nu^4*Real.exp (-nu*s))
    (2/3 : ℝ) ≤ s → s ≤ 5/7 →
      |2*((square_return_pair p q t).1 : ℝ)/((square_return_pair p q t).2 : ℝ)-
        G-H/(p : ℝ)^2-K/(p : ℝ)^4| ≤ 2439/(8000*(p : ℝ)^6) := by
  obtain ⟨n,a,r,hN,hna,hr,hfit,hWa,hWq⟩ :=
    BajnokBeattySquareDisplacementThresholdBracket.state_data p q t hp5 hpo hq3 hqo ht
  have hPn : (p.toNat : ℝ) = (p : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (show 0 ≤ p by omega)
  have hQn : (q.toNat : ℝ) = (q : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (show 0 ≤ q by omega)
  have hNR : (n : ℝ) = (p : ℝ)*(2*(q : ℝ)*(t : ℝ)-1) := by exact_mod_cast hN
  have hBr : a+r ≤ n := by
    have h : r ≤ (q.toNat+1)*r := by rw [add_mul,one_mul]; omega
    omega
  have hBpos : (0:ℝ) < (Nat.choose n (a+r) : ℝ) := by exact_mod_cast Nat.choose_pos hBr
  have hratio : 2*((square_return_pair p q t).1 : ℝ)/((square_return_pair p q t).2 : ℝ) =
      ((Nat.choose n a : ℝ)+Nat.choose n (a+(q.toNat+1)*r))/(Nat.choose n (a+r) : ℝ) := by
    rw [hWa,hWq]; push_cast; field_simp [hBpos.ne'] <;> ring
  have hh := finite_binomial p.toNat q.toNat n a r (by omega) (by omega) hr hna hfit
  dsimp only at hh ⊢
  rw [hPn,hQn,hNR] at hh
  rw [hratio]
  simpa only [C,E,B] using hh

end D5.S3.FiniteGroups.BajnokBeattySquareDisplacementFourthEnvelope
