/- GID: D5/S3/Quantum/Analysis/RefinedBMVPositiveCenterLeftStripWeightedTail
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Smallness of the cancelled BMV tail after geometric normalization. -/

import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterLeftStripTail
import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterLeftStripRadical

open Filter
open scoped Topology

noncomputable section

namespace RefinedBMV.PositiveCenter

/-- The tail contribution to the normalized lower-collision profile. -/
def leftStripTailTerm (p : ℕ) (a v : ℝ) : ℝ :=
  leftStripWeight (3/(p : ℝ)) a v * leftStripTailResidual p a v

private theorem weighted_mixed_formula {A : ℝ → ℝ → ℝ} {h a v γ : ℝ}
    (hh : 0 < h) (hv : 0 < v) (hav : a < v) (hA : ContDiff ℝ 3 (Function.uncurry A)) :
    let W := leftStripWeight h
    let P (x y : ℝ) := deriv (A · y) x
    let Q (x y : ℝ) := deriv (P · y) x
    let s := v-a
    let L := profileSlope h s
    let q := profileCurvature h s
    let q₁ := -q*(h+2*upperTailSlope h s)
    let M := Q a v-2*L*P a v+(L^2+q)*A a v
    let M₁ := deriv (Q a) v-2*q*P a v-2*L*deriv (P a) v+
      (2*L*q+q₁)*A a v+(L^2+q)*deriv (A a) v
    deriv (fun y ↦ deriv (deriv (fun x ↦ W x y*A x y)) a) v -
      γ*deriv (deriv (fun x ↦ W x v*A x v)) a =
      W a v*((profileSlope h v+L-γ)*M+M₁) := by
  let W := leftStripWeight h
  let P (x y : ℝ) := deriv (A · y) x
  let Q (x y : ℝ) := deriv (P · y) x
  let L := profileSlope h
  let q := profileCurvature h
  let M (x y : ℝ) := Q x y-2*L (y-x)*P x y+(L (y-x)^2+q (y-x))*A x y
  have hP : ContDiff ℝ 2 (Function.uncurry P) := contDiff_partialLeft hA (by decide) (by norm_num)
  have hQ : ContDiff ℝ 1 (Function.uncurry Q) := contDiff_partialLeft hP (by decide) (by norm_num)
  have hLeft {f : ℝ → ℝ → ℝ} {n : WithTop ℕ∞} (hf : ContDiff ℝ n (Function.uncurry f))
      (hn : n ≠ 0) (x y : ℝ) : HasDerivAt (f · y) (deriv (f · y) x) x :=
    ((hf.comp (contDiff_id.prodMk contDiff_const :
      ContDiff ℝ n (fun t : ℝ ↦ (t,y)))).differentiable hn x).hasDerivAt
  have hRight {f : ℝ → ℝ → ℝ} {n : WithTop ℕ∞} (hf : ContDiff ℝ n (Function.uncurry f))
      (hn : n ≠ 0) (x y : ℝ) : HasDerivAt (f x) (deriv (f x) y) y :=
    ((hf.comp (contDiff_const.prodMk contDiff_id :
      ContDiff ℝ n (fun t : ℝ ↦ (x,t)))).differentiable hn y).hasDerivAt
  have hfirst (x y : ℝ) (hxy : x < y) :
      deriv (fun t ↦ W t y*A t y) x = W x y*(P x y-L (y-x)*A x y) := by
    have hd := (hasDerivAt_leftStripWeight_left hh hxy).mul (hLeft hA (by decide) x y)
    change HasDerivAt (fun t ↦ W t y*A t y) _ x at hd
    rw [hd.deriv]
    dsimp only [W, L, P]
    ring
  have hsecond (x y : ℝ) (hxy : x < y) :
      deriv (deriv (fun t ↦ W t y*A t y)) x = W x y*M x y := by
    have heq : deriv (fun t ↦ W t y*A t y) =ᶠ[𝓝 x]
        fun t ↦ W t y*(P t y-L (y-t)*A t y) := by
      filter_upwards [eventually_lt_nhds hxy] with t ht using hfirst t y ht
    have hL := (hasDerivAt_profileSlope hh (sub_pos.mpr hxy)).comp x
      ((hasDerivAt_id' x).const_sub y)
    have hd := (hasDerivAt_leftStripWeight_left hh hxy).mul
      ((hLeft hP (by decide) x y).sub (hL.mul (hLeft hA (by decide) x y)))
    change HasDerivAt (fun t ↦ W t y*(P t y-L (y-t)*A t y)) _ x at hd
    rw [heq.deriv_eq, hd.deriv]
    dsimp only [W, M, P, Q, L, q]
    simp only [Pi.sub_apply, Pi.mul_apply, Function.comp_apply]
    ring
  have heq : (fun y ↦ deriv (deriv (fun x ↦ W x y*A x y)) a) =ᶠ[𝓝 v]
      fun y ↦ W a y*M a y := by
    filter_upwards [eventually_gt_nhds hav] with y hy using hsecond a y hy
  have hshift := (hasDerivAt_id' v).sub_const a
  have hL := (hasDerivAt_profileSlope hh (sub_pos.mpr hav)).comp v hshift
  have hq := (hasDerivAt_profileCurvature hh (sub_pos.mpr hav)).comp v hshift
  have hm := ((hRight hQ (by decide) a v).sub
    ((hL.const_mul 2).mul (hRight hP (by decide) a v))).add
      (((hL.pow 2).add hq).mul (hRight hA (by decide) a v))
  change HasDerivAt (M a) _ v at hm
  have hd := (hasDerivAt_leftStripWeight_right hh hv hav).mul hm
  change HasDerivAt (fun y ↦ W a y*M a y) _ v at hd
  dsimp only
  rw [heq.deriv_eq, hd.deriv, hsecond a v hav]
  dsimp [W, M, P, Q, L, q]
  ring

/-- The cancelled tail consumes less than (2/25) of the geometric margin. -/
theorem leftStrip_tail_mixed_lt {p : ℕ} (hp : 11 ≤ p) {a v γ : ℝ}
    (ha : 0 ≤ a) (hamax : a ≤ 1/2) (hgap : 6 ≤ v-a) (hγ : 0 ≤ γ) (hγmax : γ ≤ 1) :
    |deriv (fun y ↦ deriv (deriv (leftStripTailTerm p · y)) a) v -
      γ*deriv (deriv (leftStripTailTerm p · v)) a| < 2/25 := by
  let h := 3/(p : ℝ)
  let s := v-a
  let U := upperTailRepeatCorrection h s
  let B := ((3+h)*(3+2*h)/2) * (upperTailGap h s)^2 * Real.exp (-(2*s))
  let A := leftStripTailResidual p
  let P (x y : ℝ) := deriv (A · y) x
  let Q (x y : ℝ) := deriv (P · y) x
  let L := profileSlope h s
  let q := profileCurvature h s
  let q₁ := -q*(h+2*upperTailSlope h s)
  let W := leftStripWeight h a v
  let M := Q a v-2*L*P a v+(L^2+q)*A a v
  let M₁ := deriv (Q a) v-2*q*P a v-2*L*deriv (P a) v+
    (2*L*q+q₁)*A a v+(L^2+q)*deriv (A a) v
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hh : 0 < h := by dsimp [h]; positivity
  have hhmax : h ≤ 3/11 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by exact_mod_cast hp)
  have hsv : s ≤ v := sub_le_self v ha
  have hv : 0 < v := by linarith
  have hav : a < v := by linarith
  have hU : 0 ≤ U := by
    have hF : 0 ≤ upperTailGap h s := by
      unfold upperTailGap
      exact div_nonneg
        (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hh.le (by linarith))))) hh.le
    unfold U upperTailRepeatCorrection
    positivity
  have ha₂ : a^2 ≤ 1/4 := (pow_le_pow_left₀ ha hamax 2).trans_eq (by norm_num)
  obtain ⟨hAv,hPav,hRv,hSv⟩ := leftStripTailResidual_cancellation_bounds hp ha hgap
  obtain ⟨hQav,hTv⟩ := leftStripTailResidual_derivative_bounds hp ha hgap
  have hA₁ : |A a v| ≤ 3*U := by
    change |A a v| ≤ 12*U*a^2 at hAv
    nlinarith only [hAv, mul_le_mul_of_nonneg_left ha₂ (by positivity : 0 ≤ 12*U)]
  have hP₁ : |P a v| ≤ 6*U := by
    change |P a v| ≤ 12*U*a at hPav
    nlinarith only [hPav, mul_le_mul_of_nonneg_left hamax (by positivity : 0 ≤ 12*U)]
  have hR₁ : |deriv (A a) v| ≤ 10*U := by
    change |deriv (A a) v| ≤ 40*U*a^2 at hRv
    nlinarith only [hRv, mul_le_mul_of_nonneg_left ha₂ (by positivity : 0 ≤ 40*U)]
  have hA := leftStripTailResidual_smooth p
  have hA₂ : ContDiffAt ℝ 2 (Function.uncurry A) (a,v) := (hA.of_le (by decide)).contDiffAt
  have hS₁ : |deriv (P a) v| ≤ 20*U := by
    change |deriv (fun x ↦ deriv (A x) v) a| ≤ 40*U*a at hSv
    rw [mixed_partial_eq hA₂] at hSv
    change |deriv (P a) v| ≤ 40*U*a at hSv
    nlinarith only [hSv, mul_le_mul_of_nonneg_left hamax (by positivity : 0 ≤ 40*U)]
  change |Q a v| ≤ 12*U at hQav
  change |deriv (Q a) v| ≤ 40*U at hTv
  obtain ⟨hL₀,hLmax,hLlo,hLhi,hq₀,hqhi⟩ := leftStrip_slope_bounds hh hgap
  obtain ⟨_,_,hVlo,hVhi,_,_⟩ := leftStrip_slope_bounds hh (hgap.trans hsv)
  change 5/6 ≤ L at hLlo
  change L ≤ 1 at hLhi
  have hL : |L| ≤ 1 := abs_le.mpr ⟨by linarith,hLhi⟩
  have hq : |q| ≤ 1/36 := (abs_of_nonneg hq₀).trans_le hqhi
  have hq₁ : |q₁| ≤ 1/50 := by
    change |(-q)*(h+2*upperTailSlope h s)| ≤ _
    rw [abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ h+2*upperTailSlope h s)]
    have htop : h+2*upperTailSlope h s ≤ 3/11+1/3 := by linarith
    exact (mul_le_mul hq htop (by positivity) (by norm_num)).trans (by norm_num)
  have hC : |profileSlope h v+L-γ| ≤ 2 := abs_le.mpr ⟨by linarith,by linarith⟩
  have h2 : |(2 : ℝ)| ≤ 2 := by norm_num
  have hLq : |L^2+q| ≤ 37/36 :=
    (abs_add_bound (abs_sq_bound hL) hq).trans (by norm_num)
  have hLq₁ : |2*L*q+q₁| ≤ 1/10 :=
    (abs_add_bound (abs_mul_bound (abs_mul_bound h2 hL) hq) hq₁).trans (by norm_num)
  have hM : |M| ≤ 28*U := by
    unfold M
    exact (abs_add_bound (abs_sub_bound hQav (abs_mul_bound (abs_mul_bound h2 hL) hP₁))
      (abs_mul_bound hLq hA₁)).trans (by linarith only [hU])
  have hM₁ : |M₁| ≤ 92*U := by
    unfold M₁
    exact (abs_add_bound (abs_add_bound
      (abs_sub_bound (abs_sub_bound hTv (abs_mul_bound (abs_mul_bound h2 hq) hP₁))
        (abs_mul_bound (abs_mul_bound h2 hL) hS₁))
      (abs_mul_bound hLq₁ hA₁)) (abs_mul_bound hLq hR₁)).trans (by linarith only [hU])
  have hW : 0 ≤ W := by unfold W leftStripWeight; positivity
  have hWB : W*B ≤ 5/3 := leftStrip_weight_mul_square_le hh ha hamax hgap
  have hUB : U ≤ B/3400 := (separated_marginal_correction_lt hh hgap).le
  change |deriv (fun y ↦ deriv (deriv (fun x ↦ leftStripWeight h x y*A x y)) a) v -
    γ*deriv (deriv (fun x ↦ leftStripWeight h x v*A x v)) a| < _
  rw [weighted_mixed_formula hh hv hav hA]
  change |W*((profileSlope h v+L-γ)*M+M₁)| < _
  calc
    _ ≤ W*(2*(28*U)+92*U) :=
      abs_mul_bound (abs_of_nonneg hW).le (abs_add_bound (abs_mul_bound hC hM) hM₁)
    _ = 148*W*U := by ring
    _ ≤ 148*(5/3)/3400 := by
      have hprod := mul_le_mul_of_nonneg_left hUB hW
      nlinarith only [hprod,hWB]
    _ < _ := by norm_num

private def tailExponent (p i : ℕ) : ℝ := ((p : ℝ)+1-i)*(3/(p : ℝ))

private def tailPJet (p n : ℕ) (a : ℝ) : ℝ :=
  let h := 3/(p : ℝ)
  let k := 3+2*h
  let c := (3+h)*k/2
  (h/c)*(((p+1 : ℝ)/2)*(k^n*Real.exp (k*a) + (if n = 0 then 1 else 0)) -
    ∑ i ∈ Finset.range (p+1), (tailExponent p i)^n*Real.exp (tailExponent p i*a))

private def tailQ (p : ℕ) (a : ℝ) : ℝ :=
  let h := 3/(p : ℝ)
  let g := 3+h
  let k := 3+2*h
  let c := g*k/2
  (1-((p : ℝ)+2)*Real.exp (g*a)+((p : ℝ)+1)*Real.exp (k*a))/(2*c)

private theorem tail_eq_split {p : ℕ} (hp : 0 < p) {a v : ℝ} (ha : 0 < a)
    (hd : 0 < v-a) (hv : 0 < v) :
    let h := 3/(p : ℝ)
    let c := (3+h)*(3+2*h)/2
    leftStripTailTerm p a v =
      (leftStripWeight h a v * (c*Real.exp (-((3+h)*v)))) *
        (upperTailGap h v * tailPJet p 0 a - tailQ p a) := by
  let h := 3/(p : ℝ)
  let g := 3+h
  let k := 3+2*h
  let c := g*k/2
  let d := v-a
  let F := upperTailGap h
  let S := ∑ i ∈ Finset.range (p+1), Real.exp (tailExponent p i*a)
  let E := Real.exp (-(g*v))
  let A := Real.exp (g*a)
  let B := Real.exp (k*a)
  let X := Real.exp (-(h*a))
  let V := Real.exp (-(h*v))
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hh : 0 < h := by dsimp [h]; positivity
  have hph : (p : ℝ)*h = 3 := by dsimp [h]; field_simp
  have hgh : ((p : ℝ)+1)*h = g := by dsimp only [g]; linarith only [hph]
  have hkh : ((p : ℝ)+2)*h = k := by dsimp only [k]; linarith only [hph]
  have hc : 0 < c := by dsimp [c, g, k]; positivity
  have hFa := tail_gap_pos hh ha
  have hBA : B*X = A := by
    dsimp only [B, X, A, k, g]; rw [← Real.exp_add]; congr 1; ring
  have hds : Real.exp (-(g*d)) = E*A := by
    dsimp only [d, E, A]; rw [← Real.exp_add]; congr 1; ring
  have hdX : Real.exp (-(h*d))*X = V := by
    dsimp only [d, X, V]; rw [← Real.exp_add]; congr 1; ring
  have hX0 : 0 < X := Real.exp_pos _
  have hFD : F d * X = F v - F a := by
    have hd' := tail_gap_factor (t := d) hh
    have hv' := tail_gap_factor (t := v) hh
    have ha' := tail_gap_factor (t := a) hh
    apply mul_left_cancel₀ hh.ne'
    change h*(F d*X) = h*(F v-F a)
    linear_combination -X*hd' + hv' - ha' - hdX
  have hFv : 1-V = h*F v := tail_gap_factor hh
  have hFx : 1-X = h*F a := tail_gap_factor hh
  have hS : (1-X)*S = A-1 := by
    have hsum : S = ∑ i ∈ Finset.range (p+1), Real.exp (h*a)^i * Real.exp (h*a) := by
      dsimp only [S]
      rw [← Finset.sum_range_reflect (fun i ↦ Real.exp (tailExponent p i*a)) (p+1)]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i < p+1 := Finset.mem_range.mp hi
      rw [← pow_succ, ← Real.exp_nat_mul]
      congr 1
      unfold tailExponent
      change (((p : ℝ)+1-(↑(p+1-1-i) : ℝ))*h)*a = _
      rw [show p+1-1-i = p-i by omega, Nat.cast_sub (by omega : i ≤ p)]
      push_cast
      ring
    have hplus : Real.exp (h*a)*X = 1 := by
      dsimp [X]; rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have hpow : Real.exp (h*a)^(p+1) = A := by
      rw [← Real.exp_nat_mul]; dsimp only [A]; push_cast; congr 1
      linear_combination a*hgh
    have hgeom := geom_sum_mul_neg (Real.exp (h*a)) (p+1)
    rw [hpow] at hgeom
    rw [hsum, ← Finset.sum_mul]
    linear_combination -hgeom - (∑ i ∈ Finset.range (p+1), Real.exp (h*a)^i)*hplus
  have hC : leftStripCross p a v = E*(1+(1-V)*S) := by
    rw [leftStripCross_eq hp ha]
    unfold upperTailCrossCorrection
    change Real.exp (-(g*d))*(Real.exp (-(h*d)) + F d*(1-Real.exp (-(k*a)))/F a) = _
    rw [hds, show Real.exp (-(k*a)) = B⁻¹ by simp [B, Real.exp_neg]]
    have hB₀ : 0 < B := Real.exp_pos _
    have hquot : (1-B⁻¹)/F a = h*(B+S)/B := by
      apply (div_eq_div_iff hFa.ne' hB₀.ne').mpr
      rw [sub_mul, one_mul, inv_mul_cancel₀ hB₀.ne']
      linear_combination hBA - hS + (B+S)*hFx
    rw [mul_div_assoc, hquot]
    have hAdiv : A/B = X := (div_eq_iff hB₀.ne').mpr (by linarith [hBA])
    have hAterm : A*Real.exp (-(h*d)) = B*V := by
      linear_combination -Real.exp (-(h*d))*hBA + B*hdX
    have hf : X*(h*F d) = X-V := by
      linear_combination -X*tail_gap_factor (t := d) hh - hdX
    calc
      E*A*(Real.exp (-(h*d)) + F d*(h*(B+S)/B)) =
          E*(A*Real.exp (-(h*d))+(A/B)*(h*F d)*(B+S)) := by ring
      _ = E*(1+(1-V)*S) := by
        rw [hAdiv, hAterm, hf]
        linear_combination E*hBA - E*hS
  rw [leftStripTailTerm, leftStripTailResidual, hC]
  change leftStripWeight h a v *
    (((1+g*F v)*E+(1+g*F d)*Real.exp (-(g*d)))/2 - E*(1+(1-V)*S)) = _
  rw [hds, hFv]
  unfold tailPJet tailQ
  simp only [pow_zero, one_mul, ite_true]
  change _ = (leftStripWeight h a v*(c*E))*
    (F v*(h/c*(((p+1 : ℝ)/2)*(B+1)-S)) - (1-((p : ℝ)+2)*A+((p : ℝ)+1)*B)/(2*c))
  have hdA : F d*A = (F v-F a)*B := by
    linear_combination -F d*hBA+B*hFD
  have hga : g*F a*B = ((p : ℝ)+1)*(B-A) := by
    linear_combination -((p : ℝ)+1)*hBA - ((p : ℝ)+1)*B*hFx - F a*B*hgh
  have hpoly : (1+g*F v)+(1+g*F d)*A-2*(1+h*F v*S) =
      h*F v*(((p+1 : ℝ))*(B+1)-2*S) - (1-((p : ℝ)+2)*A+((p : ℝ)+1)*B) := by
    linear_combination g*hdA - hga - F v*(1+B)*hgh
  calc
    _ = leftStripWeight h a v*E/2*
        ((1+g*F v)+(1+g*F d)*A-2*(1+h*F v*S)) := by ring
    _ = _ := by rw [hpoly]; field_simp [hc.ne']

private theorem hasDerivAt_tailPJet (p n : ℕ) (a : ℝ) :
    HasDerivAt (tailPJet p n) (tailPJet p (n+1) a) a := by
  let h := 3/(p : ℝ)
  let k := 3+2*h
  let c := (3+h)*k/2
  have expJet (r : ℝ) : HasDerivAt (fun t ↦ r^n*Real.exp (r*t))
      (r^(n+1)*Real.exp (r*a)) a := by
    have hd := ((((hasDerivAt_id' a).const_mul r).exp).const_mul (r^n))
    apply hd.congr_deriv
    simp only [mul_one, pow_succ]
    ring
  have hs := HasDerivAt.fun_sum (u := Finset.range (p+1)) (fun i _ ↦ expJet (tailExponent p i))
  have hd := (((expJet k).add_const (if n = 0 then 1 else 0)).const_mul
    ((p+1 : ℝ)/2)).sub hs |>.const_mul (h/c)
  change HasDerivAt (tailPJet p n) _ a at hd
  simpa only [tailPJet, Nat.succ_ne_zero, ite_false, add_zero, h, k, c] using hd

private theorem tail_exponent_sum {p : ℕ} (hp : 0 < p) :
    ∑ i ∈ Finset.range (p+1), tailExponent p i = ((p+1 : ℝ)/2)*(3+2*(3/(p : ℝ))) := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hsum := congrArg (fun n : ℕ ↦ (n : ℝ)) (Finset.sum_range_id_mul_two (p+1))
  change (((∑ i ∈ Finset.range (p+1), i)*2 : ℕ) : ℝ) =
    (((p+1)*(p+1-1) : ℕ) : ℝ) at hsum
  rw [show p+1-1 = p by omega] at hsum
  push_cast at hsum
  unfold tailExponent
  rw [← Finset.sum_mul, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  have hs : (∑ i ∈ Finset.range (p+1), (i : ℝ)) = ((p : ℝ)+1)*p/2 := by
    linarith only [hsum]
  rw [hs]
  field_simp [hpR.ne']
  <;> ring

private theorem tailPJet_nonneg {p n : ℕ} (hp : 0 < p) (hn : n ≠ 0) {a : ℝ}
    (ha : 0 ≤ a) : 0 ≤ tailPJet p n a := by
  let h := 3/(p : ℝ)
  let k := 3+2*h
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hh : 0 < h := by dsimp [h]; positivity
  have hph : (p : ℝ)*h = 3 := by dsimp [h]; field_simp
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hcompare (i : ℕ) (hi : i ∈ Finset.range (p+1)) :
      (tailExponent p i)^(m+1)*Real.exp (tailExponent p i*a) ≤
        tailExponent p i*(k^m*Real.exp (k*a)) := by
    have hip : (i : ℝ) ≤ p := by exact_mod_cast (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
    let r := tailExponent p i
    have hr : 0 ≤ r := mul_nonneg (by linarith) hh.le
    have hrk : r ≤ k := by
      change ((p : ℝ)+1-i)*h ≤ 3+2*h
      nlinarith only [hph, hh, mul_nonneg (Nat.cast_nonneg i) hh.le]
    have h := mul_le_mul (pow_le_pow_left₀ hr hrk m)
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hrk ha)) (Real.exp_pos _).le
      (pow_nonneg (hr.trans hrk) m)
    rw [pow_succ]
    nlinarith only [mul_le_mul_of_nonneg_left h hr]
  have hs := Finset.sum_le_sum hcompare
  rw [← Finset.sum_mul, tail_exponent_sum hp] at hs
  dsimp only [tailPJet]
  simp only [Nat.succ_ne_zero, ite_false, add_zero]
  apply mul_nonneg (by positivity)
  change 0 ≤ ((p+1 : ℝ)/2)*(k^(m+1)*Real.exp (k*a)) -
    ∑ i ∈ Finset.range (p+1), (tailExponent p i)^(m+1)*Real.exp (tailExponent p i*a)
  rw [pow_succ]
  dsimp only [k, h] at *
  nlinarith only [hs]

private theorem monotoneOn_Icc_of_hasDerivAt_nonneg {f f' : ℝ → ℝ} {a b : ℝ}
    (hd : ∀ x ∈ Set.Icc a b, HasDerivAt f (f' x) x)
    (hs : ∀ x ∈ Set.Icc a b, 0 ≤ f' x) :
    MonotoneOn f (Set.Icc a b) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
    (fun x hx ↦ (hd x hx).continuousAt.continuousWithinAt)
  · intro x hx
    rw [interior_Icc] at hx
    exact (hd x ⟨hx.1.le, hx.2.le⟩).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    exact hs x ⟨hx.1.le, hx.2.le⟩

private theorem tailP_bounds {p : ℕ} (hp : 0 < p) {a : ℝ} (ha : 0 ≤ a) :
    0 ≤ tailPJet p 0 a ∧ 0 ≤ tailPJet p 1 a ∧ 0 ≤ tailPJet p 2 a ∧
      tailPJet p 1 a ≤ a*tailPJet p 2 a := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hzero : tailPJet p 0 0 = 0 := by
    unfold tailPJet
    simp only [mul_zero, Real.exp_zero, pow_zero, one_mul, ite_true, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  have hfirst : tailPJet p 1 0 = 0 := by
    unfold tailPJet
    simp only [mul_zero, Real.exp_zero, pow_one, mul_one, Nat.one_ne_zero, ite_false, add_zero]
    rw [tail_exponent_sum hp, sub_self, mul_zero]
  have hmono (n : ℕ) : MonotoneOn (tailPJet p n) (Set.Icc 0 a) :=
    monotoneOn_Icc_of_hasDerivAt_nonneg (fun x _ ↦ hasDerivAt_tailPJet p n x)
      (fun x hx ↦ tailPJet_nonneg hp (by omega) hx.1)
  have h₀ := hmono 0 ⟨le_rfl, ha⟩ ⟨ha, le_rfl⟩ ha
  rw [hzero] at h₀
  have h₁ := tailPJet_nonneg hp (n := 1) (by decide) ha
  have h₂ := tailPJet_nonneg hp (n := 2) (by decide) ha
  refine ⟨h₀, h₁, h₂, ?_⟩
  have hdiff (x : ℝ) : HasDerivAt (fun t ↦ t*tailPJet p 2 a-tailPJet p 1 t)
      (tailPJet p 2 a-tailPJet p 2 x) x := by
    have hd := ((hasDerivAt_id' x).mul_const (tailPJet p 2 a)).sub (hasDerivAt_tailPJet p 1 x)
    change HasDerivAt (fun t ↦ t*tailPJet p 2 a-tailPJet p 1 t) _ x at hd
    simpa only [one_mul] using hd
  have hmono' := monotoneOn_Icc_of_hasDerivAt_nonneg
    (b := a) (fun x _ ↦ hdiff x)
    (fun x (hx : x ∈ Set.Icc 0 a) ↦ sub_nonneg.mpr (hmono 2 hx ⟨ha, le_rfl⟩ hx.2))
  have h := hmono' ⟨le_rfl, ha⟩ ⟨ha, le_rfl⟩ ha
  simpa only [zero_mul, hfirst, sub_zero, sub_nonneg] using h

private def tailQFirst (p : ℕ) (a : ℝ) : ℝ :=
  let h := 3/(p : ℝ)
  Real.exp ((3+2*h)*a)*upperTailGap h a

private def tailQSecond (p : ℕ) (a : ℝ) : ℝ :=
  let h := 3/(p : ℝ)
  Real.exp ((3+2*h)*a)*(1+(3+h)*upperTailGap h a)

private theorem hasDerivAt_tailQ {p : ℕ} (hp : 0 < p) (a : ℝ) :
    HasDerivAt (tailQ p) (tailQFirst p a) a := by
  let h := 3/(p : ℝ)
  let g := 3+h
  let k := 3+2*h
  let c := g*k/2
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hh : 0 < h := by dsimp [h]; positivity
  have hg : 0 < g := by dsimp [g]; positivity
  have hk : 0 < k := by dsimp [k]; positivity
  have hph : (p : ℝ)*h = 3 := by dsimp [h]; field_simp
  have hgh : ((p : ℝ)+1)*h = g := by dsimp only [g]; linarith only [hph]
  have hkh : ((p : ℝ)+2)*h = k := by dsimp only [k]; linarith only [hph]
  have hd := ((((hasDerivAt_id' a).const_mul g).exp.const_mul ((p : ℝ)+2)).const_sub 1).add
    (((hasDerivAt_id' a).const_mul k).exp.const_mul ((p : ℝ)+1)) |>.div_const (2*c)
  change HasDerivAt (tailQ p) _ a at hd
  apply hd.congr_deriv
  simp only [mul_one]
  change _ = Real.exp (k*a)*((1-Real.exp (-(h*a)))/h)
  have he : Real.exp (k*a)*Real.exp (-(h*a)) = Real.exp (g*a) := by
    dsimp only [k, g]; rw [← Real.exp_add]; congr 1; ring
  have hE : Real.exp (k*a)*((1-Real.exp (-(h*a)))/h) =
      (Real.exp (k*a)-Real.exp (g*a))/h := by
    rw [← mul_div_assoc (Real.exp (k*a)) (1-Real.exp (-(h*a))) h, mul_sub, mul_one, he]
  rw [hE, show 2*c = g*k by dsimp [c]; ring]
  apply (div_eq_div_iff (mul_ne_zero hg.ne' hk.ne') hh.ne').mpr
  linear_combination (k*Real.exp (k*a))*hgh-(g*Real.exp (g*a))*hkh

private theorem hasDerivAt_tailQFirst {p : ℕ} (hp : 0 < p) (a : ℝ) :
    HasDerivAt (tailQFirst p) (tailQSecond p a) a := by
  let h := 3/(p : ℝ)
  let k := 3+2*h
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hh : 0 < h := by dsimp [h]; positivity
  have hd := (((hasDerivAt_id' a).const_mul k).exp).mul (hasDerivAt_upperTailGap hh)
  change HasDerivAt (tailQFirst p) _ a at hd
  apply hd.congr_deriv
  change Real.exp (k*a)*(k*1)*upperTailGap h a+Real.exp (k*a)*Real.exp (-(h*a)) =
    Real.exp (k*a)*(1+(3+h)*upperTailGap h a)
  dsimp only [k]
  linear_combination -Real.exp ((3+2*h)*a)*tail_gap_factor (t := a) hh

private theorem tailQ_bounds {p : ℕ} (hp : 0 < p) {a : ℝ} (ha : 0 ≤ a) :
    0 ≤ tailQ p a ∧ 0 ≤ tailQFirst p a ∧ 0 ≤ tailQSecond p a ∧
      tailQ p a ≤ (a^2/2)*tailQSecond p a := by
  let h := 3/(p : ℝ)
  let F := upperTailGap h
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hh : 0 < h := by dsimp [h]; positivity
  have hg : 0 ≤ 3+h := by positivity
  have hk : 0 ≤ 3+2*h := by positivity
  have hF₀ : F 0 = 0 := by simp [F, upperTailGap]
  have hFmono : Monotone F := monotone_of_hasDerivAt_nonneg
    (fun t ↦ hasDerivAt_upperTailGap (t := t) hh) (fun _ ↦ (Real.exp_pos _).le)
  have hF {t : ℝ} (ht : 0 ≤ t) : 0 ≤ F t := hF₀ ▸ hFmono ht
  have hq0 : tailQ p 0 = 0 := by
    unfold tailQ
    simp only [mul_zero, Real.exp_zero, mul_one]
    rw [show (1 : ℝ)-((p : ℝ)+2)+((p : ℝ)+1) = 0 by ring, zero_div]
  have hq1 : tailQFirst p 0 = 0 := by
    change Real.exp ((3+2*h)*0)*F 0 = 0
    rw [hF₀, mul_zero]
  have hqpos {t : ℝ} (ht : 0 ≤ t) : 0 ≤ tailQFirst p t :=
    mul_nonneg (Real.exp_pos _).le (hF ht)
  have hq₂ : 0 ≤ tailQSecond p a := by
    change 0 ≤ Real.exp ((3+2*h)*a)*(1+(3+h)*F a)
    have h := hF ha
    positivity
  have hQmono := monotoneOn_Icc_of_hasDerivAt_nonneg
    (b := a) (fun t _ ↦ hasDerivAt_tailQ hp t) (fun t ht ↦ hqpos ht.1)
  have hQa := hQmono ⟨le_rfl, ha⟩ ⟨ha, le_rfl⟩ ha
  rw [hq0] at hQa
  have hmon₂ (t : ℝ) (ht₀ : 0 ≤ t) (ht : t ≤ a) :
      tailQSecond p t ≤ tailQSecond p a := by
    change Real.exp ((3+2*h)*t)*(1+(3+h)*F t) ≤
      Real.exp ((3+2*h)*a)*(1+(3+h)*F a)
    have hf₀ := hF ht₀
    exact mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht hk))
      (add_le_add_right (mul_le_mul_of_nonneg_left (hFmono ht) hg) 1)
      (by positivity) (Real.exp_pos _).le
  have hq₁bound (t : ℝ) (ht : t ∈ Set.Icc 0 a) : tailQFirst p t ≤ t*tailQSecond p a := by
    have hd (x : ℝ) : HasDerivAt (fun z ↦ z*tailQSecond p a-tailQFirst p z)
        (tailQSecond p a-tailQSecond p x) x := by
      have hd := ((hasDerivAt_id' x).mul_const (tailQSecond p a)).sub (hasDerivAt_tailQFirst hp x)
      change HasDerivAt (fun z ↦ z*tailQSecond p a-tailQFirst p z) _ x at hd
      simpa only [one_mul] using hd
    have hm := monotoneOn_Icc_of_hasDerivAt_nonneg
      (b := a) (fun x _ ↦ hd x) (fun x hx ↦ sub_nonneg.mpr (hmon₂ x hx.1 hx.2))
    have h := hm ⟨le_rfl, ha⟩ ht ht.1
    simpa only [zero_mul, hq1, sub_zero, sub_nonneg] using h
  have hd (x : ℝ) : HasDerivAt (fun t ↦ (t^2/2)*tailQSecond p a-tailQ p t)
      (x*tailQSecond p a-tailQFirst p x) x := by
    have hd := (((hasDerivAt_pow 2 x).div_const 2).mul_const (tailQSecond p a)).sub
      (hasDerivAt_tailQ hp x)
    convert hd using 1 <;> simp <;> ring
  have hm := monotoneOn_Icc_of_hasDerivAt_nonneg
    (b := a) (fun x _ ↦ hd x) (fun x hx ↦ sub_nonneg.mpr (hq₁bound x hx))
  refine ⟨hQa, hqpos ha, hq₂, ?_⟩
  have hm' := hm ⟨le_rfl, ha⟩ ⟨ha, le_rfl⟩ ha
  simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), zero_div, zero_mul, hq0, sub_zero,
    sub_nonneg] using hm'

set_option maxRecDepth 4096 in
private theorem tail_split_weighted_formula {p : ℕ} (hp : 0 < p) {a v γ : ℝ}
    (ha : 0 < a) (hav : a < v) :
    let h := 3/(p : ℝ)
    let d := v-a
    let E := leftStripWeight h a v *
      (((3+h)*(3+2*h)/2)*Real.exp (-((3+h)*v)))
    let F := upperTailGap h v
    let L := profileSlope h d
    let q := profileCurvature h d
    let H₀ := L^2+q
    let C₀ := q*(4*L-2-h)
    let β := 1+h+upperTailSlope h d+upperTailSlope h v+γ
    let r := 1+h+upperTailSlope h d+γ
    let P := tailPJet p 0 a
    let P₁ := tailPJet p 1 a
    let P₂ := tailPJet p 2 a
    let Q := tailQ p a
    let Q₁ := tailQFirst p a
    let Q₂ := tailQSecond p a
    deriv (fun y ↦ deriv (deriv (leftStripTailTerm p · y)) a) v -
      γ*deriv (deriv (leftStripTailTerm p · v)) a =
      E*(F*(-r*(P₂-2*L*P₁)-2*q*P₁+(-r*H₀+C₀)*P) +
        β*(Q₂+H₀*Q) - (2*β*L-2*q)*Q₁ - C₀*Q) := by
  let h := 3/(p : ℝ)
  let c := (3+h)*(3+2*h)/2
  let F := upperTailGap h
  let L := profileSlope h
  let q := profileCurvature h
  let E (x y : ℝ) := leftStripWeight h x y*(c*Real.exp (-((3+h)*y)))
  let U (x y : ℝ) := F y*tailPJet p 0 x-tailQ p x
  let U₁ (x y : ℝ) := F y*tailPJet p 1 x-tailQFirst p x
  let U₂ (x y : ℝ) := F y*tailPJet p 2 x-tailQSecond p x
  let M (x y : ℝ) := U₂ x y-2*L (y-x)*U₁ x y+(L (y-x)^2+q (y-x))*U x y
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hh : 0 < h := by dsimp [h]; positivity
  have hv := ha.trans hav
  have hEl {x y : ℝ} (hxy : x < y) :
      HasDerivAt (E · y) (-E x y*L (y-x)) x := by
    have hd := (hasDerivAt_leftStripWeight_left hh hxy).mul_const (c*Real.exp (-((3+h)*y)))
    exact hd.congr_deriv (by dsimp only [E, L]; ring)
  have hEr : HasDerivAt (E a) ((L v+L (v-a)-(3+h))*E a v) v := by
    have hdec := (((hasDerivAt_id' v).const_mul (3+h)).neg.exp).const_mul c
    have hd := (hasDerivAt_leftStripWeight_right hh hv hav).mul hdec
    change HasDerivAt (E a) _ v at hd
    apply hd.congr_deriv
    simp only [E, L, Pi.neg_apply, mul_one, mul_neg, neg_mul]
    ring
  have hUl (x y : ℝ) : HasDerivAt (U · y) (U₁ x y) x := by
    have hd := ((hasDerivAt_tailPJet p 0 x).const_mul (F y)).sub (hasDerivAt_tailQ hp x)
    exact hd
  have hUl₁ (x y : ℝ) : HasDerivAt (U₁ · y) (U₂ x y) x := by
    have hd := ((hasDerivAt_tailPJet p 1 x).const_mul (F y)).sub (hasDerivAt_tailQFirst hp x)
    exact hd
  have hfirst {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
      deriv (leftStripTailTerm p · y) x = E x y*(U₁ x y-L (y-x)*U x y) := by
    have heq : (leftStripTailTerm p · y) =ᶠ[𝓝 x] fun t ↦ E t y*U t y := by
      filter_upwards [eventually_gt_nhds hx, eventually_lt_nhds hxy] with t ht hty
      exact tail_eq_split hp ht (sub_pos.mpr hty) (hx.trans hxy)
    have hd := (hEl hxy).mul (hUl x y)
    change HasDerivAt (fun t ↦ E t y*U t y) _ x at hd
    rw [heq.deriv_eq, hd.deriv]
    ring
  have hsecond {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
      deriv (deriv (leftStripTailTerm p · y)) x = E x y*M x y := by
    have heq : deriv (leftStripTailTerm p · y) =ᶠ[𝓝 x] fun t ↦
        E t y*(U₁ t y-L (y-t)*U t y) := by
      filter_upwards [eventually_gt_nhds hx, eventually_lt_nhds hxy] with t ht hty
      exact hfirst ht hty
    have hl := (hasDerivAt_profileSlope hh (sub_pos.mpr hxy)).comp x
      ((hasDerivAt_id' x).const_sub y)
    have hd := (hEl hxy).mul ((hUl₁ x y).sub (hl.mul (hUl x y)))
    change HasDerivAt (fun t ↦ E t y*(U₁ t y-L (y-t)*U t y)) _ x at hd
    rw [heq.deriv_eq, hd.deriv]
    simp only [M, L, q, Pi.sub_apply, Pi.mul_apply, Function.comp_apply]
    ring
  have heq : (fun y ↦ deriv (deriv (leftStripTailTerm p · y)) a) =ᶠ[𝓝 v]
      fun y ↦ E a y*M a y := by
    filter_upwards [eventually_gt_nhds hav] with y hy using hsecond ha hy
  have hF := hasDerivAt_upperTailGap (t := v) hh
  have hFx := (div_eq_iff (tail_gap_pos hh hv).ne').mp (upperTailGap_logDeriv hh hv)
  rw [hF.deriv] at hFx
  have hUr (k : ℕ) (Q : ℝ) :=
    ((hF.mul_const (tailPJet p k a)).sub_const Q)
  have hs := (hasDerivAt_id' v).sub_const a
  have hLr := (hasDerivAt_profileSlope hh (sub_pos.mpr hav)).comp v hs
  have hqr := (hasDerivAt_profileCurvature hh (sub_pos.mpr hav)).comp v hs
  have hMr := ((hUr 2 (tailQSecond p a)).sub
    ((hLr.const_mul 2).mul (hUr 1 (tailQFirst p a)))).add
    (((hLr.pow 2).add hqr).mul (hUr 0 (tailQ p a)))
  change HasDerivAt (M a) _ v at hMr
  have hd := hEr.mul hMr
  change HasDerivAt (fun y ↦ E a y*M a y) _ v at hd
  dsimp only
  rw [heq.deriv_eq, hd.deriv, hsecond ha hav]
  rw [hFx]
  dsimp only [M, U, U₁, U₂, E, L, q, F, Pi.add_apply, Pi.sub_apply, Pi.mul_apply,
    Pi.pow_apply, Function.comp_apply]
  simp only [profileSlope]
  generalize leftStripWeight h a v * (c*Real.exp (-((3+h)*v))) = weight
  generalize upperTailSlope h (v-a) = slope
  generalize upperTailSlope h v = upperSlope
  generalize profileCurvature h (v-a) = curvature
  ring

/-- The cancelled finite-sum correction on the left strip above seven halves. -/
theorem leftStrip_tail_seven_halves_lt {p : ℕ} (hp : 11 ≤ p) {a v γ : ℝ}
    (ha : 0 < a) (hamax : a ≤ 1/2) (hd : 7/2 ≤ v-a) (hγ : 5/12 ≤ γ)
    (hγmax : γ ≤ 1) :
    deriv (fun y ↦ deriv (deriv (leftStripTailTerm p · y)) a) v -
      γ*deriv (deriv (leftStripTailTerm p · v)) a < 43/1000 := by
  let h := 3/(p : ℝ)
  let d := v-a
  let E := leftStripWeight h a v * (((3+h)*(3+2*h)/2)*Real.exp (-((3+h)*v)))
  let F := upperTailGap h
  let L := profileSlope h d
  let q := profileCurvature h d
  let H₀ := L^2+q
  let C₀ := q*(4*L-2-h)
  let β := 1+h+upperTailSlope h d+upperTailSlope h v+γ
  let r := 1+h+upperTailSlope h d+γ
  let P := tailPJet p 0 a
  let P₁ := tailPJet p 1 a
  let P₂ := tailPJet p 2 a
  let Q := tailQ p a
  let Q₁ := tailQFirst p a
  let Q₂ := tailQSecond p a
  have hp₀ : 0 < p := by omega
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp₀
  have hh : 0 < h := by dsimp [h]; positivity
  have hhmax : h ≤ 3/11 := div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    (by exact_mod_cast hp)
  have hd₀ : 0 < d := by linarith
  have hav : a < v := sub_pos.mp hd₀
  have hv := ha.trans hav
  have hFv := tail_gap_pos hh hv
  have hFd := tail_gap_pos hh hd₀
  have hE : 0 < E := by unfold E leftStripWeight; positivity
  have hHb (t : ℝ) (ht : 7/2 ≤ t) : 0 < upperTailSlope h t ∧ upperTailSlope h t ≤ 2/7 := by
    obtain ⟨hp, hq, _⟩ := upperTailSlope_bounds hh (by linarith : 0 < t)
    exact ⟨hp, hq.trans ((one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 7/2) ht).trans_eq (by norm_num))⟩
  obtain ⟨hH, hHmax⟩ := hHb d hd
  obtain ⟨hHv, hvmax⟩ := hHb v (by linarith)
  have hL : 5/7 ≤ L := by dsimp [L, profileSlope]; linarith
  have hLmax : L ≤ 1 := by dsimp [L, profileSlope]; linarith
  have hq₀ : 0 ≤ q := by dsimp [q, profileCurvature]; positivity
  have hqmax : q ≤ 4/49 := by
    have hq' := (upperTailSlope_bounds hh hd₀).2.2.2.1
    rw [(hasDerivAt_upperTailSlope hh hd₀).deriv, neg_neg] at hq'
    refine hq'.trans ?_
    have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 7/2) hd
    simpa only [one_div_pow, show (1/(7/2) : ℝ)^2 = 4/49 by norm_num] using
      pow_le_pow_left₀ (by positivity : 0 ≤ 1/d) hi 2
  have hH₀lo : 25/49 ≤ H₀ := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5/7) hL 2
    dsimp only [H₀]
    linarith
  have hH₀hi : H₀ ≤ 53/49 := by
    have h := pow_le_pow_left₀ (by linarith : 0 ≤ L) hLmax 2
    dsimp only [H₀]
    linarith
  have hC₀ : 0 ≤ C₀ := mul_nonneg hq₀ (by linarith)
  have hr : 17/12 ≤ r := by dsimp only [r]; linarith
  have hC : C₀ ≤ r*H₀ := by
    have h₁ := mul_le_mul_of_nonneg_left (show 4*L-2-h ≤ 2 by linarith) hq₀
    have h₂ := mul_le_mul hr hH₀lo (by norm_num) (by linarith only [hr])
    dsimp only [C₀]
    linarith only [h₁, h₂, hqmax]
  have hβ : 17/12 ≤ β := by dsimp only [β]; linarith
  have hβmax : β ≤ 219/77 := by dsimp only [β]; linarith
  have hβL : 0 ≤ 2*β*L-2*q := by
    have h := mul_le_mul hβ hL (by norm_num) (by linarith only [hβ])
    linarith only [h, hqmax]
  obtain ⟨hP, hP₁, hP₂, hPbound⟩ := tailP_bounds hp₀ ha.le
  obtain ⟨hQ, hQ₁, hQ₂, hQbound⟩ := tailQ_bounds hp₀ ha.le
  have hPsign : -r*(P₂-2*L*P₁)-2*q*P₁+(-r*H₀+C₀)*P ≤ 0 := by
    have h₁ := mul_le_mul (show 2*L ≤ 2 by linarith) (show P₁ ≤ (1/2)*P₂ from
      hPbound.trans (mul_le_mul_of_nonneg_right hamax hP₂)) hP₁ (by norm_num)
    have h₂ := mul_nonpos_of_nonpos_of_nonneg (show -r ≤ 0 by linarith)
      (show 0 ≤ P₂-2*L*P₁ by linarith only [h₁])
    have h₃ := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hq₀) hP₁
    have h₄ := mul_nonpos_of_nonpos_of_nonneg (show -r*H₀+C₀ ≤ 0 by linarith) hP
    linarith only [h₂, h₃, h₄]
  have hQ₈ : Q ≤ (1/8)*Q₂ := by
    have h := pow_le_pow_left₀ ha.le hamax 2
    exact hQbound.trans (mul_le_mul_of_nonneg_right (by linarith only [h]) hQ₂)
  have hQcap : β*(Q₂+H₀*Q) ≤ (219/77 : ℝ)*(1+53/392)*Q₂ := by
    have h := mul_le_mul hH₀hi hQ₈ hQ (by norm_num)
    have h₁ := add_le_add (le_refl Q₂) h
    have hb := mul_le_mul hβmax h₁ (by linarith only [hQ₂, hH₀lo, hQ, mul_nonneg (show 0 ≤ H₀ by linarith) hQ])
      (by norm_num)
    linarith only [hb]
  have hformula := tail_split_weighted_formula (γ := γ) hp₀ ha hav
  change _ = E*(F v*(-r*(P₂-2*L*P₁)-2*q*P₁+(-r*H₀+C₀)*P) +
    β*(Q₂+H₀*Q) - (2*β*L-2*q)*Q₁ - C₀*Q) at hformula
  have hupper : E*(F v*(-r*(P₂-2*L*P₁)-2*q*P₁+(-r*H₀+C₀)*P) +
    β*(Q₂+H₀*Q) - (2*β*L-2*q)*Q₁ - C₀*Q) ≤
      (219/77 : ℝ)*(1+53/392)*(E*Q₂) := by
    have hp := mul_nonpos_of_nonneg_of_nonpos hFv.le hPsign
    have hq₁ := mul_nonneg hβL hQ₁
    have hq₂ := mul_nonneg hC₀ hQ
    calc
      _ ≤ E*((219/77 : ℝ)*(1+53/392)*Q₂) :=
        mul_le_mul_of_nonneg_left (by linarith only [hp, hq₁, hq₂, hQcap]) hE.le
      _ = _ := by ring
  have hFx (t : ℝ) (ht : 0 < t) : upperTailSlope h t*F t = Real.exp (-(h*t)) := by
    have he := upperTailGap_logDeriv hh ht
    rw [(hasDerivAt_upperTailGap hh).deriv] at he
    exact ((div_eq_iff (tail_gap_pos hh ht).ne').mp he).symm
  have hqEq : q*F d^2 = Real.exp (-(h*d)) := by
    have hF := tail_gap_factor (t := d) hh
    have hF1 : (h+upperTailSlope h d)*F d = 1 := by nlinarith only [hF, hFx d hd₀]
    change (upperTailSlope h d*(h+upperTailSlope h d))*F d^2 = _
    calc
      _ = (upperTailSlope h d*F d)*((h+upperTailSlope h d)*F d) := by ring
      _ = _ := by rw [hF1, mul_one, hFx d hd₀]
  have hEratio : E = Real.exp (-((1+h)*v+a))/(F v*F d) := by
    unfold E leftStripWeight logReciprocalGap
    rw [show v-Real.log (F v)+(d-Real.log (F d)) =
        (v+d)+(-Real.log (F v)+ -Real.log (F d)) by ring,
      Real.exp_add,
      show Real.exp (-Real.log (F v)+ -Real.log (F d)) = (F v)⁻¹*(F d)⁻¹ by
        rw [Real.exp_add, Real.exp_neg, Real.exp_neg, Real.exp_log hFv, Real.exp_log hFd]]
    have hc : 0 < (3+h)*(3+2*h)/2 := by positivity
    calc
      _ = (Real.exp (v+d)*Real.exp (-((3+h)*v)))/(F v*F d) := by
        field_simp [hc.ne', hFv.ne', hFd.ne']
        <;> ring
      _ = _ := by
        rw [← Real.exp_add]
        congr 2
        dsimp [d]
        ring
  have hfactor : E*Q₂ = Real.exp (-d)*q*(F d/F v) *
      (Real.exp ((1+h)*a)*(1+(3+h)*F a)) := by
    rw [hEratio]
    change Real.exp (-((1+h)*v+a))/(F v*F d) *
      (Real.exp ((3+2*h)*a)*(1+(3+h)*F a)) = _
    have he : Real.exp (-((1+h)*v+a))*Real.exp ((3+2*h)*a) =
        Real.exp (-d)*Real.exp (-(h*d))*Real.exp ((1+h)*a) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      dsimp [d]
      ring
    rw [show Real.exp (-((1+h)*v+a))/(F v*F d) *
      (Real.exp ((3+2*h)*a)*(1+(3+h)*F a)) =
      (Real.exp (-((1+h)*v+a))*Real.exp ((3+2*h)*a))*(1+(3+h)*F a)/(F v*F d) by ring,
      he, ← hqEq]
    field_simp [hFv.ne', hFd.ne']
    <;> ring
  have hFr : F d/F v ≤ 1 := by
    rw [div_le_one hFv]
    exact monotone_of_hasDerivAt_nonneg
      (fun t ↦ hasDerivAt_upperTailGap (t := t) hh) (fun _ ↦ (Real.exp_pos _).le)
      (sub_le_self _ ha.le)
  have hea : Real.exp ((1+h)*a) ≤ 2 := by
    have hhA : (1+h)*a ≤ 2/3 := by
      have hm := mul_le_mul (show 1+h ≤ 14/11 by linarith) hamax ha.le (by norm_num)
      linarith
    have he : Real.exp (2/3 : ℝ)^3 = Real.exp 2 := by
      rw [← Real.exp_nat_mul]; norm_num
    have he₂ : Real.exp 2 < 8 := by
      rw [show (2 : ℝ) = (2 : ℕ)*(1 : ℝ) by norm_num, Real.exp_nat_mul]
      exact (pow_lt_pow_left₀ (Real.exp_one_lt_d9.trans (by norm_num : (2.7182818286 : ℝ) < 11/4))
        (Real.exp_pos 1).le (by decide : 2 ≠ 0)).trans (by norm_num)
    have hcap : Real.exp (2/3 : ℝ) ≤ 2 := by
      by_contra! hn
      have hm := pow_lt_pow_left₀ hn (by norm_num) (by decide : 3 ≠ 0)
      rw [he] at hm
      linarith
    exact (Real.exp_le_exp.mpr hhA).trans hcap
  have hFa := (tail_gap_pos hh ha).le
  have hFa' : 1+(3+h)*F a ≤ 8/3 := by
    have h := mul_le_mul (show 3+h ≤ 10/3 by linarith)
      ((upperTailGap_le hh).trans hamax) hFa (by norm_num)
    linarith only [h]
  have hEQ : E*Q₂ ≤ (16/3 : ℝ)*(1/33)*(4/49) := by
    rw [hfactor]
    have hs := mul_le_mul hea hFa' (by positivity) (by norm_num)
    have hbase := mul_le_mul (leftStrip_exp_neg_seven_halves_lt hd).le hqmax hq₀ (by norm_num)
    have hbase' := (mul_le_of_le_one_right (mul_nonneg (Real.exp_pos _).le hq₀) hFr).trans hbase
    have hm := mul_le_mul hbase' hs (by positivity) (by norm_num)
    linarith only [hm]
  rw [hformula]
  exact (hupper.trans (mul_le_mul_of_nonneg_left hEQ (by norm_num))).trans_lt (by norm_num)

#print axioms leftStrip_tail_seven_halves_lt

#print axioms leftStrip_tail_mixed_lt

end RefinedBMV.PositiveCenter
