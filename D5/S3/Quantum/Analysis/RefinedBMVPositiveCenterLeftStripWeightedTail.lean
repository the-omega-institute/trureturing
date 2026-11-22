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

#print axioms leftStrip_tail_mixed_lt

end RefinedBMV.PositiveCenter
