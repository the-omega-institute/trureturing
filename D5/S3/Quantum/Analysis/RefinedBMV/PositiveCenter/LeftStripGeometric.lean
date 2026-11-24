/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/LeftStripGeometric
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: One-sided finite geometric reduction of the exact left-strip weighted derivative. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripGeometricProfile
import Batteries.Tactic.OpenPrivate

/-! Finite geometric scalar and its transfer to the mixed kernel sign. -/

open Filter Set
open scoped BigOperators Topology

noncomputable section

namespace RefinedBMV.PositiveCenter

open DividedDifference (homogeneousThree clear_distinct clear_repeat_first clear_repeat_last)

open private leftStripS leftStripE leftStripExpMoment leftStripReflectedSlope
  leftStrip_hasDerivAt_expMoment_left leftStrip_hasDerivAt_moment_left leftStrip_weightedThird_eq
  leftStrip_small_slope leftStrip_contDiffAt_S leftStrip_hasDerivAt_exp_sum
  from D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripCollision
open private weightedThird leftStrip_logKernel_mixed_lt_of_weighted
  from D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripKernel

open private hasDerivAt_negativeMarginal negativeMarginalDerivative compositionMoment_zero_zero
  exponent gapCount from D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterLeftLimit

open private spacing geometricScale spacing_pos geometricProfile f H geometricProfile_eq
  hasDerivAt_geometricProfile profileSecond profileThird hasDerivAt_profileFirst
  hasDerivAt_profileSecond geometricGEndpoint hasDerivAt_decay negativeMarginalFactor
  negative_marginal_eq negativeMarginalFactor_pos positiveRadical positive_marginal_eq
  geomE hasDerivAt_geomE endpointWeighted from D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripGeometricProfile

private theorem reflectedSlope_sub {p : ℕ} (hp : 0 < p) {v : ℝ} (hv : 0 < v) :
    let h := spacing p
    let V := negativeMarginalFactor h
    profileSlope h v-leftStripReflectedSlope p v = (V v-deriv V v)/(2*V v) := by
  let h := spacing p
  let F := upperTailGap h
  let c := geometricScale h
  let C (t : ℝ) := compositionMoment p 0 (-t)
  let K (t : ℝ) := c*F t^2*Real.exp (-t)
  let V := negativeMarginalFactor h
  have hh := spacing_pos hp
  have hvF := tail_gap_pos hh hv
  have hc := compositionMoment_marginal_pos hp (neg_ne_zero.mpr hv.ne')
  have hK : 0 < K v := by dsimp [K, c, geometricScale]; positivity
  have hC := hasDerivAt_negativeMarginal p v
  have hs : leftStripReflectedSlope p v = negativeMarginalDerivative p v/(2*C v) := by
    unfold leftStripReflectedSlope
    rw [((hC.sqrt hc.ne')).deriv]
    have hroot : 0 < Real.sqrt (C v) := Real.sqrt_pos.mpr hc
    change negativeMarginalDerivative p v/(2*Real.sqrt (C v))/Real.sqrt (C v) = _
    rw [div_div, mul_assoc, ← sq, Real.sq_sqrt hc.le]
  have hrate := (div_eq_iff hvF.ne').mp (upperTailGap_logDeriv hh hv)
  rw [(hasDerivAt_upperTailGap hh).deriv] at hrate
  have hdK : HasDerivAt K (K v*(2*upperTailSlope h v-1)) v := by
    have hdec : HasDerivAt (fun t : ℝ ↦ Real.exp (-t)) (-1*Real.exp (-v)) v := by
      simpa only [one_mul] using hasDerivAt_decay 1 v
    have hd := (((hasDerivAt_upperTailGap hh (t := v)).pow 2).const_mul c).mul hdec
    change HasDerivAt K _ v at hd
    apply hd.congr_deriv
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, neg_mul, K, Pi.pow_apply]
    rw [hrate]
    change c*(2*F v*(upperTailSlope h v*F v))*Real.exp (-v) +
      c*F v^2*(-(1*Real.exp (-v))) = c*F v^2*Real.exp (-v)*(2*upperTailSlope h v-1)
    ring
  have he : V = fun t ↦ K t*C t := funext fun t ↦ (negative_marginal_eq hp t).symm
  change profileSlope h v-leftStripReflectedSlope p v = (V v-deriv V v)/(2*V v)
  have hd : HasDerivAt (fun t ↦ K t*C t)
      (K v*(2*upperTailSlope h v-1)*C v+K v*negativeMarginalDerivative p v) v := hdK.mul hC
  have hc' : C v ≠ 0 := hc.ne'
  rw [hs, he, hd.deriv]
  unfold profileSlope
  dsimp only
  field_simp [hc', hK.ne']
  ring

private def marginalFactorFirst (h t : ℝ) : ℝ :=
  let F := upperTailGap h t
  let e := Real.exp (-(h*t))
  let r := 3+2*h
  r*(e-Real.exp (-(r*t))) -
    geometricScale h*Real.exp (-t)*(2*F*e-F^2)

private theorem deriv_negativeMarginalFactor {h : ℝ} (hh : 0 < h) (t : ℝ) :
    deriv (negativeMarginalFactor h) t = marginalFactorFirst h t := by
  let c := geometricScale h
  let F := upperTailGap h
  let r := 3+2*h
  have hF := hasDerivAt_upperTailGap (t := t) hh
  have hdec : HasDerivAt (fun x : ℝ ↦ Real.exp (-x)) (-1*Real.exp (-t)) t := by
    simpa only [one_mul] using hasDerivAt_decay 1 t
  have hd := (((hasDerivAt_decay r t).sub_const 1).add (hF.const_mul r)).sub
    (((hF.pow 2).const_mul c).mul hdec)
  have hd' : HasDerivAt (negativeMarginalFactor h) _ t := hd
  rw [hd'.deriv]
  simp only [marginalFactorFirst, Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.pow_apply]
  dsimp only [F, r, c]
  ring

-- The radicand derivatives are factored using the same gap identity as upperTailLambda.
private def radicandJet (h t : ℝ) : ℝ × ℝ × ℝ :=
  let j := 1+h
  let F := upperTailGap h t
  let e := Real.exp (-(h*t))
  let E := Real.exp (-(j*t))
  let R := j*F-1+E
  let R₁ := j*(e-E)
  let R₂ := j*(-h*e+j*E)
  let K := F*R
  let K₁ := e*R+F*R₁
  let K₂ := (-h*e)*R+2*e*R₁+F*R₂
  let prefactor := 2*geometricScale h*Real.exp (-(2*t))
  (prefactor*K, prefactor*(K₁-2*K), prefactor*(K₂-4*K₁+4*K))

private theorem hasDerivAt_radicandJet {h : ℝ} (hh : 0 < h) (t : ℝ) :
    HasDerivAt (fun x ↦ 1-upperTailLambda h x) (radicandJet h t).1 t ∧
    HasDerivAt (fun x ↦ (radicandJet h x).1) (radicandJet h t).2.1 t ∧
    HasDerivAt (fun x ↦ (radicandJet h x).2.1) (radicandJet h t).2.2 t := by
  let j := 1+h
  let F := upperTailGap h
  let e (x : ℝ) := Real.exp (-(h*x))
  let E (x : ℝ) := Real.exp (-(j*x))
  let R (x : ℝ) := j*F x-1+E x
  let R₁ (x : ℝ) := j*(e x-E x)
  let R₂ (x : ℝ) := j*(-h*e x+j*E x)
  let K (x : ℝ) := F x*R x
  let K₁ (x : ℝ) := e x*R x+F x*R₁ x
  let K₂ (x : ℝ) := (-h*e x)*R x+2*e x*R₁ x+F x*R₂ x
  let c := 2*geometricScale h
  have hF := hasDerivAt_upperTailGap (t := t) hh
  have hR : HasDerivAt R (R₁ t) t := by
    apply (((hF.const_mul j).sub_const 1).add (hasDerivAt_decay j t)).congr_deriv
    change j*e t + -j*E t = j*(e t-E t)
    ring
  have hR₁ : HasDerivAt R₁ (R₂ t) t := by
    apply (((hasDerivAt_decay h t).sub (hasDerivAt_decay j t)).const_mul j).congr_deriv
    change j*(-h*e t - -j*E t) = j*(-h*e t+j*E t)
    ring
  have hK : HasDerivAt K (K₁ t) t := hF.mul hR
  have hK₁ : HasDerivAt K₁ (K₂ t) t := by
    apply (((hasDerivAt_decay h t).mul hR).add (hF.mul hR₁)).congr_deriv
    change (-h*e t)*R t+e t*R₁ t+(e t*R₁ t+F t*R₂ t) = _
    unfold K₂
    ring
  have hP := (hasDerivAt_decay 2 t).const_mul c
  refine ⟨?_, ?_, ?_⟩
  · have hd := (hasDerivAt_upperTailLambda (t := t) hh).const_sub 1
    apply hd.congr_deriv
    change -(-(3+h)*(3+2*h)*Real.exp (-(2*t))*F t*R t) =
      c*Real.exp (-(2*t))*K t
    unfold c geometricScale K
    ring
  · apply (hP.mul hK).congr_deriv
    change c*(-2*Real.exp (-(2*t)))*K t+
      c*Real.exp (-(2*t))*K₁ t = c*Real.exp (-(2*t))*(K₁ t-2*K t)
    ring
  · apply (hP.mul (hK₁.sub (hK.const_mul 2))).congr_deriv
    change c*(-2*Real.exp (-(2*t)))*(K₁ t-2*K t)+
      c*Real.exp (-(2*t))*(K₂ t-2*K₁ t) = c*Real.exp (-(2*t))*(K₂ t-4*K₁ t+4*K t)
    ring

private def radicalFirst (h t : ℝ) : ℝ :=
  (radicandJet h t).1/(2*positiveRadical h t)

private def radicalSecond (h t : ℝ) : ℝ :=
  ((radicandJet h t).2.1-2*radicalFirst h t^2)/(2*positiveRadical h t)

private def radicalThird (h t : ℝ) : ℝ :=
  ((radicandJet h t).2.2-6*radicalFirst h t*radicalSecond h t)/(2*positiveRadical h t)

private theorem hasDerivAt_positiveRadical {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : 0 < t) :
    let h := spacing p
    let b := positiveRadical h
    HasDerivAt b (radicalFirst h t) t ∧
    HasDerivAt (radicalFirst h) (radicalSecond h t) t ∧
    HasDerivAt (radicalSecond h) (radicalThird h t) t := by
  let h := spacing p
  let b := positiveRadical h
  have hh := spacing_pos hp
  have hf : 0 < f h t := by
    simp only [f, geometricProfile, geometricScale]
    positivity
  have hs : 0 < leftStripS p t := Real.sqrt_pos.mpr (compositionMoment_marginal_pos hp ht.ne')
  rw [positive_marginal_eq hp ht] at hs
  have hb : 0 < b t := pos_of_mul_pos_right hs hf.le
  have hpos : 0 < 1-upperTailLambda h t := Real.sqrt_pos.mp hb
  have hden := (mul_pos zero_lt_two hb).ne'
  obtain ⟨hR, hR₁, hR₂⟩ := hasDerivAt_radicandJet hh t
  change HasDerivAt (fun x ↦ (radicandJet h x).1) (radicandJet h t).2.1 t at hR₁
  change HasDerivAt (fun x ↦ (radicandJet h x).2.1) (radicandJet h t).2.2 t at hR₂
  have hb₁ : HasDerivAt b (radicalFirst h t) t := hR.sqrt hpos.ne'
  have hn₁ : (radicandJet h t).1 = radicalFirst h t*(2*b t) :=
    (div_mul_cancel₀ _ hden).symm
  have hb₂ : HasDerivAt (radicalFirst h) (radicalSecond h t) t := by
    apply (hR₁.fun_div (hb₁.const_mul 2) hden).congr_deriv
    change _ = ((radicandJet h t).2.1-2*radicalFirst h t^2)/(2*b t)
    rw [hn₁]
    field_simp [hb.ne']
  have hn₂ : (radicandJet h t).2.1-2*radicalFirst h t^2 = radicalSecond h t*(2*b t) :=
    (div_mul_cancel₀ _ hden).symm
  refine ⟨hb₁, hb₂, ?_⟩
  apply ((hR₂.sub ((hb₂.pow 2).const_mul 2)).fun_div (hb₁.const_mul 2) hden).congr_deriv
  change _ = ((radicandJet h t).2.2-6*radicalFirst h t*radicalSecond h t)/(2*b t)
  simp only [Pi.sub_apply, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  rw [hn₂]
  field_simp [hb.ne']
  ring

private theorem positiveRadical_deriv_eq {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : 0 < t) :
    let h := spacing p
    let b := positiveRadical h
    deriv b t = radicalFirst h t ∧
    deriv (deriv b) t = radicalSecond h t ∧
    deriv (deriv (deriv b)) t = radicalThird h t := by
  let h := spacing p
  let b := positiveRadical h
  have h₁ {x : ℝ} (hx : 0 < x) : deriv b x = radicalFirst h x :=
    (hasDerivAt_positiveRadical hp hx).1.deriv
  have h₂ {x : ℝ} (hx : 0 < x) : deriv (deriv b) x = radicalSecond h x := by
    have he : deriv b =ᶠ[𝓝 x] radicalFirst h := by
      filter_upwards [eventually_gt_nhds hx] with y hy using h₁ hy
    rw [he.deriv_eq, (hasDerivAt_positiveRadical hp hx).2.1.deriv]
  refine ⟨h₁ ht, h₂ ht, ?_⟩
  have he : deriv (deriv b) =ᶠ[𝓝 t] radicalSecond h := by
    filter_upwards [eventually_gt_nhds ht] with y hy using h₂ hy
  rw [he.deriv_eq, (hasDerivAt_positiveRadical hp ht).2.2.deriv]

private def marginalSecond (h t : ℝ) : ℝ :=
  profileSecond h 0 t*positiveRadical h t +
    2*profileSlope h t*deriv (positiveRadical h) t +
    deriv (deriv (positiveRadical h)) t

private def marginalThird (h t : ℝ) : ℝ :=
  profileThird h 0 t*positiveRadical h t +
    3*profileSecond h 0 t*deriv (positiveRadical h) t +
    3*profileSlope h t*deriv (deriv (positiveRadical h)) t +
    deriv (deriv (deriv (positiveRadical h))) t

private theorem positive_marginal_derivatives {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : 0 < t) :
    let h := spacing p
    deriv (leftStripS p) t =
      f h t*(profileSlope h t*positiveRadical h t+deriv (positiveRadical h) t) ∧
    deriv (deriv (leftStripS p)) t = f h t*marginalSecond h t ∧
    deriv (deriv (deriv (leftStripS p))) t = f h t*marginalThird h t := by
  let h := spacing p
  let b := positiveRadical h
  let F := f h
  let c := Real.sqrt (geometricScale h)
  let α := profileSlope h
  have hh := spacing_pos hp
  have hb {x : ℝ} (hx : 0 < x) : ContDiffAt ℝ 3 b x := by
    have hf : 0 < F x := by
      simp only [F, f, geometricProfile, geometricScale]
      positivity
    have hs : 0 < leftStripS p x := Real.sqrt_pos.mpr (compositionMoment_marginal_pos hp hx.ne')
    rw [positive_marginal_eq hp hx] at hs
    have hpos : 0 < 1-upperTailLambda h x :=
      Real.sqrt_pos.mp (pos_of_mul_pos_right hs hf.le)
    have hd : ContDiff ℝ 3 (fun t : ℝ ↦ 1-upperTailLambda h t) := by
      unfold upperTailLambda upperTailGap
      fun_prop
    exact hd.contDiffAt.sqrt hpos.ne'
  have hb₁ {x : ℝ} (hx : 0 < x) : HasDerivAt b (deriv b x) x :=
    ((hb hx).differentiableAt (by decide)).hasDerivAt
  have hb₂ {x : ℝ} (hx : 0 < x) : HasDerivAt (deriv b) (deriv (deriv b) x) x :=
    (((hb hx).derivWithin (show (2 : WithTop ℕ∞)+1 ≤ 3 by decide)).differentiableAt
      (by decide)).hasDerivAt
  have hb₃ {x : ℝ} (hx : 0 < x) :
      HasDerivAt (deriv (deriv b)) (deriv (deriv (deriv b)) x) x :=
    ((((hb hx).derivWithin (show (2 : WithTop ℕ∞)+1 ≤ 3 by decide)).derivWithin
      (show (1 : WithTop ℕ∞)+1 ≤ 2 by decide)).differentiableAt (by decide)).hasDerivAt
  have hs₁ {x : ℝ} (hx : 0 < x) :
      deriv (leftStripS p) x = (F x*(α x-0))*b x+F x*deriv b x := by
    have he : leftStripS p =ᶠ[𝓝 x] fun y ↦ F y*b y := by
      filter_upwards [eventually_gt_nhds hx] with y hy using positive_marginal_eq hp hy
    exact (((hasDerivAt_geometricProfile hh hx 0 c).mul (hb₁ hx)).congr_of_eventuallyEq he).deriv
  have hs₂ {x : ℝ} (hx : 0 < x) :
      deriv (deriv (leftStripS p)) x =
        (F x*profileSecond h 0 x)*b x+2*((F x*(α x-0))*deriv b x)+F x*deriv (deriv b) x := by
    have he : deriv (leftStripS p) =ᶠ[𝓝 x]
        fun y ↦ (F y*(α y-0))*b y+F y*deriv b y := by
      filter_upwards [eventually_gt_nhds hx] with y hy using hs₁ hy
    have hd := ((hasDerivAt_profileFirst hh hx 0 c).mul (hb₁ hx)).add
      ((hasDerivAt_geometricProfile hh hx 0 c).mul (hb₂ hx))
    have hd' : HasDerivAt (fun y ↦ F y*(α y-0)*b y+F y*deriv b y) _ x := hd
    rw [he.deriv_eq, hd'.deriv]
    simp only [F, h, α, c, f]
    ring
  have he : deriv (deriv (leftStripS p)) =ᶠ[𝓝 t]
      fun y ↦ (F y*profileSecond h 0 y)*b y+2*((F y*(α y-0))*deriv b y)+F y*deriv (deriv b) y := by
    filter_upwards [eventually_gt_nhds ht] with y hy using hs₂ hy
  refine ⟨?_, ?_, ?_⟩
  · rw [hs₁ ht]
    change _ = F t*(α t*b t+deriv b t)
    ring
  · rw [hs₂ ht]
    unfold marginalSecond
    change _ = F t*(profileSecond h 0 t*b t+2*α t*deriv b t+deriv (deriv b) t)
    ring
  · have hd := (((hasDerivAt_profileSecond hh ht 0 c).mul (hb₁ ht)).add
        (((hasDerivAt_profileFirst hh ht 0 c).mul (hb₂ ht)).const_mul 2)).add
        ((hasDerivAt_geometricProfile hh ht 0 c).mul (hb₃ ht))
    change HasDerivAt (fun y ↦ (F y*profileSecond h 0 y)*b y+
        2*((F y*(α y-0))*deriv b y)+F y*deriv (deriv b) y) _ t at hd
    rw [he.deriv_eq, hd.deriv]
    unfold marginalThird
    change _ = F t*(profileThird h 0 t*b t+3*profileSecond h 0 t*deriv b t+
      3*α t*deriv (deriv b) t+deriv (deriv (deriv b)) t)
    simp only [F, h, α, c, f]
    ring

/-- The denominator-cleared scalar expression for the endpoint comparison. -/
def leftStripGeometricScalar (h a w : ℝ) : ℝ :=
  let v := w+a
  let V := negativeMarginalFactor h v
  let A := V-marginalFactorFirst h v
  let b := positiveRadical h
  let r := 3+2*h
  let k := 2+h
  let B₂ := profileSecond h 0 w*b w+2*profileSlope h w*radicalFirst h w+radicalSecond h w
  let B₃ := profileThird h 0 w*b w+3*profileSecond h 0 w*radicalFirst h w+
    3*profileSlope h w*radicalSecond h w+radicalThird h w
  2*V*(b v*B₃+radicalFirst h v*B₂-profileThird h 0 w) +
    A*(b v*B₂-profileSecond h 0 w) +
    Real.exp (-(r*w))*(2*V*profileThird h r w+A*profileSecond h r w) +
    upperTailGap h w*Real.exp (-((3+h)*w))*(A-2*k*V)*geometricGEndpoint h

private theorem endpointWeighted_eq_scalar {p : ℕ} (hp : 0 < p) {a v : ℝ}
    (hv : 0 < v) (hav : a < v) :
    let h := spacing p
    let w := v-a
    endpointWeighted p a v =
      f h v*f h w/(2*negativeMarginalFactor h v)*leftStripGeometricScalar h a w := by
  let h := spacing p
  let w := v-a
  let c := Real.sqrt (geometricScale h)
  let V := negativeMarginalFactor h
  let A := V v-deriv V v
  let γ := leftStripReflectedSlope p v
  let α := profileSlope h
  let r := 3+2*h
  let k := 2+h
  let b := positiveRadical h
  have hh := spacing_pos hp
  have hw := sub_pos.mpr hav
  have hV := negativeMarginalFactor_pos hp hv
  have hα := reflectedSlope_sub hp hv
  change α v-γ = A/(2*V v) at hα
  have hH : H h w/c = f h w*Real.exp (-(r*w)) := by
    change Real.exp (logReciprocalGap h w-r*w)/1/c =
      Real.exp (logReciprocalGap h w-0*w)/c*Real.exp (-(r*w))
    rw [div_one, zero_mul, sub_zero, Real.exp_sub, Real.exp_neg]
    ring
  have hG : Real.exp (-(k*w))/c =
      f h w*(upperTailGap h w*Real.exp (-((3+h)*w))) := by
    rw [show f h w = _ from geometricProfile_eq hh hw 0 c]
    simp only [sub_zero, one_mul]
    have hFw := tail_gap_pos hh hw
    have hc : 0 < c := by dsimp [c, geometricScale]; positivity
    have he : Real.exp w*Real.exp (-((3+h)*w)) = Real.exp (-(k*w)) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [k]
      ring
    have hFw' : upperTailGap h w ≠ 0 := hFw.ne'
    change _ = Real.exp w/(c*upperTailGap h w)*
      (upperTailGap h w*Real.exp (-((3+h)*w)))
    calc
      _ = (Real.exp w*Real.exp (-((3+h)*w)))/c := by rw [he]
      _ = _ := by field_simp [hc.ne', hFw']
  unfold endpointWeighted
  rw [(hasDerivAt_geomE hp hv hav (geometricGEndpoint h)).deriv]
  unfold geomE
  dsimp only
  rw [positive_marginal_eq hp hv, (positive_marginal_derivatives hp hv).1,
    (positive_marginal_derivatives hp hw).2.1, (positive_marginal_derivatives hp hw).2.2]
  change _ = f h v*f h w/(2*V v)*leftStripGeometricScalar h a w
  unfold leftStripGeometricScalar
  rw [show w+a = v by dsimp [w]; ring]
  dsimp only
  have hr := positiveRadical_deriv_eq hp hw
  have hv' := (positiveRadical_deriv_eq hp hv).1
  rw [← show deriv V v = marginalFactorFirst h v from deriv_negativeMarginalFactor hh v,
    ← show deriv b v = radicalFirst h v from hv',
    ← show deriv b w = radicalFirst h w from hr.1,
    ← show deriv (deriv b) w = radicalSecond h w from hr.2.1,
    ← show deriv (deriv (deriv b)) w = radicalThird h w from hr.2.2]
  have hγ : γ = α v-A/(2*V v) := by linarith only [hα]
  have hcoeff := show leftStripReflectedSlope p v = _ from hγ
  rw [hcoeff]
  change _ = f h v*f h w/(2*V v)*
    (2*V v*(b v*marginalThird h w+deriv b v*marginalSecond h w-profileThird h 0 w) +
      A*(b v*marginalSecond h w-profileSecond h 0 w) +
      Real.exp (-(r*w))*(2*V v*profileThird h r w+A*profileSecond h r w) +
      upperTailGap h w*Real.exp (-((3+h)*w))*(A-2*k*V v)*geometricGEndpoint h)
  have hx2 : f h w*profileSecond h 0 w -
      (H h w*profileSecond h r w+Real.exp (-(k*w))*geometricGEndpoint h)/c =
      f h w*(profileSecond h 0 w-Real.exp (-(r*w))*profileSecond h r w-
        upperTailGap h w*Real.exp (-((3+h)*w))*geometricGEndpoint h) := by
    rw [add_div, mul_div_right_comm (H h w), mul_div_right_comm (Real.exp (-(k*w))), hH, hG]
    ring
  have hx3 : f h w*profileThird h 0 w -
      (H h w*profileThird h r w-k*(Real.exp (-(k*w))*geometricGEndpoint h))/c =
      f h w*(profileThird h 0 w-Real.exp (-(r*w))*profileThird h r w+
        k*upperTailGap h w*Real.exp (-((3+h)*w))*geometricGEndpoint h) := by
    rw [sub_div, mul_div_right_comm (H h w), mul_div_assoc,
      mul_div_right_comm (Real.exp (-(k*w))), hH, hG]
    ring
  change (α v-A/(2*V v))*(f h v*(f h w*profileSecond h 0 w -
      (H h w*profileSecond h r w+Real.exp (-(k*w))*geometricGEndpoint h)/c) -
      (f h v*b v)*(f h w*marginalSecond h w)) -
    (α v*f h v*(f h w*profileSecond h 0 w -
        (H h w*profileSecond h r w+Real.exp (-(k*w))*geometricGEndpoint h)/c) +
      f h v*(f h w*profileThird h 0 w -
        (H h w*profileThird h r w-k*(Real.exp (-(k*w))*geometricGEndpoint h))/c) -
      (f h v*(α v*b v+deriv b v)*(f h w*marginalSecond h w) +
        f h v*b v*(f h w*marginalThird h w))) = _
  rw [hx2, hx3]
  have hV' : V v ≠ 0 := hV.ne'
  field_simp [hV']
  ring

/-- The exact lower comparison, expressed entirely in scalar profiles. -/
theorem leftStrip_geometric_scalar_le {p : ℕ} (hp : 0 < p) {a v : ℝ}
    (ha : 0 ≤ a) (hav : a < v) :
    let h := spacing p
    let w := v-a
    let N (x y : ℝ) := compositionMoment p x y -
      Real.sqrt (compositionMoment p 0 y*compositionMoment p 0 (y-x))
    f h v*f h w/(2*negativeMarginalFactor h v)*leftStripGeometricScalar h a w ≤
      -weightedThird N a v (leftStripReflectedSlope p v) := by
  dsimp only
  rw [← endpointWeighted_eq_scalar hp (ha.trans_lt hav) hav]
  exact leftStrip_geometric_endpoint_le hp ha hav

/-- A positive scalar certificate over the integration strip implies the mixed
derivative sign of the original kernel. -/
theorem leftStrip_logKernel_mixed_lt_of_geometric_scalar {p : ℕ} (hp : 11 ≤ p)
    {u v : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1 / 2) (huv : u < v)
    (hscalar : ∀ a ∈ Ioo 0 u, 0 < leftStripGeometricScalar (spacing p) a (v - a)) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 := by
  have hp₀ : 0 < p := by omega
  refine leftStrip_logKernel_mixed_lt_of_weighted hp₀ hu huv
    (leftStrip_small_slope hp hu hu₁) ?_
  dsimp only
  intro a ha
  have hav := ha.2.trans huv
  have hV := negativeMarginalFactor_pos hp₀ (hu.trans huv)
  have hh := spacing_pos hp₀
  have hfv : 0 < f (spacing p) v := by simp only [f, geometricProfile, geometricScale]; positivity
  have hfw : 0 < f (spacing p) (v-a) := by
    simp only [f, geometricProfile, geometricScale]
    positivity
  have hpos := mul_pos (div_pos (mul_pos hfv hfw) (mul_pos zero_lt_two hV)) (hscalar a ha)
  exact neg_pos.mp (hpos.trans_le (leftStrip_geometric_scalar_le hp₀ ha.1.le hav))

#print axioms leftStripGeometricG_zero
#print axioms leftStrip_geometric_endpoint_difference
#print axioms leftStrip_geometric_endpoint_le
#print axioms leftStrip_geometric_scalar_le
#print axioms leftStrip_logKernel_mixed_lt_of_geometric_scalar

end RefinedBMV.PositiveCenter
