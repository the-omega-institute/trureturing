/- GID: D5/S3/Quantum/Analysis/RefinedBMVPositiveCenterTailJet
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Mixed partial derivatives under the change to the upper spectral gap. -/

import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterMixedJet
import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterTailFormula
import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterTailMarginal
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.FunProp

/-! # Derivatives under the upper spectral gap change of variables -/

open Filter
open scoped Topology

namespace RefinedBMV.PositiveCenter

/-- Derivatives of a function of the lower coordinate and the gap,
reported in the independent lower and upper coordinates. -/
noncomputable def upperGapJet (F : ℝ → ℝ → ℝ) (u v : ℝ) : MixedJet ℝ :=
  let d := v-u
  ⟨F u d, deriv (fun x ↦ F x d) u - deriv (F u) d,
    deriv (F u) d, deriv (fun x ↦ deriv (F x) d) u - deriv (deriv (F u)) d⟩

theorem upperGapJet_isAt {F : ℝ → ℝ → ℝ} {u v : ℝ}
    (h : ContDiffAt ℝ 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (u,v-u)) :
    MixedJet.IsAt (upperGapJet F) u v := by
  let G : ℝ × ℝ → ℝ := fun z ↦ F z.1 z.2
  let d := v-u
  let e₁ : ℝ × ℝ := (1,0)
  let e₂ : ℝ × ℝ := (0,1)
  let D := fderiv ℝ G
  let H := fderiv ℝ D (u,d)
  have hG : ContDiffAt ℝ 2 G (u,d) := h
  have hC : ContDiffAt ℝ 1 D (u,d) := hG.fderiv_right (by norm_num)
  have hH : HasFDerivAt D H (u,d) := hC.differentiableAt_one.hasFDerivAt
  have hsym : IsSymmSndFDerivAt ℝ G (u,d) :=
    hG.isSymmSndFDerivAt (by simp)
  have hdx (x y : ℝ) : HasDerivAt (fun t : ℝ ↦ (t,y)) e₁ x :=
    (hasDerivAt_id' x).prodMk (hasDerivAt_const x y)
  have hdy (x y : ℝ) : HasDerivAt (fun t : ℝ ↦ (x,t)) e₂ y :=
    (hasDerivAt_const y x).prodMk (hasDerivAt_id' y)
  have hdiag (x y : ℝ) : HasDerivAt (fun t : ℝ ↦ (t,y-t)) (e₁-e₂) x := by
    have hd := (hasDerivAt_id' x).prodMk ((hasDerivAt_const x y).fun_sub (hasDerivAt_id' x))
    simpa only [sub_zero, zero_sub, e₁, e₂, Prod.mk_sub_mk] using hd
  have hfixed (x y : ℝ) : HasDerivAt (fun t : ℝ ↦ (x,t-x)) e₂ y :=
    (hasDerivAt_const y x).prodMk ((hasDerivAt_id' y).sub_const x)
  have hfirst {x y : ℝ} (hg : ContDiffAt ℝ 2 G (x,y)) :
      HasDerivAt (fun t ↦ F t y) (D (x,y) e₁) x := by
    have hd := (hg.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt x (hdx x y)
    change HasDerivAt (fun t ↦ F t y) (D (x,y) e₁) x at hd
    exact hd
  have hsecond {x y : ℝ} (hg : ContDiffAt ℝ 2 G (x,y)) :
      HasDerivAt (F x) (D (x,y) e₂) y :=
    (hg.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt y (hdy x y)
  have hevY : ∀ᶠ y in nhds v, ContDiffAt ℝ 2 G (u,y-u) :=
    (show Continuous (fun t : ℝ ↦ (u,t-u)) by fun_prop).continuousAt.eventually
      (hG.eventually (by simp))
  have hevD : ∀ᶠ y in nhds d, ContDiffAt ℝ 2 G (u,y) :=
    (show Continuous (fun t : ℝ ↦ (u,t)) by fun_prop).continuousAt.eventually
      (hG.eventually (by simp))
  have hevU : ∀ᶠ x in nhds u, ContDiffAt ℝ 2 G (x,d) :=
    (show Continuous (fun t : ℝ ↦ (t,d)) by fun_prop).continuousAt.eventually
      (hG.eventually (by simp))
  have eval {f : ℝ → (ℝ × ℝ →L[ℝ] ℝ)} {f' : ℝ × ℝ →L[ℝ] ℝ} {x : ℝ}
      (hf : HasDerivAt f f' x) (e : ℝ × ℝ) :
      HasDerivAt (fun t ↦ f t e) (f' e) x := by
    simpa only [map_zero, add_zero] using hf.clm_apply (hasDerivAt_const x e)
  have hUD : deriv (fun x ↦ deriv (F x) d) u = H e₁ e₂ := by
    have heq : (fun x ↦ deriv (F x) d) =ᶠ[nhds u] fun x ↦ D (x,d) e₂ :=
      hevU.mono fun _ hx ↦ (hsecond hx).deriv
    exact ((eval (hH.comp_hasDerivAt u (hdx u d)) e₂).congr_of_eventuallyEq heq).deriv
  have hDD : deriv (deriv (F u)) d = H e₂ e₂ := by
    have heq : deriv (F u) =ᶠ[nhds d] fun t ↦ D (u,t) e₂ :=
      hevD.mono fun _ hx ↦ (hsecond hx).deriv
    exact ((eval (hH.comp_hasDerivAt d (hdy u d)) e₂).congr_of_eventuallyEq heq).deriv
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hevY] with y hy
    have hd := (hy.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt u (hdiag u y)
    refine hd.congr_deriv ?_
    change D (u,y-u) (e₁-e₂) = deriv (fun x ↦ F x (y-u)) u - deriv (F u) (y-u)
    rw [map_sub, (hfirst hy).deriv, (hsecond hy).deriv]
  · exact (hG.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt v (hfixed u v)
      |>.congr_deriv (hsecond hG).deriv.symm
  · have heq : (fun y ↦ (upperGapJet F u y).du) =ᶠ[nhds v]
        fun y ↦ D (u,y-u) (e₁-e₂) := by
      filter_upwards [hevY] with y hy
      change deriv (fun x ↦ F x (y-u)) u - deriv (F u) (y-u) = _
      rw [(hfirst hy).deriv, (hsecond hy).deriv, map_sub]
    have hm := eval (hH.comp_hasDerivAt v (hfixed u v)) (e₁-e₂)
    refine (hm.congr_of_eventuallyEq heq).congr_deriv ?_
    change H e₂ (e₁-e₂) = deriv (fun x ↦ deriv (F x) d) u - deriv (deriv (F u)) d
    rw [hUD, hDD, map_sub, hsym e₂ e₁]

private noncomputable def tailLowerFactor (p : ℕ) (u : ℝ) : ℝ :=
  Real.exp u*(1-Real.exp (-u))^2/Real.sqrt (compositionMoment p 0 (-u))

private noncomputable def tailRightFactor (h v : ℝ) : ℝ :=
  Real.exp (-v/2)/Real.sqrt (1-Real.exp (-(h*v)))

private noncomputable def tailLowerSlope (p : ℕ) (u : ℝ) : ℝ :=
  1 + 2/(Real.exp u-1) -
    (deriv (fun s ↦ compositionMoment p 0 (-s)) u/compositionMoment p 0 (-u))/2

private theorem hasDerivAt_tailDecay (c t : ℝ) :
    HasDerivAt (fun s ↦ Real.exp (-(c*s))) (-c*Real.exp (-(c*t))) t := by
  have h : HasDerivAt (fun s : ℝ ↦ -(c*s)) (-c) t := by
    have hd := ((hasDerivAt_id' t).const_mul c).neg
    change HasDerivAt (fun s : ℝ ↦ -(c*s)) (-(c*1)) t at hd
    simpa only [mul_one] using hd
  simpa only [mul_comm] using h.exp

private theorem hasDerivAt_tailBeta {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    let β : ℝ → ℝ := fun t ↦ 1-Real.exp (-(h*t))
    HasDerivAt β (upperTailSlope h t*β t) t := by
  let β : ℝ → ℝ := fun t ↦ 1-Real.exp (-(h*t))
  have he : 0 < Real.exp (h*t)-1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr (mul_pos hh ht))
  have hd := (hasDerivAt_const t (1 : ℝ)).fun_sub (hasDerivAt_tailDecay h t)
  refine hd.congr_deriv ?_
  change 0-(-h*Real.exp (-(h*t))) = upperTailSlope h t*β t
  dsimp [upperTailSlope, β]
  rw [Real.exp_neg]
  field_simp [(Real.exp_pos (h*t)).ne', he.ne']
  ring

private theorem tailLowerFactor_derivative {p : ℕ} (hp : 0 < p) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (tailLowerFactor p) (tailLowerSlope p u*tailLowerFactor p u) u := by
  let C : ℝ → ℝ := fun x ↦ compositionMoment p 0 (-x)
  let ell : ℝ → ℝ := fun x ↦ 1-Real.exp (-x)
  let G := SmallCorner.G p 1
  have hId (x : ℝ) (hx : x ≠ 0) : C x = x^2*G (-x) := by
    unfold C G SmallCorner.G
    field_simp [hx]
  have hC : 0 < C u := by
    rw [hId u hu.ne']
    exact mul_pos (sq_pos_of_pos hu)
      (SmallCorner.G_pos hp (by norm_num : (0 : ℝ) < 1) (neg_ne_zero.mpr hu.ne'))
  have hCg : HasDerivAt C (deriv C u) u := by
    have hL : C =ᶠ[𝓝 u] (fun x ↦ x^2*G (-x)) :=
      (eventually_ne_nhds hu.ne').mono hId
    have hG := SmallCorner.hasDerivAt_G p one_ne_zero (neg_ne_zero.mpr hu.ne')
    have hg : DifferentiableAt ℝ (fun x ↦ G (-x)) u :=
      (hG.comp u (HasDerivAt.neg (hasDerivAt_id' u))).differentiableAt
    have hfun : DifferentiableAt ℝ (fun x ↦ x^2*G (-x)) u :=
      (hasDerivAt_pow 2 u).differentiableAt.fun_mul hg
    exact (hfun.congr_of_eventuallyEq hL).hasDerivAt
  have hℓ : 0 < ell u := sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hu))
  have hE : 0 < Real.exp u-1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hu)
  have hR : Real.exp (-u)/ell u = 1/(Real.exp u-1) := by
    unfold ell
    rw [Real.exp_neg]
    field_simp [hℓ.ne', hE.ne', (Real.exp_pos u).ne']
  have hℓd : HasDerivAt ell (Real.exp (-u)) u := by
    simpa only [zero_sub, neg_mul, one_mul, neg_neg, ell] using
      (hasDerivAt_const u (1 : ℝ)).fun_sub (hasDerivAt_tailDecay 1 u)
  have hℓsq : HasDerivAt (fun x ↦ (ell x)^2) ((2/(Real.exp u-1))*(ell u)^2) u := by
    have h := hℓd.pow 2
    change HasDerivAt (fun x ↦ (ell x)^2) _ u at h
    refine h.congr_deriv ?_
    simp only [Nat.reduceSub, Nat.cast_ofNat, pow_one]
    rw [show 2/(Real.exp u-1) = 2*(1/(Real.exp u-1)) by ring, ← hR]
    field_simp [hℓ.ne']
  have hs : 0 < Real.sqrt (C u) := Real.sqrt_pos.mpr hC
  have hInv : HasDerivAt (fun x ↦ (Real.sqrt (C x))⁻¹)
      (-(deriv C u/C u)/2*(Real.sqrt (C u))⁻¹) u := by
    have hd := (hCg.sqrt hC.ne').inv hs.ne'
    refine hd.congr_deriv ?_
    rw [← Real.sq_sqrt hC.le]
    simp only [Real.sqrt_sq hs.le]
    field_simp [hs.ne']
  have h := (((Real.hasDerivAt_exp u).mul hℓsq).mul hInv)
  have hfun : (fun x ↦ Real.exp x*(ell x)^2*(Real.sqrt (C x))⁻¹) = tailLowerFactor p := by
    funext x
    rfl
  change HasDerivAt (fun x ↦ Real.exp x*(ell x)^2*(Real.sqrt (C x))⁻¹) _ u at h
  rw [hfun] at h
  apply h.congr_deriv
  change _ = (1 + 2/(Real.exp u-1) - (deriv C u/C u)/2) *
    (Real.exp u*(ell u)^2*(Real.sqrt (C u))⁻¹)
  simp only [Pi.mul_apply]
  ring

private theorem tailRightFactor_derivative {h v : ℝ} (hh : 0 < h) (hv : 0 < v) :
    HasDerivAt (tailRightFactor h) ((-1/2-upperTailSlope h v/2)*tailRightFactor h v) v := by
  let α : ℝ → ℝ := fun s ↦ 1-Real.exp (-(h*s))
  let L := upperTailSlope h v
  have hα : 0 < α v := sub_pos.mpr
    (Real.exp_lt_one_iff.mpr (neg_neg_of_pos (mul_pos hh hv)))
  have hαd : HasDerivAt α (L*α v) v := hasDerivAt_tailBeta hh hv
  have hs : 0 < Real.sqrt (α v) := Real.sqrt_pos.mpr hα
  have hInv : HasDerivAt (fun s ↦ (Real.sqrt (α s))⁻¹)
      (-(L/2)*(Real.sqrt (α v))⁻¹) v := by
    have hd := (hαd.sqrt hα.ne').inv hs.ne'
    refine hd.congr_deriv ?_
    rw [← Real.sq_sqrt hα.le]
    simp only [Real.sqrt_sq hs.le]
    field_simp [hs.ne']
  have he : HasDerivAt (fun s : ℝ ↦ Real.exp (-s/2)) ((-1/2)*Real.exp (-v/2)) v := by
    have hEq (t : ℝ) : -((1/2 : ℝ)*t) = -t/2 := by ring
    simpa only [hEq, neg_div] using hasDerivAt_tailDecay (1/2) v
  have h := he.mul hInv
  change HasDerivAt (fun s : ℝ ↦ Real.exp (-s/2)*(Real.sqrt (α s))⁻¹) _ v at h
  apply h.congr_deriv
  change _ = (-1/2-L/2)*(Real.exp (-v/2)*(Real.sqrt (α v))⁻¹)
  ring

private noncomputable def tailBaseJet (p : ℕ) (u v : ℝ) : MixedJet ℝ :=
  let h : ℝ := 3/(p : ℝ)
  let d := v-u
  let T := upperTailBaseFactor p u d
  let l := tailLowerSlope p u - upperTailSlope h d
  let w := -1/2 + upperTailSlope h d - upperTailSlope h v/2
  ⟨T, T*l, T*w, T*(w*l - deriv (upperTailSlope h) d)⟩

private theorem tailBaseJet_isAt {p : ℕ} (hp : 0 < p) {u v : ℝ}
    (hu : 0 < u) (huv : u < v) : MixedJet.IsAt (tailBaseJet p) u v := by
  let h : ℝ := 3/(p : ℝ)
  let β : ℝ → ℝ := fun t ↦ 1-Real.exp (-(h*t))
  let P := tailLowerFactor p
  let Q := tailRightFactor h
  let T : ℝ → ℝ → ℝ := fun x y ↦ upperTailBaseFactor p x (y-x)
  let L := upperTailSlope h
  let b := tailLowerSlope p u
  let d := v-u
  let k : ℝ := Real.sqrt (((p+2).choose 2 : ℝ)/(p+1))/2
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hh : 0 < h := by dsimp [h]; positivity
  have hv : 0 < v := hu.trans huv
  have hd : 0 < d := sub_pos.mpr huv
  have hT (x y : ℝ) : T x y = k*P x*β (y-x)*Q y := by
    dsimp [T, upperTailBaseFactor, P, Q, tailLowerFactor, tailRightFactor, β]
    rw [sub_add_cancel]
    have he : Real.exp (-(y-x)/2)*Real.exp (x/2) = Real.exp x*Real.exp (-y/2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    change k*Real.exp (-(y-x)/2)*
      ((1-Real.exp (-(h*(y-x))))/Real.sqrt (1-Real.exp (-(h*y))))*
      ((Real.exp (x/2)*(1-Real.exp (-x))^2)/Real.sqrt (compositionMoment p 0 (-x))) =
      k*(Real.exp x*(1-Real.exp (-x))^2/Real.sqrt (compositionMoment p 0 (-x)))*
        (1-Real.exp (-(h*(y-x))))*(Real.exp (-y/2)/Real.sqrt (1-Real.exp (-(h*y))))
    rw [show
      k*Real.exp (-(y-x)/2)*
        ((1-Real.exp (-(h*(y-x))))/Real.sqrt (1-Real.exp (-(h*y))))*
        ((Real.exp (x/2)*(1-Real.exp (-x))^2)/Real.sqrt (compositionMoment p 0 (-x))) =
      (Real.exp (-(y-x)/2)*Real.exp (x/2))*
        (k*((1-Real.exp (-(h*(y-x))))/Real.sqrt (1-Real.exp (-(h*y))))*
        ((1-Real.exp (-x))^2/Real.sqrt (compositionMoment p 0 (-x)))) by ring,
      he]
    ring
  have hU {y : ℝ} (hy : u < y) : HasDerivAt (fun x ↦ T x y) (T u y*(b-L (y-u))) u := by
    have hBeta := (hasDerivAt_tailBeta hh (sub_pos.mpr hy)).comp u
      ((hasDerivAt_const u y).fun_sub (hasDerivAt_id' u))
    change HasDerivAt (fun x ↦ β (y-x)) _ u at hBeta
    have hD := (((tailLowerFactor_derivative hp hu).const_mul k).mul hBeta).mul_const (Q y)
    have heq : (fun x ↦ T x y) =ᶠ[𝓝 u] fun x ↦ k*P x*β (y-x)*Q y :=
      Eventually.of_forall fun x ↦ hT x y
    apply (hD.congr_of_eventuallyEq heq).congr_deriv
    rw [hT]
    change (k*(b*P u)*β (y-u) + k*P u*((L (y-u)*β (y-u))*(0-1)))*Q y =
      (k*P u*β (y-u)*Q y)*(b-L (y-u))
    ring
  have hV : HasDerivAt (T u) (T u v*(-1/2+L d-L v/2)) v := by
    have hBeta := (hasDerivAt_tailBeta hh hd).comp v ((hasDerivAt_id' v).sub_const u)
    change HasDerivAt (fun t ↦ β (t-u)) _ v at hBeta
    have hD := (hBeta.const_mul (k*P u)).mul (tailRightFactor_derivative hh hv)
    have heq : T u =ᶠ[𝓝 v] fun y ↦ k*P u*β (y-u)*Q y :=
      Eventually.of_forall fun y ↦ hT u y
    apply (hD.congr_of_eventuallyEq heq).congr_deriv
    rw [hT]
    change (k*P u*((L d*β d)*1)*Q v + k*P u*β d*((-1/2-L v/2)*Q v)) =
      (k*P u*β d*Q v)*(-1/2+L d-L v/2)
    ring
  have hL : HasDerivAt L (deriv L d) d :=
    (hasDerivAt_upperTailSlope hh hd).differentiableAt.hasDerivAt
  have hL' := hL.comp v ((hasDerivAt_id' v).sub_const u)
  change HasDerivAt (fun y ↦ L (y-u)) _ v at hL'
  refine ⟨?_, hV, ?_⟩
  · exact (eventually_gt_nhds huv).mono fun _ hy ↦ hU hy
  · have h' := hV.mul ((hasDerivAt_const v b).fun_sub hL')
    change HasDerivAt (fun y ↦ (tailBaseJet p u y).du) _ v at h'
    refine h'.congr_deriv ?_
    change T u v*(-1/2+L d-L v/2)*(b-L d) + T u v*(0-deriv L d*1) =
      T u v*((-1/2+L d-L v/2)*(b-L d)-deriv L d)
    ring

private theorem tailGap_positive {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    0 < upperTailGap h t :=
  div_pos (sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos (mul_pos hh ht)))) hh

private theorem tailLinear_smooth {h u d : ℝ} (hh : 0 < h) (hu : 0 < u) (hd : 0 < d) :
    ContDiffAt ℝ 2 (fun z : ℝ × ℝ ↦ upperTailLinearError h z.1 z.2) (u,d) := by
  have h₁ : ContDiffAt ℝ 2 (fun z : ℝ × ℝ ↦ upperTailGap h z.1) (u,d) := by
    unfold upperTailGap
    fun_prop
  have h₂ : ContDiffAt ℝ 2 (fun z : ℝ × ℝ ↦ upperTailGap h z.2) (u,d) := by
    unfold upperTailGap
    fun_prop
  have hz : (1-Real.exp (-u)) ≠ 0 :=
    (sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hu))).ne'
  have hp₀ : ContDiffAt ℝ 2 (fun z : ℝ × ℝ ↦ upperTailLinearP0 h z.1) (u,d) := by
    unfold upperTailLinearP0 upperTailLinearA
    apply ContDiffAt.div (by fun_prop) (by fun_prop)
    exact pow_ne_zero _ hz
  have hp₁ : ContDiffAt ℝ 2 (fun z : ℝ × ℝ ↦ upperTailLinearP1 h z.1) (u,d) := by
    unfold upperTailLinearP1 upperTailLinearA1
    have hdiv : ContDiffAt ℝ 2
        (fun z : ℝ × ℝ ↦ (1-Real.exp (-((3+2*h)*z.1)))/upperTailGap h z.1) (u,d) :=
      (show ContDiffAt ℝ 2 (fun z : ℝ × ℝ ↦ 1-Real.exp (-((3+2*h)*z.1))) (u,d)
        by fun_prop).div h₁ (tailGap_positive hh hu).ne'
    exact ContDiffAt.div (by fun_prop) (by fun_prop) (pow_ne_zero _ hz)
  have hW (n : ℕ) : ContDiffAt ℝ 2 (fun z : ℝ × ℝ ↦ upperTailLinearW h n z.2) (u,d) := by
    unfold upperTailLinearW
    exact ContDiffAt.div (by fun_prop) (h₂.pow n) (pow_ne_zero _ (tailGap_positive hh hd).ne')
  have hc : ((3+h)*(3+2*h)/2 : ℝ) ≠ 0 := by positivity
  unfold upperTailLinearError
  exact ((hp₀.neg.mul (hW 2)).add (hp₁.mul (hW 1))).div contDiffAt_const hc

private theorem tailQuadratic_smooth {h u d : ℝ} (hh : 0 < h) (hhmax : h ≤ 3/11)
    (hu : 0 < u) (hd : 11 ≤ d) :
    ContDiffAt ℝ 2 (fun z : ℝ × ℝ ↦ upperTailQuadratic h z.1 z.2) (u,d) := by
  have hz : (1-Real.exp (-u)) ≠ 0 :=
    (sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hu))).ne'
  have hr {t : ℝ} (ht : 11 ≤ t) : 1-upperTailLambda h t ≠ 0 :=
    (Real.sqrt_pos.mp ((by norm_num : (0 : ℝ) < 3/4).trans_le
      (upperTail_radical_lower hh hhmax ht))).ne'
  have hd' : 11 ≤ d+u := by linarith
  have h₁ : ContDiffAt ℝ 2 (fun z : ℝ × ℝ ↦ 1-upperTailLambda h (z.2+z.1)) (u,d) := by
    unfold upperTailLambda upperTailGap
    fun_prop
  have h₂ : ContDiffAt ℝ 2 (fun z : ℝ × ℝ ↦ 1-upperTailLambda h z.2) (u,d) := by
    unfold upperTailLambda upperTailGap
    fun_prop
  have hT : ContDiffAt ℝ 2 (fun z : ℝ × ℝ ↦ upperTailRootDifference h z.1 z.2) (u,d) :=
    ((h₁.sqrt (hr hd')).sub (h₂.sqrt (hr hd))).div (by fun_prop) hz
  have hX : ContDiffAt ℝ 2 (fun z : ℝ × ℝ ↦
      ((3+h)*(3+2*h)/2)*(upperTailGap h z.2)^2*Real.exp (-(2*z.2))) (u,d) := by
    unfold upperTailGap
    fun_prop
  have hx : ((3+h)*(3+2*h)/2)*(upperTailGap h d)^2*Real.exp (-(2*d)) ≠ 0 := by
    have ha := tailGap_positive hh (show 0 < d by linarith)
    positivity
  exact (hT.pow 2).mul (hX.inv hx)

private theorem tailCorrection_smooth {h u d : ℝ} (hh : 0 < h) (hu : 0 < u) (hd : 0 < d) :
    ContDiffAt ℝ 2 (fun z : ℝ × ℝ ↦ 1 -
      upperTailSlope h z.2*upperTailRatio h z.1) (u,d) := by
  have hL : ContDiffAt ℝ 2 (fun z : ℝ × ℝ ↦ upperTailSlope h z.2) (u,d) := by
    unfold upperTailSlope
    exact contDiffAt_const.div (by fun_prop)
      (sub_pos.mpr (Real.one_lt_exp_iff.mpr (mul_pos hh hd))).ne'
  have hR : ContDiffAt ℝ 2 (fun z : ℝ × ℝ ↦ upperTailRatio h z.1) (u,d) := by
    unfold upperTailRatio upperTailGap
    exact ContDiffAt.div (by fun_prop) (by fun_prop)
      (sub_pos.mpr (Real.one_lt_exp_iff.mpr hu)).ne'
  exact contDiffAt_const.sub (hL.mul hR)

private theorem tailCorrection_jet {h u v : ℝ} (hh : 0 < h) (hu : 0 < u) (huv : u < v) :
    let d := v-u
    let L := upperTailSlope h d
    let L₁ := deriv (upperTailSlope h) d
    let L₂ := deriv (deriv (upperTailSlope h)) d
    let f := upperTailRatio h u
    let f₁ := deriv (upperTailRatio h) u
    upperGapJet (fun x y ↦ 1-upperTailSlope h y*upperTailRatio h x) u v =
      ⟨1-L*f, -L*f₁+L₁*f, -L₁*f, -L₁*f₁+L₂*f⟩ := by
  let d := v-u
  let L := upperTailSlope h
  let f := upperTailRatio h
  have hd : 0 < d := sub_pos.mpr huv
  have hL : ∀ t, 0 < t → ContDiffAt ℝ 2 L t := by
    intro t ht
    unfold L upperTailSlope
    exact contDiffAt_const.div (by fun_prop)
      (sub_pos.mpr (Real.one_lt_exp_iff.mpr (mul_pos hh ht))).ne'
  have hf : DifferentiableAt ℝ f u := by
    unfold f upperTailRatio upperTailGap
    exact DifferentiableAt.fun_div (by fun_prop) (by fun_prop)
      (sub_pos.mpr (Real.one_lt_exp_iff.mpr hu)).ne'
  have hX : deriv (fun x ↦ 1-L d*f x) u = -L d*deriv f u := by
    have hh := ((hasDerivAt_const u (1 : ℝ)).fun_sub (hf.hasDerivAt.const_mul (L d))).deriv
    rw [hh, zero_sub, neg_mul]
  have hY (x t : ℝ) (ht : 0 < t) :
      deriv (fun y ↦ 1-L y*f x) t = -deriv L t*f x := by
    have h := ((hasDerivAt_const t (1 : ℝ)).fun_sub
      ((((hL t ht).differentiableAt (by norm_num)).hasDerivAt).mul_const (f x))).deriv
    rw [h, zero_sub, neg_mul]
  have hm : deriv (fun x ↦ deriv (fun y ↦ 1-L y*f x) d) u = -deriv L d*deriv f u := by
    simp_rw [hY _ _ hd]
    exact (hf.hasDerivAt.const_mul _).deriv
  have hdd : deriv (deriv (fun y ↦ 1-L y*f u)) d = -deriv (deriv L) d*f u := by
    have heq : deriv (fun y ↦ 1-L y*f u) =ᶠ[𝓝 d] fun t ↦ -deriv L t*f u :=
      (eventually_gt_nhds hd).mono fun t ht ↦ hY u t ht
    rw [heq.deriv_eq]
    have h := ((hL d hd).derivWithin (m := 1) (by norm_num)).differentiableAt_one.hasDerivAt
    exact ((HasDerivAt.neg h).mul_const _).deriv
  change (⟨1-L d*f u, _, _, _⟩ : MixedJet ℝ) = _
  rw [hX, hY _ _ hd, hm, hdd]
  congr 1 <;> ring

/-- The upper-tail region with a strict cutoff is open, so the exact
normalized kernel formula can be differentiated in both coordinates. -/
theorem logKernel_upperTail_mixed_lt {p : ℕ} (hp : 11 ≤ p) {u v : ℝ}
    (hu : 0 < u) (hgap : 11 < v-u) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 := by
  let h : ℝ := 3/(p : ℝ)
  let d := v-u
  let n : ℝ := p+1
  let N : ℝ := (p+2).choose 2
  let A := upperTailNormalizer (p+1) h (N/n)
  let S : ℝ → ℝ := fun y ↦ 1/Real.sqrt (A y)
  let R : ℝ → ℝ → ℝ := fun x y ↦ 1-upperTailSlope h y*upperTailRatio h x
  let E := upperTailLinearError h
  let Q := upperTailQuadratic h
  let evalE := upperGapJet E
  let evalQ := upperGapJet Q
  let evalR := upperGapJet R
  let J : ℝ → ℝ → MixedJet ℝ := fun x y ↦
    (tailBaseJet p x y).mul (((evalR x y).mul (evalR x y)).add
      ((evalE x y).add (evalQ x y)))
  have hp₀ : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp₀
  have hple : (11 : ℝ) ≤ p := by exact_mod_cast hp
  have hh : 0 < h := by dsimp [h]; positivity
  have hhmax : h ≤ 3/11 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hple
  have hd : 11 ≤ d := hgap.le
  have hd₀ : 0 < d := by linarith
  have huv : u < v := by dsimp [d] at hd₀; linarith
  have hv : 0 < v := hu.trans huv
  have hv₁ : 1 ≤ v := by dsimp [d] at hd; linarith
  have hn : 0 < n := by dsimp [n]; positivity
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast (Nat.choose_pos (show 2 ≤ p+2 by omega))
  have hgap' : ∀ t : ℝ, 0 < t → 0 < 1-Real.exp (-(h*t)) := fun t ht ↦
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos (mul_pos hh ht)))
  have ha : Real.exp (-v/(p : ℝ)) < 1 :=
    Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (neg_lt_zero.mpr hv) hpR)
  have hA : 0 < A v := by
    have ha₀ : (0 : ℝ) ≤ Real.exp (-v/(p : ℝ)) := (Real.exp_pos _).le
    have hw := upperTail_upper_weight hp₀ hv
    have hgap : 0 < 1-(Real.exp (-v/(p : ℝ)))^3 := by
      exact sub_pos.mpr (by nlinarith [pow_lt_pow_left₀ ha ha₀ (by decide : 3 ≠ 0)])
    have hp := mul_pos hgap (weight_pos hp₀ ha₀ ha)
    rw [hw] at hp
    exact (mul_pos_iff_of_pos_left hn).mp hp
  have hBase : 0 < upperTailBaseFactor p u d := by
    have hC : 0 < compositionMoment p 0 (-u) := by
      let G := SmallCorner.G p 1
      have hId : compositionMoment p 0 (-u) = u^2*G (-u) := by
        unfold G SmallCorner.G
        field_simp [hu.ne']
      rw [hId]
      exact mul_pos (sq_pos_of_pos hu)
        (SmallCorner.G_pos hp₀ (by norm_num : (0 : ℝ) < 1) (neg_ne_zero.mpr hu.ne'))
    have hell := sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hu))
    unfold upperTailBaseFactor
    change 0 < Real.sqrt (N/n)/2*Real.exp (-d/2)*
      ((1-Real.exp (-(h*d)))/Real.sqrt (1-Real.exp (-(h*(d+u)))))*
        (Real.exp (u/2)*(1-Real.exp (-u))^2/Real.sqrt (compositionMoment p 0 (-u)))
    have ha := hgap' (d+u) (by positivity)
    have hb := hgap' d hd₀
    positivity
  have hEJ : MixedJet.IsAt evalE u v := upperGapJet_isAt (tailLinear_smooth hh hu hd₀)
  have hQJ : MixedJet.IsAt evalQ u v := upperGapJet_isAt (tailQuadratic_smooth hh hhmax hu hd)
  have hRJ : MixedJet.IsAt evalR u v := upperGapJet_isAt (tailCorrection_smooth hh hu hd₀)
  have hJ : MixedJet.IsAt J u v := (tailBaseJet_isAt hp₀ hu huv).mul
    ((hRJ.mul hRJ).add (hEJ.add hQJ))
  obtain ⟨he, heu, hed, heud, hedd⟩ := upperTailLinearError_bounds hh hhmax hu hd
  obtain ⟨hq, hqu, hqd, hqud, hqdd⟩ := upperTail_quadratic_bounds hh hhmax hu hd
  let X := ((3+h)*(3+2*h)/2)*(upperTailGap h d)^2*Real.exp (-(2*d))
  let B := (26/3)*Real.exp (-d) + 190*X
  have hX₀ : 0 ≤ X := by dsimp [X]; positivity
  have hbudget : B < 1/200 := by
    let a := upperTailGap h d
    let U := a^2*Real.exp (-(2*d))
    let c : ℝ := (3+h)*(3+2*h)/2
    have hc : c ≤ 6 := by
      have hm := mul_le_mul_of_nonneg_left hhmax hh.le
      dsimp [c]
      nlinarith only [hm, hhmax]
    have ha : 0 ≤ a := (tailGap_positive hh hd₀).le
    have hU : 0 ≤ U := by dsimp [U]; positivity
    have hX : X = c*U := by dsimp [X, c, U, a]; ring
    have hx : X ≤ 6*U := hX.trans_le (mul_le_mul_of_nonneg_right hc hU)
    have hb : 200*Real.exp (-d) + 10000*U < 1/200 := by
      simpa only [U, neg_mul] using upperTail_remainder_budget hd ha (upperTailGap_le hh)
    dsimp only [B]
    linarith only [hx, hb, hU, Real.exp_pos (-d)]
  let e := E u d + Q u d
  let eu := deriv (fun t ↦ E t d) u + deriv (fun t ↦ Q t d) u
  let ed := deriv (E u) d + deriv (Q u) d
  let eud := deriv (fun t ↦ deriv (E t) d) u + deriv (fun t ↦ deriv (Q t) d) u
  let edd := deriv (deriv (E u)) d + deriv (deriv (Q u)) d
  have hsum {a b k : ℝ} (ha : |a| ≤ (26/3)*Real.exp (-d)) (hb : |b| ≤ k*X)
      (hk : k ≤ 190) : |a+b| ≤ 1/200 := by
    have h := (abs_add_le a b).trans (add_le_add ha (hb.trans
      (mul_le_mul_of_nonneg_right hk hX₀)))
    exact h.trans hbudget.le
  have he' : |e| ≤ 1/200 := hsum he hq (by norm_num)
  have heu' : |eu| ≤ 1/200 := hsum heu hqu (by norm_num)
  have hed' : |ed| ≤ 1/200 := hsum hed hqd (by norm_num)
  have heud' : |eud| ≤ 1/200 := by
    change |deriv (fun t ↦ deriv (E t) d) u + deriv (fun t ↦ deriv (Q t) d) u| ≤ 1/200
    rw [← upperTailLinearError_mixed_commute hh hu hd₀]
    exact hsum heud hqud (by norm_num)
  have hedd' : |edd| ≤ 1/200 := hsum hedd hqdd le_rfl
  have hRJ' := tailCorrection_jet hh hu huv
  have hEJ' : (evalE u v).add (evalQ u v) = ⟨e, eu-ed, ed, eud-edd⟩ := by
    unfold evalE evalQ upperGapJet
    dsimp only [MixedJet.add, e, eu, ed, eud, edd]
    congr 1 <;> ring
  let L := upperTailSlope h d
  let L₁ := deriv (upperTailSlope h) d
  let w := -1/2+L-upperTailSlope h v/2
  let l := tailLowerSlope p u-L
  let B₀ := upperTailBaseFactor p u d
  let K : MixedJet ℝ := ⟨1,l,w,w*l-L₁⟩
  let W := ((evalR u v).mul (evalR u v)).add ((evalE u v).add (evalQ u v))
  have hs := upperTail_normalized_sign hh hhmax hu hd
    (upperTail_marginal_scale hp₀ hu) he' heu' hed' heud' hedd'
  have hv' : u+d = v := by dsimp [d]; ring
  dsimp only at hs
  rw [hv', ← hEJ', ← hRJ'] at hs
  change 0 < (K.mul W).du ∧ (K.mul W).duv < 0 at hs
  have hJu : 0 ≤ (J u v).du := by
    have heq : (J u v).du = B₀*(K.mul W).du := by
      dsimp [J, tailBaseJet, K, W, B₀, l, d, L, w]
      simp only [MixedJet.mul]
      ring
    rw [heq]
    exact (mul_pos hBase hs.1).le
  have hJuv : (J u v).duv < 0 := by
    have heq : (J u v).duv = B₀*(K.mul W).duv := by
      dsimp [J, tailBaseJet, K, W, B₀, l, d, L, L₁, w]
      simp only [MixedJet.mul]
      ring
    rw [heq]
    exact mul_neg_of_pos_of_neg hBase hs.2
  obtain ⟨s', hs'₀, hs'⟩ := upperTail_normalizer_invSqrt hh
    (div_nonneg hN.le hn.le) hv₁ hA
  have hsign := upperTail_restore_upperFactor hJ hs'
    (one_div_pos.mpr (Real.sqrt_pos.mpr hA)) hs'₀ hJu hJuv
  have hLocal : (fun y ↦ deriv (fun x ↦ logKernel p x y) u) =ᶠ[𝓝 v]
      fun y ↦ deriv (fun x ↦ S y*(J x y).value) u := by
    have hv' : u+11 < v := by linarith
    filter_upwards [eventually_gt_nhds hv'] with y hy
    apply Filter.EventuallyEq.deriv_eq
    have hy' : u < y-11 := by linarith
    filter_upwards [eventually_gt_nhds hu, eventually_lt_nhds hy'] with x hx hxy
    have hgap : 11 ≤ y-x := by linarith
    have hk := upperTail_logKernel_decomposition hp hx hgap
    dsimp only at hk
    rw [sub_add_cancel y x] at hk
    change logKernel p x y = S y*(J x y).value
    rw [hk]
    dsimp [J, evalR, evalE, evalQ, upperGapJet, tailBaseJet, S, A, W, R, E, Q, h, n, N,
      MixedJet.mul, MixedJet.add]
    ring
  rwa [hLocal.deriv_eq]

#print axioms tailLowerFactor_derivative
#print axioms tailRightFactor_derivative
#print axioms tailBaseJet_isAt
#print axioms upperGapJet_isAt
#print axioms tailCorrection_jet
#print axioms logKernel_upperTail_mixed_lt

end RefinedBMV.PositiveCenter
