/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/LeftStripCollision
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Analytic identities for the continued left-strip collision integrand. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripKernel

/-! Analytic reduction near the left collision. -/

open Filter Set
open scoped Topology

noncomputable section

namespace RefinedBMV.PositiveCenter

open private compositionMoment_smooth weightedThird from D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripKernel

private theorem leftStrip_small_slope {p : ℕ} (hp : 11 ≤ p) {u : ℝ}
    (hu : 0 < u) (humax : u ≤ 1/2) :
    u * deriv (fun t ↦ Real.sqrt (compositionMoment p 0 (-t))) u ≤
      Real.sqrt (compositionMoment p 0 (-u)) := by
  let M (t : ℝ) := compositionMoment p 0 (-t)
  let D (t : ℝ) := Real.sqrt (M t)
  have hp₀ : 0 < p := by omega
  have hMpos (t : ℝ) (ht : 0 < t) : 0 < M t :=
    compositionMoment_marginal_pos hp₀ (neg_ne_zero.mpr ht.ne')
  have hMs : ContDiff ℝ 3 M :=
    (compositionMoment_smooth p).comp (contDiff_const.prodMk contDiff_id.neg :
      ContDiff ℝ 3 (fun t : ℝ ↦ ((0 : ℝ),-t)))
  have hM (t : ℝ) : HasDerivAt M (deriv M t) t := (hMs.differentiable (by decide) t).hasDerivAt
  have hD (t : ℝ) (ht : 0 < t) : HasDerivAt D (deriv M t/(2*D t)) t :=
    (hM t).sqrt (hMpos t ht).ne'
  have hDpos (t : ℝ) (ht : 0 < t) : 0 < D t := Real.sqrt_pos.mpr (hMpos t ht)
  have hDsq (t : ℝ) (ht : 0 < t) : D t^2 = M t := Real.sq_sqrt (hMpos t ht).le
  have hreg := (SmallCorner.hasDerivAt_G p (c := 1) one_ne_zero
    (neg_ne_zero.mpr hu.ne')).comp u (hasDerivAt_id' u).neg
  change HasDerivAt (fun t ↦ compositionMoment p 0 (-t)/(1*(-t)^2))
    (SmallCorner.GPrime p 1 (-u)*(-1)) u at hreg
  have hreg' : HasDerivAt (fun t ↦ M t/t^2) (-SmallCorner.GPrime p 1 (-u)) u := by
    simpa only [M, one_mul, neg_sq, mul_neg, mul_one] using hreg
  have hd := (hM u).fun_div (hasDerivAt_pow 2 u) (pow_ne_zero 2 hu.ne')
  have hcmp := hd.deriv.symm.trans hreg'.deriv
  have hnonpos : (deriv M u*u^2-M u*(↑(2 : ℕ)*u^(2-1)))/(u^2)^2 ≤ 0 := by
    rw [hcmp]
    exact neg_nonpos.mpr (leftStrip_GPrime_nonneg hp hu humax)
  have hcross := (div_le_iff₀ (sq_pos_of_ne_zero (pow_ne_zero 2 hu.ne'))).mp hnonpos
  norm_num at hcross
  have hbound : u*deriv M u ≤ 2*M u := by
    by_contra! hbad
    have hm := mul_pos hu (sub_pos.mpr hbad)
    nlinarith only [hcross,hm]
  rw [(hD u hu).deriv, ← mul_div_assoc,
    div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) (hDpos u hu))]
  nlinarith only [hbound,hDsq u hu]

private abbrev leftStripS (p : ℕ) (t : ℝ) := Real.sqrt (compositionMoment p 0 t)

private abbrev leftStripGap := ℕ × ℕ × ℕ

private def leftStripX (p : ℕ) (g : leftStripGap) : ℝ := 3 * (g.2.1 : ℝ) / p - 1

private def leftStripY (p : ℕ) (g : leftStripGap) : ℝ := 3 * (g.2.2 : ℝ) / p - 1

/-- The tilted joint moment with polynomial weight `X^i Y^j` under the
uniform law on the degree-`p` compositions. -/
private def leftStripExpMoment (p i j : ℕ) (a v : ℝ) : ℝ :=
  ((DimThree.gaps p).map fun g ↦ leftStripX p g ^ i * leftStripY p g ^ j *
    Real.exp (leftStripX p g * a + leftStripY p g * v)).sum / (DimThree.gaps p).length

private theorem leftStrip_hasDerivAt_exp_sum (l : List leftStripGap) (w A B : leftStripGap → ℝ)
    (t : ℝ) :
    HasDerivAt (fun x ↦ (l.map fun g ↦ w g * Real.exp (A g * x + B g)).sum)
      (l.map fun g ↦ (w g * A g) * Real.exp (A g * t + B g)).sum t := by
  induction l with
  | nil => simpa using hasDerivAt_const t (0 : ℝ)
  | cons g l ih =>
    have hg : HasDerivAt (fun x ↦ w g * Real.exp (A g * x + B g))
        ((w g * A g) * Real.exp (A g * t + B g)) t := by
      convert (((hasDerivAt_const_mul (A g)).add_const (B g)).exp.const_mul (w g)) using 1
      ring
    exact hg.add ih

private theorem leftStrip_hasDerivAt_expMoment_left (p i j : ℕ) (a v : ℝ) :
    HasDerivAt (leftStripExpMoment p i j · v) (leftStripExpMoment p (i+1) j a v) a := by
  have h := (leftStrip_hasDerivAt_exp_sum (DimThree.gaps p)
    (fun g ↦ leftStripX p g ^ i * leftStripY p g ^ j) (leftStripX p)
    (fun g ↦ leftStripY p g * v) a).div_const ((DimThree.gaps p).length : ℝ)
  simpa only [leftStripExpMoment, pow_succ, mul_right_comm] using h

private theorem leftStrip_hasDerivAt_expMoment_right (p i j : ℕ) (a v : ℝ) :
    HasDerivAt (leftStripExpMoment p i j a) (leftStripExpMoment p i (j+1) a v) v := by
  have h := (leftStrip_hasDerivAt_exp_sum (DimThree.gaps p)
    (fun g ↦ leftStripX p g ^ i * leftStripY p g ^ j) (leftStripY p)
    (fun g ↦ leftStripX p g * a) v).div_const ((DimThree.gaps p).length : ℝ)
  unfold leftStripExpMoment
  simpa only [pow_succ, mul_assoc, add_comm] using h

private theorem leftStrip_hasDerivAt_moment_left (p : ℕ) (a v : ℝ) :
    HasDerivAt (compositionMoment p · v) (leftStripExpMoment p 1 0 a v) a := by
  have h : ∀ t : ℝ, compositionMoment p t v = leftStripExpMoment p 0 0 t v - 1 := by
    intro t
    simp only [compositionMoment, leftStripExpMoment, pow_zero, mul_one, one_mul]
    rfl
  exact ((leftStrip_hasDerivAt_expMoment_left p 0 0 a v).sub_const 1).congr_of_eventuallyEq
    (Eventually.of_forall h)

/-- The second partial of the exact kernel numerator in its first coordinate. -/
private def leftStripE (p : ℕ) (a v : ℝ) : ℝ :=
  leftStripExpMoment p 2 0 a v - leftStripS p v * deriv (deriv (leftStripS p)) (v-a)

private theorem leftStrip_contDiffAt_S {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : t ≠ 0) :
    ContDiffAt ℝ 3 (leftStripS p) t := by
  have h := (compositionMoment_smooth p).comp
    (contDiff_const.prodMk contDiff_id : ContDiff ℝ 3 (fun t : ℝ ↦ ((0 : ℝ), t)))
  exact h.contDiffAt.sqrt (compositionMoment_marginal_pos hp ht).ne'

private theorem leftStrip_numerator_second_eq_E {p : ℕ} (hp : 0 < p) {a v : ℝ}
    (hv : 0 < v) (hav : a < v) :
    let N (x y : ℝ) := compositionMoment p x y -
      Real.sqrt (compositionMoment p 0 y * compositionMoment p 0 (y-x))
    deriv (deriv (N · v)) a = leftStripE p a v := by
  let S := leftStripS p
  have hN : ∀ x : ℝ, compositionMoment p x v -
      Real.sqrt (compositionMoment p 0 v * compositionMoment p 0 (v-x)) =
      compositionMoment p x v - S v * S (v-x) := by
    intro x
    rw [Real.sqrt_mul (compositionMoment_marginal_pos hp hv.ne').le]
  have hgap (x : ℝ) : HasDerivAt (fun t : ℝ ↦ v-t) (-1) x :=
    (hasDerivAt_id' x).const_sub v
  have hfirst : (fun x ↦ deriv (fun t ↦ compositionMoment p t v -
      Real.sqrt (compositionMoment p 0 v * compositionMoment p 0 (v-t))) x)
      =ᶠ[𝓝 a] fun x ↦ leftStripExpMoment p 1 0 x v + S v * deriv S (v-x) := by
    filter_upwards [eventually_lt_nhds hav] with x hx
    have hs := ((leftStrip_contDiffAt_S hp (sub_pos.mpr hx).ne').differentiableAt
      (by decide)).hasDerivAt
    have hd := (leftStrip_hasDerivAt_moment_left p x v).sub
      ((hs.comp x (hgap x)).const_mul (S v))
    have he := (hd.congr_of_eventuallyEq (Eventually.of_forall hN)).deriv
    simpa only [mul_neg, mul_one, sub_neg_eq_add] using he
  change deriv (fun x ↦ deriv (fun t ↦ compositionMoment p t v -
    Real.sqrt (compositionMoment p 0 v * compositionMoment p 0 (v-t))) x) a = _
  rw [hfirst.deriv_eq]
  have hs := ((leftStrip_contDiffAt_S hp (sub_pos.mpr hav).ne').derivWithin
    (show (2 : WithTop ℕ∞)+1 ≤ 3 by decide)).differentiableAt (by decide)
  have hd := (leftStrip_hasDerivAt_expMoment_left p 1 0 a v).add
    ((hs.hasDerivAt.comp a (hgap a)).const_mul (S v))
  simpa only [leftStripE, Pi.add_def, Function.comp_apply, mul_neg, mul_one, sub_eq_add_neg]
    using hd.deriv

/-- The weighted third derivative uses the ordinary second-coordinate derivative of `E`
with `a` fixed. The weight `γ` is a scalar at the evaluation point. -/
private theorem leftStrip_weightedThird_eq {p : ℕ} (hp : 0 < p) {a v γ : ℝ}
    (hv : 0 < v) (hav : a < v) :
    let N (x y : ℝ) := compositionMoment p x y -
      Real.sqrt (compositionMoment p 0 y * compositionMoment p 0 (y-x))
    deriv (fun y ↦ deriv (deriv (N · y)) a) v - γ * deriv (deriv (N · v)) a =
      deriv (leftStripE p a) v - γ * leftStripE p a v := by
  let N (x y : ℝ) := compositionMoment p x y -
    Real.sqrt (compositionMoment p 0 y * compositionMoment p 0 (y-x))
  have he : (fun y ↦ deriv (deriv (N · y)) a) =ᶠ[𝓝 v] leftStripE p a := by
    filter_upwards [eventually_gt_nhds hv, eventually_gt_nhds hav] with y hy hay
    exact leftStrip_numerator_second_eq_E hp hy hay
  change weightedThird N a v γ = _
  rw [weightedThird, he.deriv_eq, he.eq_of_nhds]

/-- The explicit derivative of `E` in its second coordinate. -/
private theorem leftStrip_hasDerivAt_E_right {p : ℕ} (hp : 0 < p) {a v : ℝ}
    (hv : 0 < v) (hav : a < v) :
    let S (t : ℝ) := Real.sqrt (compositionMoment p 0 t)
    HasDerivAt (leftStripE p a)
      (leftStripExpMoment p 2 1 a v -
        (deriv S v * deriv (deriv S) (v-a) + S v * deriv (deriv (deriv S)) (v-a))) v := by
  let S := leftStripS p
  have hS := ((leftStrip_contDiffAt_S hp hv.ne').differentiableAt (by decide)).hasDerivAt
  have hS'' := ((leftStrip_contDiffAt_S hp (sub_pos.mpr hav).ne').derivWithin
    (show (2 : WithTop ℕ∞)+1 ≤ 3 by decide)).derivWithin
    (show (1 : WithTop ℕ∞)+1 ≤ 2 by decide)
  have hd := (hS''.differentiableAt (by decide)).hasDerivAt.comp v
    ((hasDerivAt_id' v).sub_const a)
  have hm := (leftStrip_hasDerivAt_expMoment_right p 2 0 a v).sub (hS.mul hd)
  change HasDerivAt (fun t ↦ leftStripExpMoment p 2 0 a t - S t * deriv (deriv S) (t-a)) _ v
  simpa only [Pi.sub_def, Pi.mul_def, Function.comp_apply, mul_one, add_comm] using hm

/-- The negative marginal's half-log slope, with the reflection included. -/
private def leftStripReflectedSlope (p : ℕ) (v : ℝ) : ℝ :=
  deriv (fun t ↦ leftStripS p (-t)) v / leftStripS p (-v)

/-- The rescaled sign of the differentiated numerator used at the origin. -/
private def leftStripScaledIntegrand (p : ℕ) (a v : ℝ) : ℝ :=
  v * (leftStripReflectedSlope p v * leftStripE p a v - deriv (leftStripE p a) v)

private abbrev leftStripVarianceHalf (p : ℕ) := compositionMarginalVariance p / 2

private abbrev leftStripZ (p k : ℕ) :=
  SmallCorner.integralMarginalDerivative p (leftStripVarianceHalf p) k

private theorem leftStrip_hasDerivAt_Z (p k : ℕ) (t : ℝ) :
    HasDerivAt (leftStripZ p k) (leftStripZ p (k + 1) t) t := by
  simpa only [SmallCorner.affineMarginalJet, zero_mul, zero_add, one_mul] using
    (SmallCorner.continuedMarginalJet_isAt p k 0 1 0 t).2.1

private theorem leftStrip_Z_eq_G {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : t ≠ 0) :
    leftStripZ p 0 t = SmallCorner.G p (leftStripVarianceHalf p) t := by
  simpa only [iteratedDeriv_zero] using
    (SmallCorner.iteratedDeriv_G_eq_integral hp
      (half_pos (compositionMarginalVariance_pos p)).ne' ht 0).symm

private theorem leftStrip_Z_pos {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : t ≠ 0) :
    0 < leftStripZ p 0 t := by
  rw [leftStrip_Z_eq_G hp ht]
  exact SmallCorner.G_pos hp (half_pos (compositionMarginalVariance_pos p)) ht

private def leftStripRoot (p : ℕ) (t : ℝ) : ℝ := Real.sqrt (leftStripZ p 0 t)

private def leftStripRootOne (p : ℕ) (t : ℝ) : ℝ :=
  leftStripZ p 1 t / (2 * leftStripRoot p t)

private def leftStripRootTwo (p : ℕ) (t : ℝ) : ℝ :=
  (leftStripZ p 2 t - 2 * leftStripRootOne p t ^ 2) / (2 * leftStripRoot p t)

private def leftStripRootThree (p : ℕ) (t : ℝ) : ℝ :=
  (leftStripZ p 3 t - 6 * leftStripRootOne p t * leftStripRootTwo p t) /
    (2 * leftStripRoot p t)

private theorem leftStrip_root_derivatives {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (leftStripRoot p) (leftStripRootOne p t) t ∧
    HasDerivAt (leftStripRootOne p) (leftStripRootTwo p t) t ∧
    HasDerivAt (leftStripRootTwo p) (leftStripRootThree p t) t := by
  have hr : 0 < leftStripRoot p t := Real.sqrt_pos.mpr (leftStrip_Z_pos hp ht)
  have hden := (mul_pos (by norm_num : (0 : ℝ) < 2) hr).ne'
  have h₁ : HasDerivAt (leftStripRoot p) (leftStripRootOne p t) t :=
    (leftStrip_hasDerivAt_Z p 0 t).sqrt (leftStrip_Z_pos hp ht).ne'
  have hn₁ := (div_mul_cancel₀ (leftStripZ p 1 t) hden).symm
  have h₂ : HasDerivAt (leftStripRootOne p) (leftStripRootTwo p t) t := by
    apply ((leftStrip_hasDerivAt_Z p 1 t).fun_div (h₁.const_mul 2) hden).congr_deriv
    change _ = (leftStripZ p 2 t - 2 * leftStripRootOne p t ^ 2) / (2 * leftStripRoot p t)
    rw [show leftStripZ p 1 t = leftStripRootOne p t * (2 * leftStripRoot p t) from hn₁]
    field_simp [hr.ne']
    <;> ring
  have hn₂ := (div_mul_cancel₀ (leftStripZ p 2 t - 2 * leftStripRootOne p t ^ 2) hden).symm
  refine ⟨h₁, h₂, ?_⟩
  apply (((leftStrip_hasDerivAt_Z p 2 t).sub ((h₂.pow 2).const_mul 2)).fun_div
    (h₁.const_mul 2) hden).congr_deriv
  change _ = (leftStripZ p 3 t - 6 * leftStripRootOne p t * leftStripRootTwo p t) /
    (2 * leftStripRoot p t)
  simp only [Pi.sub_apply, Pi.pow_apply]
  rw [show leftStripZ p 2 t - 2 * leftStripRootOne p t ^ 2 =
    leftStripRootTwo p t * (2 * leftStripRoot p t) from hn₂]
  field_simp [hr.ne']
  <;> ring

private theorem leftStrip_S_eq_root {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : t ≠ 0) :
    leftStripS p t = Real.sqrt (leftStripVarianceHalf p) * |t| * leftStripRoot p t := by
  have hc := half_pos (compositionMarginalVariance_pos p)
  have hm : compositionMoment p 0 t = leftStripVarianceHalf p * t ^ 2 * leftStripZ p 0 t := by
    rw [leftStrip_Z_eq_G hp ht, SmallCorner.G,
      mul_div_cancel₀ _ (mul_ne_zero hc.ne' (pow_ne_zero 2 ht))]
  change Real.sqrt (compositionMoment p 0 t) = _
  rw [hm, Real.sqrt_mul (mul_nonneg hc.le (sq_nonneg _)), Real.sqrt_mul hc.le,
    Real.sqrt_sq_eq_abs]
  rfl

private theorem leftStrip_S_derivatives {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : 0 < t) :
    let k := Real.sqrt (leftStripVarianceHalf p)
    deriv (leftStripS p) t = k * (leftStripRoot p t + t * leftStripRootOne p t) ∧
    deriv (deriv (leftStripS p)) t = k * (2 * leftStripRootOne p t + t * leftStripRootTwo p t) ∧
    deriv (deriv (deriv (leftStripS p))) t =
      k * (3 * leftStripRootTwo p t + t * leftStripRootThree p t) := by
  let k := Real.sqrt (leftStripVarianceHalf p)
  have h₁ {x : ℝ} (hx : 0 < x) :
      deriv (leftStripS p) x = k * (leftStripRoot p x + x * leftStripRootOne p x) := by
    have hd := ((hasDerivAt_id' x).mul (leftStrip_root_derivatives hp hx.ne').1).const_mul k
    have he : leftStripS p =ᶠ[𝓝 x] fun y ↦ k * (y * leftStripRoot p y) := by
      filter_upwards [eventually_gt_nhds hx] with y hy
      simpa only [abs_of_pos hy, mul_assoc] using leftStrip_S_eq_root hp hy.ne'
    simpa only [id_eq, mul_one, one_mul, add_comm] using (hd.congr_of_eventuallyEq he).deriv
  have h₂ {x : ℝ} (hx : 0 < x) :
      deriv (deriv (leftStripS p)) x =
        k * (2 * leftStripRootOne p x + x * leftStripRootTwo p x) := by
    have h := leftStrip_root_derivatives hp hx.ne'
    have hd := (h.1.add ((hasDerivAt_id' x).mul h.2.1)).const_mul k
    have he : deriv (leftStripS p) =ᶠ[𝓝 x]
        fun y ↦ k * (leftStripRoot p y + y * leftStripRootOne p y) := by
      filter_upwards [eventually_gt_nhds hx] with y hy using h₁ hy
    convert (hd.congr_of_eventuallyEq he).deriv using 1
    ring
  refine ⟨h₁ ht, h₂ ht, ?_⟩
  have h := leftStrip_root_derivatives hp ht.ne'
  have hd := ((h.2.1.const_mul 2).add ((hasDerivAt_id' t).mul h.2.2)).const_mul k
  have he : deriv (deriv (leftStripS p)) =ᶠ[𝓝 t]
      fun y ↦ k * (2 * leftStripRootOne p y + y * leftStripRootTwo p y) := by
    filter_upwards [eventually_gt_nhds ht] with y hy using h₂ hy
  convert (hd.congr_of_eventuallyEq he).deriv using 1
  ring

private theorem leftStrip_S_reflected_slope {p : ℕ} (hp : 0 < p) {v : ℝ} (hv : 0 < v) :
    leftStripReflectedSlope p v = 1 / v - leftStripRootOne p (-v) / leftStripRoot p (-v) := by
  let k := Real.sqrt (leftStripVarianceHalf p)
  have hk : 0 < k := Real.sqrt_pos.mpr (half_pos (compositionMarginalVariance_pos p))
  have hr : 0 < leftStripRoot p (-v) :=
    Real.sqrt_pos.mpr (leftStrip_Z_pos hp (neg_ne_zero.mpr hv.ne'))
  have he : (fun t ↦ leftStripS p (-t)) =ᶠ[𝓝 v] fun t ↦ k * (t * leftStripRoot p (-t)) := by
    filter_upwards [eventually_gt_nhds hv] with t ht
    simpa only [abs_neg, abs_of_pos ht, mul_assoc] using
      leftStrip_S_eq_root hp (neg_ne_zero.mpr ht.ne')
  have h := ((leftStrip_root_derivatives hp (neg_ne_zero.mpr hv.ne')).1.comp v
    (hasDerivAt_id' v).neg)
  have hd := ((hasDerivAt_id' v).mul h).const_mul k
  rw [leftStripReflectedSlope, (hd.congr_of_eventuallyEq he).deriv, he.eq_of_nhds]
  simp only [id_eq, Function.comp_apply, mul_neg, mul_one, one_mul]
  field_simp [hk.ne', hr.ne', hv.ne']
  <;> ring

private theorem leftStrip_S_mul_second {p : ℕ} (hp : 0 < p) {v d : ℝ}
    (hv : 0 < v) (hd : 0 < d) :
    leftStripS p v * deriv (deriv (leftStripS p)) d =
      leftStripVarianceHalf p * v * leftStripRoot p v *
        (2 * leftStripRootOne p d + d * leftStripRootTwo p d) := by
  have hk : Real.sqrt (leftStripVarianceHalf p) ^ 2 = leftStripVarianceHalf p :=
    Real.sq_sqrt (half_pos (compositionMarginalVariance_pos p)).le
  rw [leftStrip_S_eq_root hp hv.ne', abs_of_pos hv, (leftStrip_S_derivatives hp hd).2.1]
  calc
    _ = Real.sqrt (leftStripVarianceHalf p) ^ 2 * v * leftStripRoot p v *
        (2 * leftStripRootOne p d + d * leftStripRootTwo p d) := by ring
    _ = _ := by rw [hk]

/-- The normalized radical in `E` uses the existing continued marginal jet. -/
private theorem leftStrip_E_eq_regularized {p : ℕ} (hp : 0 < p) {a v : ℝ}
    (hv : 0 < v) (hav : a < v) :
    leftStripE p a v = leftStripExpMoment p 2 0 a v -
      leftStripVarianceHalf p * v * leftStripRoot p v *
        (2 * leftStripRootOne p (v-a) + (v-a) * leftStripRootTwo p (v-a)) := by
  rw [leftStripE, leftStrip_S_mul_second hp hv (sub_pos.mpr hav)]

private def leftStripRegularizedSlope (p : ℕ) (t : ℝ) : ℝ :=
  leftStripZ p 1 t / (2 * leftStripZ p 0 t)

private theorem leftStrip_root_log_slope {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : t ≠ 0) :
    leftStripRootOne p t / leftStripRoot p t = leftStripRegularizedSlope p t := by
  rw [leftStripRootOne, leftStripRegularizedSlope, div_div, mul_assoc, ← sq,
    show leftStripRoot p t ^ 2 = leftStripZ p 0 t from Real.sq_sqrt (leftStrip_Z_pos hp ht).le]

/-- The expression bounded by the origin replay, in terms of the tilted moments
and the regularized marginal jet. -/
private def leftStripRegularizedIntegrand (p : ℕ) (a v : ℝ) : ℝ :=
  let d := v-a
  let b := leftStripRegularizedSlope p (-v)
  let radical := ((1 + 3 / (p : ℝ)) / 4) * v * leftStripRoot p v *
    (3 * leftStripRootTwo p d + d * leftStripRootThree p d +
      (leftStripRegularizedSlope p v + b) *
        (2 * leftStripRootOne p d + d * leftStripRootTwo p d))
  v * (radical - leftStripExpMoment p 2 1 a v) + (1 - v * b) * leftStripExpMoment p 2 0 a v

/-- The regularized expression equals `v * (γ * E - E_v)` for the exact reflected slope. -/
private theorem leftStrip_scaled_integrand_eq_regularized {p : ℕ} (hp : 0 < p) {a v : ℝ}
    (hv : 0 < v) (hav : a < v) :
    leftStripScaledIntegrand p a v = leftStripRegularizedIntegrand p a v := by
  let d := v-a
  let k := Real.sqrt (leftStripVarianceHalf p)
  let r := leftStripRoot p v
  let r₁ := leftStripRootOne p v
  let b := leftStripRegularizedSlope p (-v)
  let A := 2 * leftStripRootOne p d + d * leftStripRootTwo p d
  let B := 3 * leftStripRootTwo p d + d * leftStripRootThree p d
  have hd : 0 < d := sub_pos.mpr hav
  have hk : k ^ 2 = leftStripVarianceHalf p :=
    Real.sq_sqrt (half_pos (compositionMarginalVariance_pos p)).le
  have hr : 0 < r := Real.sqrt_pos.mpr (leftStrip_Z_pos hp hv.ne')
  have hs : leftStripS p v = k * v * r := by rw [leftStrip_S_eq_root hp hv.ne', abs_of_pos hv]
  have hγ : leftStripReflectedSlope p v = 1 / v - b := by
    rw [leftStrip_S_reflected_slope hp hv, leftStrip_root_log_slope hp (neg_ne_zero.mpr hv.ne')]
  have hSlope : leftStripRegularizedSlope p v = r₁ / r :=
    (leftStrip_root_log_slope hp hv.ne').symm
  unfold leftStripScaledIntegrand leftStripRegularizedIntegrand
  rw [hγ, (leftStrip_hasDerivAt_E_right hp hv hav).deriv, leftStrip_E_eq_regularized hp hv hav]
  change v * ((1 / v - b) * (leftStripExpMoment p 2 0 a v - leftStripVarianceHalf p * v * r * A) -
      (leftStripExpMoment p 2 1 a v - (deriv (leftStripS p) v * deriv (deriv (leftStripS p)) d +
        leftStripS p v * deriv (deriv (deriv (leftStripS p))) d))) =
    v * (((1 + 3 / (p : ℝ)) / 4) * v * r * (B + (leftStripRegularizedSlope p v + b) * A) -
      leftStripExpMoment p 2 1 a v) + (1 - v * b) * leftStripExpMoment p 2 0 a v
  rw [hs, (leftStrip_S_derivatives hp hv).1, (leftStrip_S_derivatives hp hd).2.1,
    (leftStrip_S_derivatives hp hd).2.2, hSlope, ← SmallCorner.joint_normalization_eq hp]
  change v * ((1 / v - b) * (leftStripExpMoment p 2 0 a v - leftStripVarianceHalf p * v * r * A) -
      (leftStripExpMoment p 2 1 a v - (k * (r + v * r₁) * (k * A) + k * v * r * (k * B)))) =
    v * (leftStripVarianceHalf p * v * r * (B + (r₁ / r + b) * A) -
      leftStripExpMoment p 2 1 a v) +
      (1 - v * b) * leftStripExpMoment p 2 0 a v
  generalize k = K at hk ⊢
  generalize leftStripVarianceHalf p = c at hk ⊢
  rw [← hk]
  field_simp [hv.ne', hr.ne']
  <;> ring

end RefinedBMV.PositiveCenter
