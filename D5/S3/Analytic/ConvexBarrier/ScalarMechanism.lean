/- GID: D5/S3/Analytic/ConvexBarrier/ScalarMechanism
   generality: I
   mirror-B: D5/B/S3/Analytic/ConvexBarrier/ScalarMechanism
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Formalized power-cone geometry and analytic support module. -/

import D5.S3.Analytic.ConvexBarrier.ScalarAlgebra
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
The minimizer-curve ODE mechanism of Zhang--Fu--Dai, Theorem 3.5,
printed pp. 10--12.  `Curve` records local analytic/chord data, not either
contradictory limiting outcome.  The integration, infinite projective length,
vanishing of k*w^2, vertical positive lower bound, and contradiction are
derived below.  This is NOT an arbitrary-barrier lower theorem: constructing
`Curve` from an arbitrary LHSCB remains an explicit foundation gap.

Here `s=sqrt(rho)`, `rho=nu-1`, and `q=sqrt(qhat)` (so `q` is NOT `qhat`).
All theorem statements are source only; no elaboration/kernel check has run.
Intended canonical subject: D5/S3/Analytic/ConvexBarrier.
-/

open Set

namespace D5.S3.Analytic.ConvexBarrier

def J : Set ℝ := Ioo 0 1
noncomputable def logit (r : ℝ) : ℝ := Real.log r - Real.log (1-r)
noncomputable def width (c r : ℝ) : ℝ := r ^ c * (1-r) ^ (1-c)
noncomputable def eta (c s : ℝ) : ℝ := 2 * ((2-c) - (1+c)*s^2) / s
noncomputable def ellMinus (p q r : ℝ) : ℝ := (p + 1/r) / q
noncomputable def ellPlus (p q r : ℝ) : ℝ := (-p + 1/(1-r)) / q
noncomputable def beta (p k kp q : ℝ) : ℝ := (kp/k - 2*p) / q
noncomputable def logKappa (c : ℝ) (k : ℝ → ℝ) (r : ℝ) : ℝ :=
  Real.log (k r) + 2*c*Real.log r + 2*(1-c)*Real.log (1-r)
noncomputable def kappa (c : ℝ) (k : ℝ → ℝ) (r : ℝ) : ℝ := k r * width c r ^ 2

structure Curve (c s : ℝ) where
  p : ℝ → ℝ
  q : ℝ → ℝ
  k : ℝ → ℝ
  kp : ℝ → ℝ
  zeta : ℝ → ℝ
  sigma : ℝ → ℝ
  q_pos : ∀ r ∈ J, 0 < q r
  k_pos : ∀ r ∈ J, 0 < k r
  k_deriv : ∀ r ∈ J, HasDerivAt k (kp r) r
  sigma_deriv : ∀ r ∈ J, HasDerivAt sigma (q r) r
  horizontal : ∀ r ∈ J,
    (1/s ≤ ellMinus (p r) (q r) r ∧ ellMinus (p r) (q r) r ≤ s) ∧
    (1/s ≤ ellPlus (p r) (q r) r ∧ ellPlus (p r) (q r) r ≤ s)
  mixed : ∀ r ∈ J, |beta (p r) (k r) (kp r) (q r)| ≤ 2*(s^2-1)/s
  vertical : ∀ r ∈ J,
    1/s ≤ (width c r + zeta r)*Real.sqrt (k r) ∧
    1/s ≤ (width c r - zeta r)*Real.sqrt (k r)

theorem hasDerivAt_logit {r : ℝ} (hr : r ∈ J) :
    HasDerivAt logit (1/(r*(1-r))) r := by
  have hr0 : r ≠ 0 := hr.1.ne'
  have hr1 : 1-r ≠ 0 := (sub_pos.2 hr.2).ne'
  have h := ((hasDerivAt_id r).log hr0).sub
    (((hasDerivAt_const r (1:ℝ)).sub (hasDerivAt_id r)).log hr1)
  convert h using 1
  · rfl
  · dsimp
    field_simp [hr0, hr1]
    ring

private theorem antitone_from_derivatives {f d : ℝ → ℝ}
    (hd : ∀ r ∈ J, HasDerivAt f (d r) r) (hn : ∀ r ∈ J, d r ≤ 0) :
    AntitoneOn f J := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioo (0 : ℝ) 1)
  · exact fun r hr => (hd r hr).continuousAt.continuousWithinAt
  · intro r hr
    have hr' : r ∈ J := by simpa [J] using hr
    exact (hd r hr').differentiableAt.differentiableWithinAt
  · intro r hr
    have hr' : r ∈ J := by simpa [J] using hr
    rw [(hd r hr').deriv]
    exact hn r hr'

private theorem logit_monotone : MonotoneOn logit J := by
  have h := antitone_from_derivatives
    (f := fun r => -logit r) (d := fun r => -(1/(r*(1-r))))
    (fun r hr => (hasDerivAt_logit hr).neg) (fun r hr => by
      have : 0 < r*(1-r) := mul_pos hr.1 (sub_pos.2 hr.2)
      exact neg_nonpos.2 (by positivity))
  intro a ha b hb hab
  have := h ha hb hab
  linarith

/-- Every prescribed projective coordinate occurs, with an explicit point. -/
theorem logit_surjective (T : ℝ) : ∃ r ∈ J, logit r = T := by
  let e := Real.exp T
  have he : 0 < e := Real.exp_pos T
  have hden : 0 < 1+e := by linarith
  let r := e/(1+e)
  have hr : r ∈ J := by
    exact ⟨div_pos he hden, (div_lt_one hden).2 (by linarith)⟩
  have hsub : 1-r = 1/(1+e) := by dsimp [r]; field_simp [hden.ne'] <;> ring
  refine ⟨r, hr, ?_⟩
  unfold logit
  rw [hsub]
  change Real.log (e/(1+e)) - Real.log (1/(1+e)) = T
  rw [Real.log_div he.ne' hden.ne', Real.log_div one_ne_zero hden.ne', Real.log_one]
  have : Real.log e = T := Real.log_exp T
  linarith

/-- Integrated primitive bound, obtained from the derivative sign on the
whole interval by the mean-value theorem.  No asymptotic premise occurs. -/
theorem primitive_lower {σ q : ℝ → ℝ} {B : ℝ}
    (hσ : ∀ r ∈ J, HasDerivAt σ (q r) r)
    (hq : ∀ r ∈ J, B/(r*(1-r)) ≤ q r)
    {a r : ℝ} (ha : a ∈ J) (hr : r ∈ J) (har : a ≤ r) :
    σ a + B*(logit r - logit a) ≤ σ r := by
  have hd : ∀ t ∈ J, HasDerivAt (fun t => B*logit t - σ t)
      (B/(t*(1-t)) - q t) t := by
    intro t ht
    convert ((hasDerivAt_logit ht).const_mul B).sub (hσ t ht) using 1 <;> ring
  have hm := antitone_from_derivatives hd (fun t ht => sub_nonpos.2 (hq t ht))
  have := hm ha hr har
  linarith

/-- Exact one-sided `sigma -> +infinity`, expressed without filter notation.
The lower derivative comparison and divergence of logit are both proved. -/
theorem primitive_diverges {σ q : ℝ → ℝ} {B : ℝ} (hB : 0 < B)
    (hσ : ∀ r ∈ J, HasDerivAt σ (q r) r)
    (hq : ∀ r ∈ J, B/(r*(1-r)) ≤ q r) :
    ∀ M : ℝ, ∃ a ∈ J, ∀ r ∈ J, a ≤ r → M ≤ σ r := by
  intro M
  let r0 : ℝ := 1/2
  have h0 : r0 ∈ J := by norm_num [r0, J]
  obtain ⟨t, ht, htlog⟩ := logit_surjective (logit r0 + (M-σ r0)/B)
  refine ⟨max r0 t, ⟨lt_of_lt_of_le h0.1 (le_max_left _ _), max_lt h0.2 ht.2⟩, ?_⟩
  intro r hr har
  have h0r : r0 ≤ r := le_trans (le_max_left _ _) har
  have htr : t ≤ r := le_trans (le_max_right _ _) har
  have hlog := logit_monotone ht hr htr
  rw [htlog] at hlog
  have hm := mul_le_mul_of_nonneg_left hlog hB.le
  have hcancel : B*((M-σ r0)/B) = M-σ r0 := by field_simp [hB.ne'] <;> ring
  have hint := primitive_lower hσ hq h0 hr h0r
  nlinarith

theorem exp_logKappa {c r : ℝ} {k : ℝ → ℝ} (hr : r ∈ J) (hk : 0 < k r) :
    Real.exp (logKappa c k r) = kappa c k r := by
  have h1 : 0 < 1-r := sub_pos.2 hr.2
  have he : logKappa c k r = Real.log (k r) +
      (Real.log r*c + Real.log (1-r)*(1-c)) +
      (Real.log r*c + Real.log (1-r)*(1-c)) := by unfold logKappa; ring
  rw [he, Real.exp_add, Real.exp_add, Real.exp_log hk]
  simp only [kappa, width, Real.rpow_def_of_pos hr.1, Real.rpow_def_of_pos h1]
  simp only [Real.exp_add]
  ring

theorem Curve.logKappa_deriv {c s r : ℝ} (C : Curve c s) (hr : r ∈ J) :
    HasDerivAt (logKappa c C.k)
      (C.kp r/C.k r + 2*c/r - 2*(1-c)/(1-r)) r := by
  have hk := (C.k_deriv r hr).log (C.k_pos r hr).ne'
  have hx := ((hasDerivAt_id r).log hr.1.ne').const_mul (2*c)
  have hy := (((hasDerivAt_const r (1:ℝ)).sub (hasDerivAt_id r)).log
    (sub_pos.2 hr.2).ne').const_mul (2*(1-c))
  convert (hk.add hx).add hy using 1 <;>
    (try simp only [logKappa, Function.comp_apply]) <;>
    (try funext y) <;> simp [logKappa, id_eq, Function.comp_apply] <;> ring

theorem normalized_logKappa_identity (p q k kp c r : ℝ) :
    (kp/k + 2*c/r - 2*(1-c)/(1-r))/q =
      beta p k kp q + 2*c*ellMinus p q r - 2*(1-c)*ellPlus p q r := by
  unfold beta ellMinus ellPlus
  ring

theorem normalized_rate_bound {c s b lm lp : ℝ}
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (hs : 0 < s)
    (hb : b ≤ 2*(s^2-1)/s) (hm : lm ≤ s) (hp : 1/s ≤ lp) :
    b + 2*c*lm - 2*(1-c)*lp ≤ -eta c s := by
  have hm' := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ 2*c)
  have hp' := mul_le_mul_of_nonneg_left hp (by nlinarith : 0 ≤ 2*(1-c))
  calc
    b + 2*c*lm - 2*(1-c)*lp ≤ 2*(s^2-1)/s + 2*c*s - 2*(1-c)*(1/s) := by
      linarith
    _ = -eta c s := by unfold eta; field_simp [hs.ne'] <;> ring

theorem Curve.q_lower {c s : ℝ} (C : Curve c s) (hs : 0 < s)
    {r : ℝ} (hr : r ∈ J) : (1/(2*s))/(r*(1-r)) ≤ C.q r := by
  have hq := C.q_pos r hr
  have hden : 0 < r*(1-r) := mul_pos hr.1 (sub_pos.2 hr.2)
  have hsum : (ellMinus (C.p r) (C.q r) r + ellPlus (C.p r) (C.q r) r) *
      (r*(1-r)*C.q r) = 1 := by
    unfold ellMinus ellPlus
    field_simp [hq.ne', hr.1.ne', (sub_pos.2 hr.2).ne']
    <;> ring
  have hm := (C.horizontal r hr).1.2
  have hp := (C.horizontal r hr).2.2
  have hh := mul_le_mul_of_nonneg_right (add_le_add hm hp) (mul_pos hden hq).le
  rw [hsum] at hh
  apply (div_le_iff₀ hden).2
  apply (div_le_iff₀ (by positivity : 0 < 2*s)).2
  nlinarith

theorem Curve.logKappa_rate {c s : ℝ} (C : Curve c s)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (hs : 0 < s) {r : ℝ} (hr : r ∈ J) :
    C.kp r/C.k r + 2*c/r - 2*(1-c)/(1-r) ≤ -eta c s * C.q r := by
  have hid := normalized_logKappa_identity (C.p r) (C.q r) (C.k r) (C.kp r) c r
  have hb := (abs_le.1 (C.mixed r hr)).2
  have hh := normalized_rate_bound hc hc1 hs hb
    (C.horizontal r hr).1.2 (C.horizontal r hr).2.1
  rw [← hid] at hh
  exact (div_le_iff₀ (C.q_pos r hr)).1 hh

/-- This is the integrated log-kappa inequality (3.27)--(3.28), proved from
derivatives by mean value monotonicity, rather than assumed as curve data. -/
theorem Curve.integrated_logKappa {c s : ℝ} (C : Curve c s)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (hs : 0 < s)
    {a r : ℝ} (ha : a ∈ J) (hr : r ∈ J) (har : a ≤ r) :
    logKappa c C.k r ≤ logKappa c C.k a - eta c s*(C.sigma r-C.sigma a) := by
  have hd : ∀ t ∈ J, HasDerivAt
      (fun t => logKappa c C.k t + eta c s*C.sigma t)
      (C.kp t/C.k t + 2*c/t - 2*(1-c)/(1-t) + eta c s*C.q t) t := by
    intro t ht
    exact (C.logKappa_deriv ht).add ((C.sigma_deriv t ht).const_mul (eta c s))
  have hm := antitone_from_derivatives hd (fun t ht => by
    have := C.logKappa_rate hc hc1 hs ht
    linarith)
  have := hm ha hr har
  nlinarith

theorem Curve.exponential_bound {c s : ℝ} (C : Curve c s)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (hs : 0 < s)
    {a r : ℝ} (ha : a ∈ J) (hr : r ∈ J) (har : a ≤ r) :
    kappa c C.k r ≤ kappa c C.k a * Real.exp (-eta c s*(C.sigma r-C.sigma a)) := by
  have h := Real.exp_le_exp.2 (C.integrated_logKappa hc hc1 hs ha hr har)
  rw [exp_logKappa hr (C.k_pos r hr)] at h
  rw [sub_eq_add_neg, Real.exp_add, exp_logKappa ha (C.k_pos a ha)] at h
  simpa only [neg_mul] using h

/-- Actual epsilon proof of k*w^2 -> 0 as r -> 1 from the left.  No decay or
infinite-length assumption is a field of `Curve`. -/
theorem Curve.kappa_vanishes {c s : ℝ} (C : Curve c s)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (hs : 0 < s) (hη : 0 < eta c s) :
    ∀ ε : ℝ, 0 < ε → ∃ a ∈ J, ∀ r ∈ J, a ≤ r → kappa c C.k r ≤ ε := by
  intro ε hε
  let r0 : ℝ := 1/2
  have h0 : r0 ∈ J := by norm_num [r0, J]
  let M := C.sigma r0 + (logKappa c C.k r0 - Real.log ε)/eta c s
  obtain ⟨t, ht, htail⟩ := primitive_diverges (by positivity : 0 < 1/(2*s))
    C.sigma_deriv (fun r hr => C.q_lower hs hr) M
  refine ⟨max r0 t, ⟨lt_of_lt_of_le h0.1 (le_max_left _ _), max_lt h0.2 ht.2⟩, ?_⟩
  intro r hr har
  have hsigma := htail r hr (le_trans (le_max_right _ _) har)
  have hm := mul_le_mul_of_nonneg_left hsigma hη.le
  have hcancel : eta c s * (M-C.sigma r0) = logKappa c C.k r0 - Real.log ε := by
    dsimp [M]
    field_simp [hη.ne']
    <;> ring
  have hi := C.integrated_logKappa hc hc1 hs h0 hr (le_trans (le_max_left _ _) har)
  have he : logKappa c C.k r ≤ Real.log ε := by nlinarith
  have := Real.exp_le_exp.2 he
  rwa [exp_logKappa hr (C.k_pos r hr), Real.exp_log hε] at this

theorem Curve.kappa_positive_lower {c s : ℝ} (C : Curve c s) (hs : 0 < s)
    {r : ℝ} (hr : r ∈ J) : 1/s^2 ≤ kappa c C.k r := by
  exact vertical_kappa_lower hs (C.k_pos r hr) (C.vertical r hr).1 (C.vertical r hr).2

/-- Complete contradiction on the curve.  It is deliberately named and
typed as a curve theorem, not as an arbitrary-LHSCB theorem. -/
theorem Curve.parameter_lower {c s : ℝ} (C : Curve c s)
    (hc : 0 < c) (hc2 : c ≤ 1/2) (hs : 1 ≤ s) : 3/(1+c) ≤ s^2+1 := by
  have hs0 : 0 < s := by linarith
  by_contra hn
  have hsmall : s^2+1 < 3/(1+c) := lt_of_not_ge hn
  have hcden : 0 < 1+c := by linarith
  have hsmall' := (lt_div_iff₀ hcden).1 hsmall
  have hη : 0 < eta c s := by unfold eta; exact div_pos (by nlinarith) hs0
  let ε := (1/s^2)/2
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨a, ha, htail⟩ := C.kappa_vanishes hc.le (by linarith) hs0 hη ε hε
  have hlo := C.kappa_positive_lower hs0 ha
  have hhi := htail a ha le_rfl
  dsimp [ε] at hhi
  have : 0 < 1/s^2 := by positivity
  linarith

end D5.S3.Analytic.ConvexBarrier
