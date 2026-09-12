/- GID: D5/S3/Analytic/Interpolation/EnvelopeKMonotone
   generality: G
   mirror-B: D5/B/S3/Analytic/Interpolation/EnvelopeKMonotone
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The moment envelope increases with mean and decreases with squared deviation. -/

import D5.S3.Analytic.Interpolation.TwoPointGridDominance
import D5.S3.Analytic.Interpolation.HermiteMomentBounds
import D5.S3.Analytic.Interpolation.HermiteUpperEnvelope
import D5.S3.Analytic.Interpolation.LogOneSubExpDerivatives
import Mathlib.Analysis.Calculus.ContDiff.Deriv

open Set
open scoped Topology

noncomputable section

namespace D5.S3.Analytic.Interpolation.EnvelopeKMonotone

open TwoPointGridDominance
open private logValue_strictMono from D5.S3.Analytic.Interpolation.TwoPointGridDominance

/-- The two-node logarithmic envelope, with V the total squared deviation. -/
def psiK (k : ℕ) (m V : ℝ) : ℝ :=
  let r := Real.sqrt (V / ((k : ℝ) * ((k : ℝ) - 1)))
  let L := m - r
  let H := m + ((k : ℝ) - 1) * r
  logValue H + ((k : ℝ) - 1) * logValue L

private theorem radius_lt_mean {k : ℕ} (hk : 2 ≤ k) {m V : ℝ} (hm : 0 < m)
    (hV : V < (k : ℝ) * ((k : ℝ) - 1) * m ^ 2) :
    Real.sqrt (V / ((k : ℝ) * ((k : ℝ) - 1))) < m := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hden : (0 : ℝ) < (k : ℝ) * ((k : ℝ) - 1) :=
    mul_pos (by linarith) (by linarith)
  apply (Real.sqrt_lt' hm).mpr
  exact (div_lt_iff₀ hden).mpr (by nlinarith [hV])

/-- For fixed total squared deviation, increasing the positive mean increases the envelope. -/
theorem psiK_strictMono_mean {k : ℕ} (hk : 2 ≤ k) {m n V : ℝ}
    (hm : 0 < m) (hmn : m < n)
    (hV : V < (k : ℝ) * ((k : ℝ) - 1) * m ^ 2) : psiK k m V < psiK k n V := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkm : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  let r := Real.sqrt (V / ((k : ℝ) * ((k : ℝ) - 1)))
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hrm : r < m := radius_lt_mean hk hm hV
  have hL := logValue_strictMono (sub_pos.mpr hrm)
    (sub_pos.mpr (hrm.trans hmn)) (show m - r < n - r by linarith)
  have hH := logValue_strictMono
    (show 0 < m + ((k : ℝ) - 1) * r by positivity)
    (show 0 < n + ((k : ℝ) - 1) * r from
      add_pos_of_pos_of_nonneg (hm.trans hmn) (mul_nonneg hkm.le hr))
    (show m + ((k : ℝ) - 1) * r < n + ((k : ℝ) - 1) * r by linarith)
  exact add_lt_add hH (mul_lt_mul_of_pos_left hL hkm)

private theorem logValue_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt logValue (deriv logValue x) x :=
  ((LogOneSubExpDerivatives.log_one_sub_exp_derivatives.1.contDiffAt
    (isOpen_Ioi.mem_nhds hx)).differentiableAt (by norm_num)).hasDerivAt

private theorem logValue_deriv_strictAnti : StrictAntiOn (deriv logValue) (Ioi 0) := by
  have hlog := LogOneSubExpDerivatives.log_one_sub_exp_derivatives
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
    (hlog.1.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num))
  intro x hx
  have hxpos : 0 < x := interior_subset hx
  have hsecond := (hlog.2 x hxpos).2.1
  have he : 0 < Real.exp x - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hxpos)
  have hneg : -Real.exp x / (Real.exp x - 1) ^ 2 < 0 :=
    div_neg_of_neg_of_pos (neg_neg_of_pos (Real.exp_pos x)) (sq_pos_of_pos he)
  simpa only [logValue, iteratedDeriv_succ, iteratedDeriv_zero] using hsecond.trans_lt hneg

/-- Differentiating in the radius cancels the two node velocities into a derivative difference. -/
theorem radius_envelope_hasDerivAt {k : ℕ} (hk : 2 ≤ k) {m r : ℝ}
    (hr : 0 ≤ r) (hrm : r < m) :
    HasDerivAt
      (fun t => logValue (m + ((k : ℝ) - 1) * t) + ((k : ℝ) - 1) * logValue (m - t))
      (((k : ℝ) - 1) *
        (deriv logValue (m + ((k : ℝ) - 1) * r) - deriv logValue (m - r))) r := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hm : 0 < m := hr.trans_lt hrm
  have hH : 0 < m + ((k : ℝ) - 1) * r :=
    add_pos_of_pos_of_nonneg hm (mul_nonneg (by linarith) hr)
  have hupper := (logValue_hasDerivAt hH).comp r
    (((hasDerivAt_id r).const_mul ((k : ℝ) - 1)).const_add m)
  have hlower := (logValue_hasDerivAt (sub_pos.mpr hrm)).comp r
    ((hasDerivAt_const r m).sub (hasDerivAt_id r))
  have hd := hupper.add (hlower.const_mul ((k : ℝ) - 1))
  have hcoeff :
      deriv logValue (m + ((k : ℝ) - 1) * r) * (((k : ℝ) - 1) * 1) +
        ((k : ℝ) - 1) * (deriv logValue (m - r) * (0 - 1)) =
      ((k : ℝ) - 1) *
        (deriv logValue (m + ((k : ℝ) - 1) * r) - deriv logValue (m - r)) := by ring
  rw [hcoeff] at hd
  exact hd

/-- The two-node logarithmic sum strictly decreases with radius, including a zero left endpoint. -/
theorem radius_envelope_strictAnti {k : ℕ} (hk : 2 ≤ k) (m : ℝ) :
    StrictAntiOn
      (fun r => logValue (m + ((k : ℝ) - 1) * r) + ((k : ℝ) - 1) * logValue (m - r))
      (Ico 0 m) := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkm : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  apply strictAntiOn_of_deriv_neg (convex_Ico 0 m)
  · intro r hr
    exact (radius_envelope_hasDerivAt hk hr.1 hr.2).continuousAt.continuousWithinAt
  · intro r hr
    rw [interior_Ico] at hr
    rw [(radius_envelope_hasDerivAt hk hr.1.le hr.2).deriv]
    have hH : 0 < m + ((k : ℝ) - 1) * r :=
      add_pos (hr.1.trans hr.2) (mul_pos hkm hr.1)
    have hLH : m - r < m + ((k : ℝ) - 1) * r := by
      nlinarith [mul_pos (show (0 : ℝ) < k by linarith) hr.1]
    exact mul_neg_of_pos_of_neg hkm
      (sub_neg.mpr (logValue_deriv_strictAnti (sub_pos.mpr hr.2) hH hLH))

/-- At fixed positive mean, a larger feasible total squared deviation lowers the envelope. -/
theorem psiK_strictAnti_variance {k : ℕ} (hk : 2 ≤ k) {m V W : ℝ}
    (hm : 0 < m) (hV : 0 ≤ V) (hVW : V < W)
    (hW : W < (k : ℝ) * ((k : ℝ) - 1) * m ^ 2) : psiK k m W < psiK k m V := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hden : (0 : ℝ) < (k : ℝ) * ((k : ℝ) - 1) :=
    mul_pos (by linarith) (by linarith)
  have hrR := Real.sqrt_lt_sqrt (div_nonneg hV hden.le)
    ((div_lt_div_iff_of_pos_right hden).mpr hVW)
  exact radius_envelope_strictAnti hk m
    ⟨Real.sqrt_nonneg _, radius_lt_mean hk hm (hVW.trans hW)⟩
    ⟨Real.sqrt_nonneg _, radius_lt_mean hk hm hW⟩ hrR

/-- Positive coordinates place their total squared deviation strictly inside the envelope domain. -/
theorem coordinate_variance_domain {k : ℕ} (hk : 2 ≤ k) (x : Fin k → ℝ)
    (hx : ∀ i, 0 < x i) :
    let m := (∑ i, x i) / (k : ℝ)
    0 ≤ ∑ i, (x i - m) ^ 2 ∧
      ∑ i, (x i - m) ^ 2 < (k : ℝ) * ((k : ℝ) - 1) * m ^ 2 := by
  dsimp only
  refine ⟨Finset.sum_nonneg (fun i _ => sq_nonneg _), ?_⟩
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hden : (0 : ℝ) < (k : ℝ) * ((k : ℝ) - 1) :=
    mul_pos (by linarith) (by linarith)
  have hL := (HermiteMomentBounds.hermite_moment_bounds hk x hx).1
  have hsq := Real.lt_sq_of_sqrt_lt (sub_pos.mp hL)
  have hbound := (div_lt_iff₀ hden).mp hsq
  nlinarith [hbound]

#print axioms psiK_strictMono_mean
#print axioms radius_envelope_hasDerivAt
#print axioms radius_envelope_strictAnti
#print axioms psiK_strictAnti_variance
#print axioms coordinate_variance_domain

end D5.S3.Analytic.Interpolation.EnvelopeKMonotone
