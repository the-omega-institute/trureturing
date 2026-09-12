/- GID: D5/S3/Analytic/Interpolation/EnvelopeKMonotone
   generality: G
   mirror-B: D5/B/S3/Analytic/Interpolation/EnvelopeKMonotone
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The logarithmic moment envelope increases with the mean and decreases with total squared deviation on its positive domain. -/

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
#print axioms coordinate_variance_domain

end D5.S3.Analytic.Interpolation.EnvelopeKMonotone
