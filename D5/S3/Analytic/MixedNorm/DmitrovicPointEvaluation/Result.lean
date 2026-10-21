/- GID: D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/Result
   generality: G
   mirror-B: D5/B/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/Result
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/Defs.claim; result=D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/Result.result; claim=D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/Defs.claim
   digest: The constant-one mixed-norm point-evaluation conjecture fails at every finite positive p and every larger q, including infinity. -/

import D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.CircleMean
import D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.FirstOrderGap

open scoped ENNReal
open D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.Defs
open D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.CircleMean

namespace D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.Result

/-- Every exponent pair above the contractive range has a holomorphic counterexample. -/
theorem fails_off_contractive_range {p : ℝ} {q : ℝ≥0∞} {α : ℝ}
    (hp : 0 < p) (hpq : ENNReal.ofReal p < q) (hα : 0 < α) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f (Metric.ball 0 1) ∧
      mixedNorm (ENNReal.ofReal p) q α f < ∞ ∧
      ∃ z : ℂ, ‖z‖ < 1 ∧ mixedNorm (ENNReal.ofReal p) q α f <
        ENNReal.ofReal ‖f z‖ *
          ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ (α + 1 / (ENNReal.ofReal p).toReal)) := by
  by_cases hq : q = ∞
  · subst q
    obtain ⟨a, ha, z, hz, hfinite, hviol, _⟩ := refutes_at_infinity hp hα
    exact ⟨powerFamily p a, powerFamily_differentiableOn hp ha.1.le ha.2,
      hfinite, z, hz, hviol⟩
  · have hpqt : p < q.toReal := by
      have ht := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hq).mpr hpq
      simpa only [ENNReal.toReal_ofReal hp.le] using ht
    have hqt : 0 < q.toReal := hp.trans hpqt
    obtain ⟨t, ht0, ht1, hgap⟩ := FirstOrderGap.exists_gap hp hpqt hα
    have ha : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
    have ha1 : Real.sqrt t < 1 :=
      (Real.sqrt_lt' zero_lt_one).mpr (by simpa using ht1)
    have hgap' : Radial.radialIntegral p q.toReal α ((Real.sqrt t) ^ 2) <
        Radial.evaluationExcess p q.toReal α ((Real.sqrt t) ^ 2) := by
      simpa only [Real.sq_sqrt ht0.le] using hgap
    obtain ⟨hhol, hfinite, hz, hviol, _⟩ := refutes_of_gap hp hqt hα ha ha1 hgap'
    rw [ENNReal.ofReal_toReal hq] at hfinite hviol
    exact ⟨powerFamily p (Real.sqrt t), hhol, hfinite,
      ((1 / (1 + α * p) * Real.sqrt t : ℝ) : ℂ), hz, hviol⟩

/-- Dmitrovic's universal constant-one point-evaluation conjecture is false. -/
theorem result : ¬ claim := by
  obtain ⟨f, hhol, hfinite, z, hz, hviol⟩ :=
    fails_off_contractive_range (p := 1) (q := 2) (α := 1)
      (by norm_num) (by norm_num) (by norm_num)
  intro hclaim
  exact (not_lt_of_ge (hclaim (ENNReal.ofReal 1) 2 1
    (by norm_num) (by norm_num) (by norm_num) f hhol hfinite z hz)) hviol

end D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.Result
