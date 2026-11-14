/- GID: D5/S3/Arith/Robin/Analytic/LcmPowerCollisionDensity
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/Analytic/LcmPowerCollisionDensity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Density of real parameters giving coincident LCM power thresholds. -/

import D5.S3.Arith.Robin.Analytic.LcmPowerLeadingTerm
import D5.S3.Arith.Robin.Analytic.LcmPowerLogLattice
import D5.S3.Arith.Robin.Analytic.LcmPowerCollisionCrossing

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open D5.S3.Arith.Robin.Analytic.LcmPowerLemmaFifteen
open D5.S3.Arith.Robin.Analytic.LcmPowerLeadingTerm
open D5.S3.Arith.Robin.Analytic.LcmPowerCollisionCoefficient
open D5.S3.Arith.Robin.Analytic.LcmPowerLogLattice
open D5.S3.Arith.Robin.Analytic.LcmPowerCollisionCrossing

namespace D5.S3.Arith.Robin.Analytic.LcmPowerCollisionDensity

private lemma collision_ordered {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    {α β : ℝ} (hα : 1 < α) (hαβ : α < β) (M : ℕ) :
    ∃ κ ∈ Set.Ioo α β, ∃ i j : ℕ, M ≤ i ∧ M ≤ j ∧ 1 ≤ i ∧ 1 ≤ j ∧
      lcmPowerF κ p i = lcmPowerF κ q j := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  have hpq' : (p : ℝ) < q := by exact_mod_cast hpq
  have hβ : 1 < β := hα.trans hαβ
  apply collision_of_scaled_limits (by linarith) (by linarith) hαβ
    (coefficient_pos hα hp1) (coefficient_pos hβ hp1)
    (coefficient_pos hα hq1) (coefficient_pos hβ hq1)
    (lcmPowerF_scaled_limit hα hp1) (lcmPowerF_scaled_limit hβ hp1)
    (lcmPowerF_scaled_limit hα hq1) (lcmPowerF_scaled_limit hβ hq1)
    (log_coefficient_ratio_strictMono hp1 hpq' hα hβ hαβ) _ _ M
  · intro u v huv N
    exact prime_log_lattice_tail hp hq (ne_of_lt hpq) huv N
  · intro i j hi hj
    exact ((continuousOn_lcmPowerF hp1 hi).sub (continuousOn_lcmPowerF hq1 hj)).mono
      (fun κ hκ => hα.trans_le hκ.1)

/-- Fan–Kobayashi–Molnar §8: collision parameters are dense in (1, ∞). -/
theorem collision_parameters_dense {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {α β : ℝ} (hα : 1 < α) (hαβ : α < β) (M : ℕ) :
    ∃ κ ∈ Set.Ioo α β, ∃ i j : ℕ, M ≤ i ∧ M ≤ j ∧ 1 ≤ i ∧ 1 ≤ j ∧
      lcmPowerF κ p i = lcmPowerF κ q j := by
  rcases lt_or_gt_of_ne hpq with h | h
  · exact collision_ordered hp hq h hα hαβ M
  · obtain ⟨κ, hκ, i, j, hi, hj, hi1, hj1, hij⟩ := collision_ordered hq hp h hα hαβ M
    exact ⟨κ, hκ, j, i, hj, hi, hj1, hi1, hij.symm⟩

end D5.S3.Arith.Robin.Analytic.LcmPowerCollisionDensity
