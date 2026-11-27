/- GID: D5/S3/Arith/Abundancy/ZelinskyNortonConjecture27
   generality: I
   mirror-B: D5/B/S3/Arith/Abundancy/ZelinskyNortonConjecture27
   mirror-E: none(waiver:symbolic-asymptotic-theorem)
   anchors: []
   utility: none
   digest: Unbounded first differences of Norton thresholds at every alpha greater than one. -/

import D5.S3.Arith.Abundancy.BeriZelinskyQuestion6
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Positive-power lower bounds force the integer first differences to diverge. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Filter Real
open scoped Topology

open D5.S3.Arith.OmegaGreedyPermutation (prime)

namespace D5.S3.Arith.Abundancy.ZelinskyNortonConjecture27

private lemma difference_diverges_of_bound (A : ℕ → ℕ) (P : ℕ → ℝ)
    (beta c : ℝ) (hbeta : 0 < beta) (hc : 0 < c)
    (hP : Tendsto P atTop atTop)
    (hbound : ∀ᶠ n in atTop,
      c * P n ^ beta ≤ (A (n + 1) : ℝ) - A n + 1) :
    Tendsto (fun n => (A (n + 1) : ℤ) - A n) atTop atTop := by
  have hpower : Tendsto (fun n => c * P n ^ beta) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hc).mpr ((tendsto_rpow_atTop hbeta).comp hP)
  apply (tendsto_intCast_atTop_iff (R := ℝ)).mp
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [hbound, hpower.eventually (eventually_ge_atTop (b + 1))]
    with n hn hb
  simp only [Int.cast_sub, Int.cast_natCast]
  linarith

/-- Every fixed positive real increment is eventually exceeded by the first difference. -/
theorem result (α : ℝ) (hα : 1 < α) (C : ℝ) (_hC : 0 < C) :
    ∀ᶠ n in atTop,
      (BeriZelinskyQuestion6.aAlpha α n : ℝ) + C <
        (BeriZelinskyQuestion6.aAlpha α (n + 1) : ℝ) := by
  obtain ⟨c, hc, hbound⟩ := BeriZelinskyQuestion6.norton_adjacent_cancellation α hα
  have hPtop :
      Tendsto (fun n : ℕ => (prime (n - 1) : ℝ))
        atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      ((Nat.nth_strictMono Nat.infinite_setOfPred_prime).tendsto_atTop.comp
        (tendsto_sub_atTop_nat 1))
  have hdiff := difference_diverges_of_bound (BeriZelinskyQuestion6.aAlpha α)
    (fun n => (prime (n - 1) : ℝ))
    (α - 1) c (by linarith) hc hPtop hbound
  have hreal : Tendsto (fun n =>
      (((BeriZelinskyQuestion6.aAlpha α (n + 1) : ℤ) -
        BeriZelinskyQuestion6.aAlpha α n : ℤ) : ℝ)) atTop atTop :=
    tendsto_intCast_atTop_atTop.comp hdiff
  filter_upwards [hreal.eventually_gt_atTop C] with n hn
  simp only [Int.cast_sub, Int.cast_natCast] at hn
  linarith

end D5.S3.Arith.Abundancy.ZelinskyNortonConjecture27
