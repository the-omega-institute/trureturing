/- GID: D5/S3/Geometry/Hyperideal/TransitionEnvelopes
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/TransitionEnvelopes
   mirror-E: none(waiver:universal-real-transition-inequality)
   anchors: []
   utility: none
   digest: Actual hyper-ideal upper faces with two short neighbours, and the sharper high-edge estimate with one short neighbour. -/

import D5.S3.Geometry.Hyperideal.FourCycleEnvelopes

/-!
The hypotheses describe whole continuous faces, not endpoint samples.
The cosine is the original six-variable function. Neither monotonicity nor
an endpoint inequality is supplied as a premise. The analytic comparison
is consumed from its single owner, whose proof derives the derivative sign.

The two-short-neighbour cases distinguish all three pair arrangements under
the target-edge stabilizer. They cover the unbalanced P4 transition used in
CFMP_GEOMETRIC_REALIZATION.md Section 25. The second clause is the improved
high-edge envelope needed for the occurrence budget at degree seventeen.

The statement does not assume or construct a geometric manifold, co-volume,
zero-curvature metric, or a solution of unrestricted CFMP. The source and its
candidate dependency have not been elaborated in this runtime.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Geometry.Hyperideal.TransitionEnvelopes
open D5.S3.Geometry.Hyperideal.FourCycleEnvelopes

/-- At least two of the four neighbouring coordinates have the smaller cap. -/
def TwoSmall (y z v w : ℝ) : Prop :=
  (y ≤ 5/4 ∧ z ≤ 5/4) ∨ (y ≤ 5/4 ∧ v ≤ 5/4) ∨
  (y ≤ 5/4 ∧ w ≤ 5/4) ∨ (z ≤ 5/4 ∧ v ≤ 5/4) ∨
  (z ≤ 5/4 ∧ w ≤ 5/4) ∨ (v ≤ 5/4 ∧ w ≤ 5/4)

/-- At least one neighbouring coordinate has the same cap as the high edge. -/
def OneSmall (y z v w : ℝ) : Prop :=
  y ≤ 5/4 ∨ z ≤ 5/4 ∨ v ≤ 5/4 ∨ w ≤ 5/4

/-- The two uniform upper-face envelopes for a genuinely mixed local system. -/
theorem transition_envelopes :
    (∀ y z o v w : ℝ,
      y ∈ Set.Icc 1 2 → z ∈ Set.Icc 1 2 → o ∈ Set.Icc 1 2 →
      v ∈ Set.Icc 1 2 → w ∈ Set.Icc 1 2 → TwoSmall y z v w →
      cosine 2 y z o v w ≤ (70:ℝ)/99) ∧
    (∀ y z o v w : ℝ,
      y ∈ Set.Icc 1 2 → z ∈ Set.Icc 1 2 → o ∈ Set.Icc 1 2 →
      v ∈ Set.Icc 1 2 → w ∈ Set.Icc 1 2 → OneSmall y z v w →
      cosine (5/4) y z o v w ≤ 25/Real.sqrt 726) := by
  have hc1 : (1:ℝ) ∈ Set.Icc 1 2 := by constructor <;> norm_num
  have hc2 : (2:ℝ) ∈ Set.Icc 1 2 := by constructor <;> norm_num
  have hcb : (5/4:ℝ) ∈ Set.Icc 1 2 := by constructor <;> norm_num
  have cmp := cosine_mixed_comparison
  -- An internal positive-denominator step. All its premises are verified
  -- from the actual radicands and numerator at each analytic endpoint.
  have rootBound : ∀ A B P q : ℝ, 0 < A → 0 < B → 0 ≤ q →
      P^2 ≤ q^2*(A*B) → P / Real.sqrt A / Real.sqrt B ≤ q := by
    intro A B P q hA hB hq hs
    let r := Real.sqrt A * Real.sqrt B
    have hr : 0 < r := mul_pos (Real.sqrt_pos.2 hA) (Real.sqrt_pos.2 hB)
    have hrsq : r^2 = A*B := by
      dsimp [r]
      rw [mul_pow, Real.sq_sqrt hA.le, Real.sq_sqrt hB.le]
    rw [div_div]
    change P/r ≤ q
    apply (div_le_iff₀ hr).2
    by_cases hP : P ≤ 0
    · exact hP.trans (mul_nonneg hq hr.le)
    · by_contra h
      have hlt : q*r < P := lt_of_not_ge h
      have hsum : 0 < P+q*r := by nlinarith [mul_nonneg hq hr.le]
      have hprod := mul_pos (sub_pos.mpr hlt) hsum
      have hltSq : (q*r)^2 < P^2 := by nlinarith
      have heq : (q*r)^2 = q^2*(A*B) := by rw [mul_pow, hrsq]
      rw [heq] at hltSq
      exact (not_lt_of_ge hs) hltSq
  constructor
  · intro y z o v w hy hz ho hv hw hsmall
    rcases hsmall with ⟨hyb,hzb⟩ | ⟨hyb,hvb⟩ | ⟨hyb,hwb⟩ |
      ⟨hzb,hvb⟩ | ⟨hzb,hwb⟩ | ⟨hvb,hwb⟩
    · calc
        cosine 2 y z o v w ≤ cosine 2 (5/4) (5/4) 1 2 2 :=
          cmp 2 y z o v w (5/4) (5/4) 1 2 2
            hc2 hy hz ho hv hw hcb hcb hc1 hc2 hc2
            hyb hzb ho.1 hv.2 hw.2
        _ ≤ (70:ℝ)/99 := by
          unfold cosine
          apply rootBound <;> norm_num [rad, numerator]
    · calc
        cosine 2 y z o v w ≤ cosine 2 (5/4) 2 1 (5/4) 2 :=
          cmp 2 y z o v w (5/4) 2 1 (5/4) 2
            hc2 hy hz ho hv hw hcb hc2 hc1 hcb hc2
            hyb hz.2 ho.1 hvb hw.2
        _ ≤ (70:ℝ)/99 := by
          unfold cosine
          apply rootBound <;> norm_num [rad, numerator]
    · calc
        cosine 2 y z o v w ≤ cosine 2 (5/4) 2 1 2 (5/4) :=
          cmp 2 y z o v w (5/4) 2 1 2 (5/4)
            hc2 hy hz ho hv hw hcb hc2 hc1 hc2 hcb
            hyb hz.2 ho.1 hv.2 hwb
        _ ≤ (70:ℝ)/99 := by
          unfold cosine
          apply rootBound <;> norm_num [rad, numerator]
    · calc
        cosine 2 y z o v w ≤ cosine 2 2 (5/4) 1 (5/4) 2 :=
          cmp 2 y z o v w 2 (5/4) 1 (5/4) 2
            hc2 hy hz ho hv hw hc2 hcb hc1 hcb hc2
            hy.2 hzb ho.1 hvb hw.2
        _ ≤ (70:ℝ)/99 := by
          unfold cosine
          apply rootBound <;> norm_num [rad, numerator]
    · calc
        cosine 2 y z o v w ≤ cosine 2 2 (5/4) 1 2 (5/4) :=
          cmp 2 y z o v w 2 (5/4) 1 2 (5/4)
            hc2 hy hz ho hv hw hc2 hcb hc1 hc2 hcb
            hy.2 hzb ho.1 hv.2 hwb
        _ ≤ (70:ℝ)/99 := by
          unfold cosine
          apply rootBound <;> norm_num [rad, numerator]
    · calc
        cosine 2 y z o v w ≤ cosine 2 2 2 1 (5/4) (5/4) :=
          cmp 2 y z o v w 2 2 1 (5/4) (5/4)
            hc2 hy hz ho hv hw hc2 hc2 hc1 hcb hcb
            hy.2 hz.2 ho.1 hvb hwb
        _ ≤ (70:ℝ)/99 := by
          unfold cosine
          apply rootBound <;> norm_num [rad, numerator]
  · intro y z o v w hy hz ho hv hw hsmall
    rcases hsmall with hyb | hzb | hvb | hwb
    · calc
        cosine (5/4) y z o v w ≤ cosine (5/4) (5/4) 2 1 2 2 :=
          cmp (5/4) y z o v w (5/4) 2 1 2 2
            hcb hy hz ho hv hw hcb hc2 hc1 hc2 hc2
            hyb hz.2 ho.1 hv.2 hw.2
        _ ≤ 25/Real.sqrt 726 := by
          unfold cosine
          apply rootBound
          · norm_num [rad]
          · norm_num [rad]
          · positivity
          · rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 726)]
            norm_num [rad, numerator]
    · calc
        cosine (5/4) y z o v w ≤ cosine (5/4) 2 (5/4) 1 2 2 :=
          cmp (5/4) y z o v w 2 (5/4) 1 2 2
            hcb hy hz ho hv hw hc2 hcb hc1 hc2 hc2
            hy.2 hzb ho.1 hv.2 hw.2
        _ ≤ 25/Real.sqrt 726 := by
          unfold cosine
          apply rootBound
          · norm_num [rad]
          · norm_num [rad]
          · positivity
          · rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 726)]
            norm_num [rad, numerator]
    · calc
        cosine (5/4) y z o v w ≤ cosine (5/4) 2 2 1 (5/4) 2 :=
          cmp (5/4) y z o v w 2 2 1 (5/4) 2
            hcb hy hz ho hv hw hc2 hc2 hc1 hcb hc2
            hy.2 hz.2 ho.1 hvb hw.2
        _ ≤ 25/Real.sqrt 726 := by
          unfold cosine
          apply rootBound
          · norm_num [rad]
          · norm_num [rad]
          · positivity
          · rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 726)]
            norm_num [rad, numerator]
    · calc
        cosine (5/4) y z o v w ≤ cosine (5/4) 2 2 1 2 (5/4) :=
          cmp (5/4) y z o v w 2 2 1 2 (5/4)
            hcb hy hz ho hv hw hc2 hc2 hc1 hc2 hcb
            hy.2 hz.2 ho.1 hv.2 hwb
        _ ≤ 25/Real.sqrt 726 := by
          unfold cosine
          apply rootBound
          · norm_num [rad]
          · norm_num [rad]
          · positivity
          · rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 726)]
            norm_num [rad, numerator]

#print axioms transition_envelopes
end D5.S3.Geometry.Hyperideal.TransitionEnvelopes
