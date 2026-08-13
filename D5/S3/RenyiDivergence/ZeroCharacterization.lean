/- GID: D5/S3/RenyiDivergence/ZeroCharacterization
   generality: G
   mirror-B: D5/B/S3/RenyiDivergence/ZeroCharacterization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Characterize zero Renyi divergence and prove above-one nonnegativity. -/

/- Library-search audit trail (2026-08-13):
   * Pinned mathlib searches covered weighted AM--GM equality and strictness, Young's inequality,
     strict concavity of `Real.log`, finite-sum equality, and Renyi names. The exact equality result
     is `Real.geom_mean_eq_arith_mean2_weighted_iff_of_pos`; its inequality companion and
     `Finset.sum_eq_sum_iff_of_le` reduce the below-one equality case to pointwise equality. No
     finite probability-theory Renyi divergence or reusable Renyi zero characterization was found.
   * A working-tree search found only `renyi_divergence_nonneg` in `Basic`, for `0 < alpha < 1`,
     and no Renyi equality-to-zero characterization. Renyi `eq`/`iff` hits elsewhere are order,
     skew-symmetry, or additivity identities rather than a zero characterization.
   * The import closure is OrderLimits -> Monotone -> Basic -> Bhattacharyya -> Metric -> Pinsker ->
     {GrandmotherTheorem, ZeroSupportDPI} -> ClassicalDPI -> Mathlib, together with GibbsEquality ->
     {GrandmotherTheorem, ClassicalDPI}. Every repository module in the closure has generality G;
     Mathlib is external.
-/

import D5.S3.RenyiDivergence.OrderLimits
import D5.S3.Divergence.GibbsEquality

namespace D5.S3.RenyiDivergence

open D5.S3.Divergence.ClassicalDPI
open D5.S3.Divergence.GrandmotherTheorem
open D5.S3.Divergence.GibbsEquality

/-!
The literal totalized definition has value zero at order one for every pair, so zero can
characterize equality only away from order one. Above one, both nonnegativity and the forward zero
implication factor through KL. Below one, the KL comparison has the wrong direction; equality is
instead extracted from weighted AM--GM coordinate by coordinate.
-/

/-- Finite Renyi divergence is nonnegative above order one under discrete absolute continuity. -/
theorem renyi_divergence_nonneg_of_one_lt {ι : Type*} [Fintype ι]
    (alpha : Real) (p q : ι -> Real) (halpha : 1 < alpha)
    (hp : (forall i, 0 <= p i) ∧ ∑ i, p i = 1)
    (hq : (forall i, 0 <= q i) ∧ ∑ i, q i = 1)
    (hac : forall i, q i = 0 -> p i = 0) :
    0 <= renyiDivergence alpha p q := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  have hq_pos : forall i, 0 < p i -> 0 < q i := by
    intro i hpi
    have hqi_ne : q i ≠ 0 := by
      intro hqi
      exact hpi.ne' (hac i hqi)
    exact lt_of_le_of_ne (hq.1 i) (Ne.symm hqi_ne)
  exact (kl_divergence_nonneg p q hp hq hac).trans
    (kl_le_renyi_divergence_of_one_lt alpha p q halpha hp hq_pos)

/-- Below order one, zero Renyi divergence characterizes equality of probability masses when their
positive supports overlap. The forward implication uses weighted AM--GM equality, not KL. -/
theorem renyi_divergence_eq_zero_iff_of_lt_one {ι : Type*} [Fintype ι]
    (alpha : Real) (p q : ι -> Real) (halpha : 0 < alpha ∧ alpha < 1)
    (hp : (forall i, 0 <= p i) ∧ ∑ i, p i = 1)
    (hq : (forall i, 0 <= q i) ∧ ∑ i, q i = 1)
    (hcommon : Exists fun i => 0 < p i ∧ 0 < q i) :
    renyiDivergence alpha p q = 0 <-> p = q := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  constructor
  · intro hzero
    have hsum_pos : 0 < ∑ i, (p i) ^ alpha * (q i) ^ (1 - alpha) := by
      apply Finset.sum_pos' (fun i _ => mul_nonneg
        (Real.rpow_nonneg (hp.1 i) alpha)
        (Real.rpow_nonneg (hq.1 i) (1 - alpha)))
      rcases hcommon with ⟨i, hpi, hqi⟩
      exact ⟨i, Finset.mem_univ i, mul_pos
        (Real.rpow_pos_of_pos hpi alpha)
        (Real.rpow_pos_of_pos hqi (1 - alpha))⟩
    have hprefactor_ne : 1 / (alpha - 1) ≠ 0 :=
      div_ne_zero one_ne_zero (sub_ne_zero.mpr halpha.2.ne)
    have hlog_zero : Real.log (∑ i, (p i) ^ alpha * (q i) ^ (1 - alpha)) = 0 := by
      rw [renyiDivergence] at hzero
      exact (mul_eq_zero.mp hzero).resolve_left hprefactor_ne
    have hsum_eq_one : (∑ i, (p i) ^ alpha * (q i) ^ (1 - alpha)) = 1 :=
      Real.eq_one_of_pos_of_log_eq_zero hsum_pos hlog_zero
    have harith_sum : (∑ i, (alpha * p i + (1 - alpha) * q i)) = 1 := by
      rw [Finset.sum_add_distrib, <- Finset.mul_sum, <- Finset.mul_sum, hp.2, hq.2]
      ring
    have hpointwise (i : ι) :
        (p i) ^ alpha * (q i) ^ (1 - alpha) <=
          alpha * p i + (1 - alpha) * q i :=
      Real.geom_mean_le_arith_mean2_weighted halpha.1.le
        (sub_nonneg.mpr halpha.2.le) (hp.1 i) (hq.1 i) (by ring)
    have hall : forall i, i ∈ Finset.univ ->
        (p i) ^ alpha * (q i) ^ (1 - alpha) =
          alpha * p i + (1 - alpha) * q i := by
      apply (Finset.sum_eq_sum_iff_of_le fun i _ => hpointwise i).mp
      exact hsum_eq_one.trans harith_sum.symm
    funext i
    exact (Real.geom_mean_eq_arith_mean2_weighted_iff_of_pos
      halpha.1 (sub_pos.mpr halpha.2) (hp.1 i) (hq.1 i) (by ring)).mp
        (hall i (Finset.mem_univ i))
  · rintro rfl
    exact renyi_divergence_self alpha p hp

/-- Above order one, zero Renyi divergence characterizes equality of probability masses under
discrete absolute continuity. The forward implication is the KL equality characterization. -/
theorem renyi_divergence_eq_zero_iff_of_one_lt {ι : Type*} [Fintype ι]
    (alpha : Real) (p q : ι -> Real) (halpha : 1 < alpha)
    (hp : (forall i, 0 <= p i) ∧ ∑ i, p i = 1)
    (hq : (forall i, 0 <= q i) ∧ ∑ i, q i = 1)
    (hac : forall i, q i = 0 -> p i = 0) :
    renyiDivergence alpha p q = 0 <-> p = q := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  constructor
  · intro hzero
    have hq_pos : forall i, 0 < p i -> 0 < q i := by
      intro i hpi
      have hqi_ne : q i ≠ 0 := by
        intro hqi
        exact hpi.ne' (hac i hqi)
      exact lt_of_le_of_ne (hq.1 i) (Ne.symm hqi_ne)
    have hkl_nonneg : 0 <= klDivergence p q :=
      kl_divergence_nonneg p q hp hq hac
    have hkl_le : klDivergence p q <= renyiDivergence alpha p q :=
      kl_le_renyi_divergence_of_one_lt alpha p q halpha hp hq_pos
    have hkl_zero : klDivergence p q = 0 :=
      le_antisymm (hkl_le.trans_eq hzero) hkl_nonneg
    exact (kl_divergence_eq_zero_iff p q hp hq hac).mp hkl_zero
  · rintro rfl
    exact renyi_divergence_self alpha p hp

/-- At every positive order other than one, zero Renyi divergence characterizes equality of
probability masses under discrete absolute continuity. -/
theorem renyi_divergence_eq_zero_iff {ι : Type*} [Fintype ι]
    (alpha : Real) (p q : ι -> Real) (halpha : 0 < alpha) (halpha_ne : alpha ≠ 1)
    (hp : (forall i, 0 <= p i) ∧ ∑ i, p i = 1)
    (hq : (forall i, 0 <= q i) ∧ ∑ i, q i = 1)
    (hac : forall i, q i = 0 -> p i = 0) :
    renyiDivergence alpha p q = 0 <-> p = q := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  by_cases hlt : alpha < 1
  · have hcommon : Exists fun i => 0 < p i ∧ 0 < q i := by
      have hsum_pos : 0 < ∑ i, p i := by rw [hp.2]; norm_num
      rcases (Finset.sum_pos_iff_of_nonneg fun i _ => hp.1 i).mp hsum_pos with
        ⟨i, _, hpi⟩
      have hqi_ne : q i ≠ 0 := by
        intro hqi
        exact hpi.ne' (hac i hqi)
      exact ⟨i, hpi, lt_of_le_of_ne (hq.1 i) (Ne.symm hqi_ne)⟩
    exact renyi_divergence_eq_zero_iff_of_lt_one alpha p q ⟨halpha, hlt⟩ hp hq hcommon
  · have hone : 1 < alpha := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm halpha_ne)
    exact renyi_divergence_eq_zero_iff_of_one_lt alpha p q hone hp hq hac

#print axioms renyi_divergence_nonneg_of_one_lt
#print axioms renyi_divergence_eq_zero_iff_of_lt_one
#print axioms renyi_divergence_eq_zero_iff_of_one_lt
#print axioms renyi_divergence_eq_zero_iff

end D5.S3.RenyiDivergence
