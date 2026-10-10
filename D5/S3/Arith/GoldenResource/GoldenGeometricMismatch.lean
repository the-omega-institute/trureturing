/- GID: D5/S3/Arith/GoldenResource/GoldenGeometricMismatch
   generality: I
   mirror-B: D5/B/S3/Arith/GoldenResource/GoldenGeometricMismatch
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite geometric exponent mismatch pays the actual prime-power objective gap. -/

import D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
import D5.S3.Arith.GoldenResource.GoldenResourceSupremum
import D5.S3.Arith.GoldenResourceObjectiveFactorization
import Mathlib.Data.Nat.Dist

/- Source/reuse audit (2026-10-10): the classical benefit and pressure objective
   are inherited, not new definitions of the optimization problem. D5 searches,
   including private suppliers, found the exact local increment in GoldenLocalThreshold
   and the exact active/next-count thresholds in GoldenResourceOptimalLayerCount.
   These declarations are exposed at their original owners, without copied proofs.
   GoldenResourceSupremum.local_eq_layer_sum already owns the telescoping identity;
   the proof below uses its original single-step supplier instead of duplicating it.
   GoldenLayerMarginalDecay gives an absolute upper bound, not the endpoint-preserving
   two-sided mismatch estimate. Pinned Mathlib db584cd6d46c92f209a44c0f1c829460d327499d
   supplies the generic log bounds used by the consumed contraction helper.
   Read-only OpenAI math adc7f1241b42e322a6451854ab7e4b4c146bf78a searches of
   NumberTheory/Analysis found no matching prime-power mismatch theorem.
   Library/ArithSums/erdosnicolas1975repartition.md already records the source-card
   1/p separation derivation: the contraction helper is bind-only, not an escape witness.
   Preregistered content: unbounded accumulated missing/excess-layer estimates for
   goldenPrimeLocalObjective, retaining both first-layer slacks and finite geometric
   sums; the coarse bound and finite actual-support consumer use these estimates.
   No numeric instance, infinite summability claim or RH closure is asserted. -/

namespace D5.S3.Arith.GoldenResource.GoldenGeometricMismatch

open Finset
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenLocalThreshold
open D5.S3.Arith.GoldenResourceObjectiveFactorization
open D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open D5.S3.Arith.GoldenResource.GoldenResourceSupremum

noncomputable section

/-- Endpoint-preserving budget. The first branch is used only when `1 ≤ m`.
At distance one these are exactly the missing/extra layer's price slack. -/
def geometricMismatchBudget (lambda : ℝ) (p a m : ℕ) : ℝ :=
  if a < m then
    Real.log p * goldenLayerMarginal p m * (∑ i ∈ range (m - a), (p : ℝ) ^ i) -
      lambda * Real.log p * (m - a)
  else if m < a then
    lambda * Real.log p * (a - m) -
      Real.log p * goldenLayerMarginal p (m + 1) *
        (∑ i ∈ range (a - m), (p : ℝ)⁻¹ ^ i)
  else 0

-- Consumed bind-only helper: generic logarithm bounds plus the actual layer ratio.
private theorem layer_contraction {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    Real.log p * goldenLayerMarginal p (k + 1) <
      (p : ℝ)⁻¹ * (Real.log p * goldenLayerMarginal p k) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hl : Real.log (p : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  have hq0 : 0 < (p : ℝ)⁻¹ := inv_pos.mpr hp0
  have hq1 : (p : ℝ)⁻¹ < 1 :=
    (inv_lt_one₀ hp0).mpr (by exact_mod_cast hp.one_lt)
  have hd : 0 < 1 - (p : ℝ)⁻¹ ^ k :=
    sub_pos.mpr (pow_lt_one₀ hq0.le hq1 (by omega))
  have he : 0 < 1 - (p : ℝ)⁻¹ ^ (k + 1) :=
    sub_pos.mpr (pow_lt_one₀ hq0.le hq1 (by omega))
  have hf : 0 < 1 - (p : ℝ)⁻¹ ^ (k + 1 + 1) :=
    sub_pos.mpr (pow_lt_one₀ hq0.le hq1 (by omega))
  have hr : (1 - (p : ℝ)⁻¹ ^ (k + 1 + 1)) /
      (1 - (p : ℝ)⁻¹ ^ (k + 1)) ≠ 1 := by
    rw [ne_eq, div_eq_one_iff_eq he.ne']
    have hpow := pow_pos hq0 (k + 1)
    rw [pow_succ]
    nlinarith
  have hupper := Real.log_lt_sub_one_of_pos (div_pos hf he) hr
  have hlower := mul_le_mul_of_nonneg_left
    (Real.one_sub_inv_le_log_of_pos (div_pos he hd)) hq0.le
  have hid : (1 - (p : ℝ)⁻¹ ^ (k + 1 + 1)) /
      (1 - (p : ℝ)⁻¹ ^ (k + 1)) - 1 =
      (p : ℝ)⁻¹ * (1 - ((1 - (p : ℝ)⁻¹ ^ (k + 1)) /
        (1 - (p : ℝ)⁻¹ ^ k))⁻¹) := by
    rw [inv_div]
    field_simp [he.ne', hp0.ne']
    simp only [pow_succ]
    ring
  unfold goldenLayerMarginal
  simp only [mul_div_cancel₀ _ hl]
  rw [hid] at hupper
  exact hupper.trans_le hlower

private theorem layer_geometric_decay {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k)
    (i : ℕ) :
    Real.log p * goldenLayerMarginal p (k + i) ≤
      (p : ℝ)⁻¹ ^ i * (Real.log p * goldenLayerMarginal p k) := by
  induction i with
  | zero => simp
  | succ i ih =>
      have hq : 0 ≤ (p : ℝ)⁻¹ := by positivity
      calc
        Real.log p * goldenLayerMarginal p (k + (i + 1)) ≤
            (p : ℝ)⁻¹ * (Real.log p * goldenLayerMarginal p (k + i)) := by
          simpa [Nat.add_assoc] using (layer_contraction hp (by omega : 1 ≤ k + i)).le
        _ ≤ (p : ℝ)⁻¹ * ((p : ℝ)⁻¹ ^ i *
            (Real.log p * goldenLayerMarginal p k)) :=
          mul_le_mul_of_nonneg_left ih hq
        _ = (p : ℝ)⁻¹ ^ (i + 1) *
            (Real.log p * goldenLayerMarginal p k) := by rw [pow_succ]; ring

private theorem missing_layers_gap {p : ℕ} (hp : p.Prime)
    (lambda : ℝ) (a j : ℕ) :
    Real.log p * goldenLayerMarginal p (a + j) * (∑ i ∈ range j, (p : ℝ) ^ i) -
        lambda * Real.log p * j ≤
      goldenPrimeLocalObjective lambda p (a + j) - goldenPrimeLocalObjective lambda p a := by
  induction j with
  | zero => simp
  | succ j ih =>
      by_cases hj : j = 0
      · subst j
        simpa [mul_sub, mul_comm, mul_left_comm, mul_assoc] using
          (golden_prime_local_objective_diff hp lambda a).symm.le
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
      have hc := (layer_contraction hp (by omega : 1 ≤ a + j)).le
      have hc' : (p : ℝ) * (Real.log p * goldenLayerMarginal p (a + j + 1)) ≤
          Real.log p * goldenLayerMarginal p (a + j) := by
        have h := mul_le_mul_of_nonneg_left hc hp0.le
        simpa [mul_assoc, hp0.ne'] using h
      have hs : 0 ≤ ∑ i ∈ range j, (p : ℝ) ^ i :=
        sum_nonneg fun i _ => pow_nonneg hp0.le i
      have hm := mul_le_mul_of_nonneg_right hc' hs
      have hd := golden_prime_local_objective_diff hp lambda (a + j)
      rw [Nat.add_succ, geom_sum_succ]
      push_cast
      nlinarith

private theorem extra_layers_gap {p : ℕ} (hp : p.Prime)
    (lambda : ℝ) (m j : ℕ) :
    lambda * Real.log p * j -
        Real.log p * goldenLayerMarginal p (m + 1) *
          (∑ i ∈ range j, (p : ℝ)⁻¹ ^ i) ≤
      goldenPrimeLocalObjective lambda p m - goldenPrimeLocalObjective lambda p (m + j) := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hb := layer_geometric_decay hp (by omega : 1 ≤ m + 1) j
      have hd := golden_prime_local_objective_diff hp lambda (m + j)
      rw [Nat.add_succ, sum_range_succ]
      push_cast
      have hindex : m + 1 + j = m + j + 1 := by omega
      rw [hindex] at hb
      nlinarith

/-- The geometric budget is a lower bound on the actual local prime-power gap.
No optimality hypothesis is needed for this comparison itself. -/
theorem prime_power_objective_gap_ge_geometric_mismatch {p : ℕ} (hp : p.Prime)
    (lambda : ℝ) (a m : ℕ) :
    geometricMismatchBudget lambda p a m ≤
      goldenPrimeLocalObjective lambda p m - goldenPrimeLocalObjective lambda p a := by
  unfold geometricMismatchBudget
  split_ifs with ham hma
  · simpa [Nat.add_sub_of_le ham.le] using missing_layers_gap hp lambda a (m - a)
  · simpa [Nat.add_sub_of_le hma.le] using extra_layers_gap hp lambda m (a - m)
  · have h : a = m := by omega
    subst a
    simp

private theorem missing_geometric_sum_lower {p : ℕ} (hp : p.Prime) (j : ℕ) :
    (j : ℝ) + ((j - 1 : ℕ) : ℝ) ≤ ∑ i ∈ range j, (p : ℝ) ^ i := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  induction j with
  | zero => simp
  | succ j ih =>
      by_cases hj : j = 0
      · subst j; simp
      have hpow : (2 : ℝ) ≤ (p : ℝ) ^ j :=
        hp2.trans (le_self_pow₀ (by linarith) hj)
      rw [sum_range_succ, Nat.succ_sub_one, Nat.cast_add, Nat.cast_one]
      rw [Nat.cast_sub (by omega : 1 ≤ j), Nat.cast_one] at ih
      nlinarith

private theorem extra_geometric_sum_upper {p : ℕ} (hp : p.Prime) (j : ℕ) :
    (∑ i ∈ range j, (p : ℝ)⁻¹ ^ i) ≤ (j : ℝ) - ((j - 1 : ℕ) : ℝ) / 2 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hq0 : 0 ≤ (p : ℝ)⁻¹ := by positivity
  have hqhalf : (p : ℝ)⁻¹ ≤ 1 / 2 := by
    simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 2) hp2
  induction j with
  | zero => simp
  | succ j ih =>
      by_cases hj : j = 0
      · subst j; simp
      have hpow : (p : ℝ)⁻¹ ^ j ≤ 1 / 2 := by
        exact (show (p : ℝ)⁻¹ ^ j ≤ (p : ℝ)⁻¹ from
          by simpa using pow_le_pow_of_le_one hq0 (by linarith) (by omega : 1 ≤ j)).trans
          hqhalf
      rw [sum_range_succ, Nat.succ_sub_one, Nat.cast_add, Nat.cast_one]
      rw [Nat.cast_sub (by omega : 1 ≤ j), Nat.cast_one] at ih
      nlinarith

/-- Under the two endpoint thresholds the budget is nonnegative and coercive,
including tied prices, zero distance and the first-layer slacks. -/
theorem geometric_mismatch_budget_coercive {p : ℕ} (hp : p.Prime)
    {lambda : ℝ} (hlambda : 0 < lambda) (a m : ℕ)
    (hlower : 0 < m → lambda ≤ goldenLayerMarginal p m)
    (hupper : goldenLayerMarginal p (m + 1) ≤ lambda) :
    lambda * Real.log p / 2 * ((Nat.dist a m - 1 : ℕ) : ℝ) ≤
      geometricMismatchBudget lambda p a m ∧
    0 ≤ geometricMismatchBudget lambda p a m := by
  have hl : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have ht : 0 ≤ lambda * Real.log p := (mul_pos hlambda hl).le
  have hmain : lambda * Real.log p / 2 * ((Nat.dist a m - 1 : ℕ) : ℝ) ≤
      geometricMismatchBudget lambda p a m := by
    unfold geometricMismatchBudget
    split_ifs with ham hma
    · rw [Nat.dist_eq_sub_of_le ham.le]
      have hs := missing_geometric_sum_lower hp (m - a)
      have hs0 : 0 ≤ ∑ i ∈ range (m - a), (p : ℝ) ^ i :=
        sum_nonneg fun i _ => pow_nonneg (by positivity) i
      have hb := mul_le_mul_of_nonneg_left (hlower (by omega)) hl.le
      have hbs := mul_le_mul_of_nonneg_right hb hs0
      have hts := mul_le_mul_of_nonneg_left hs ht
      have hd : 0 ≤ ((m - a - 1 : ℕ) : ℝ) := by positivity
      nlinarith [mul_nonneg ht hd]
    · rw [Nat.dist_eq_sub_of_le_right hma.le]
      have hs := extra_geometric_sum_upper hp (a - m)
      have hs0 : 0 ≤ ∑ i ∈ range (a - m), (p : ℝ)⁻¹ ^ i :=
        sum_nonneg fun i _ => pow_nonneg (by positivity) i
      have hb := mul_le_mul_of_nonneg_left hupper hl.le
      have hbs := mul_le_mul_of_nonneg_right hb hs0
      have hts := mul_le_mul_of_nonneg_left hs ht
      nlinarith
    · have h : a = m := by omega
      subst a
      simp [Nat.dist_self]
  exact ⟨hmain, (by positivity :
    0 ≤ lambda * Real.log p / 2 * ((Nat.dist a m - 1 : ℕ) : ℝ)).trans hmain⟩

/-- Sum every exponent mismatch on the union of the actual prime supports.
The reference is the existing minimal-count optimizer at the same price. -/
theorem golden_resource_objective_gap_ge_geometric_mismatch
    {lambda : ℝ} (hlambda : 0 < lambda) {n M : ℕ} (hn : 1 ≤ n) (hM : 1 ≤ M)
    (hcounts : ∀ p : ℕ, M.factorization p = optimalLayerCount lambda p) :
    (lambda / 2 * ∑ p ∈ n.primeFactors ∪ M.primeFactors,
        Real.log p * ((Nat.dist (n.factorization p) (M.factorization p) - 1 : ℕ) : ℝ)) ≤
      (∑ p ∈ n.primeFactors ∪ M.primeFactors,
        geometricMismatchBudget lambda p (n.factorization p) (M.factorization p)) ∧
    (∑ p ∈ n.primeFactors ∪ M.primeFactors,
        geometricMismatchBudget lambda p (n.factorization p) (M.factorization p)) ≤
      goldenResourceObjective lambda M - goldenResourceObjective lambda n ∧
    0 ≤ (∑ p ∈ n.primeFactors ∪ M.primeFactors,
        geometricMismatchBudget lambda p (n.factorization p) (M.factorization p)) ∧
    (∑ p ∈ n.primeFactors ∪ M.primeFactors,
        geometricMismatchBudget lambda p (n.factorization p) (M.factorization p)) ≤
      sSup {x : ℝ | ∃ N : ℕ, 1 ≤ N ∧ goldenResourceObjective lambda N = x} -
        goldenResourceObjective lambda n := by
  classical
  have hprime (p : ℕ) (hp : p ∈ n.primeFactors ∪ M.primeFactors) : p.Prime := by
    rcases mem_union.mp hp with hp | hp
    · exact Nat.prime_of_mem_primeFactors hp
    · exact Nat.prime_of_mem_primeFactors hp
  have hlocal (p : ℕ) (hp : p ∈ n.primeFactors ∪ M.primeFactors) :=
    geometric_mismatch_budget_coercive (hprime p hp) hlambda
      (n.factorization p) (M.factorization p)
      (by
        rw [hcounts]
        intro hm
        exact (count_layer_active hlambda (hprime p hp) (by omega)).le)
      (by rw [hcounts]; exact count_next_layer_le hlambda (hprime p hp))
  have hgap : (∑ p ∈ n.primeFactors ∪ M.primeFactors,
        geometricMismatchBudget lambda p (n.factorization p) (M.factorization p)) ≤
      goldenResourceObjective lambda M - goldenResourceObjective lambda n := by
    rw [golden_resource_objective_sum_on lambda hM _ (subset_union_right),
      golden_resource_objective_sum_on lambda hn _ (subset_union_left), ← sum_sub_distrib]
    exact sum_le_sum fun p hp =>
      prime_power_objective_gap_ge_geometric_mismatch (hprime p hp) lambda _ _
  refine ⟨?_, hgap, sum_nonneg (fun p hp => (hlocal p hp).2), ?_⟩
  · rw [mul_sum]
    apply sum_le_sum
    intro p hp
    have h := (hlocal p hp).1
    convert h using 1 <;> ring
  · rw [golden_resource_supremum_eq_positive_part_sum hlambda,
      ← objective_at_optimal_eq_positive_part_sum hlambda hM hcounts]
    exact hgap

#print axioms prime_power_objective_gap_ge_geometric_mismatch
#print axioms geometric_mismatch_budget_coercive
#print axioms golden_resource_objective_gap_ge_geometric_mismatch
#print axioms golden_prime_local_objective_diff
#print axioms count_layer_active
#print axioms count_next_layer_le

end
end D5.S3.Arith.GoldenResource.GoldenGeometricMismatch
