/- GID: D5/S3/Arith/PrimeLogBudget
   generality: G
   mirror-B: D5/B/S3/Arith/PrimeLogBudget
   mirror-E: none(waiver:general-real-existence-and-uniqueness)
   anchors: []
   utility: none
   digest: Every positive real budget uniquely determines a threshold above two through the sum of logarithmic prime ratios. -/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

namespace D5.S3.Arith.PrimeLogBudget

open scoped BigOperators Topology

noncomputable section

/-- Sum of `log (y / p)` over exactly the natural primes strictly below `y`. -/
def primeLogBudget (y : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesBelow ⌈y⌉₊, Real.log (y / p)

-- A fixed upper cutoff retains the value even as primes enter the active set.
private theorem budget_eq_fixed_sum {y : ℝ} {N : ℕ} (hy : 0 < y) (hN : y ≤ N) :
    primeLogBudget y = ∑ p ∈ Nat.primesBelow N, max 0 (Real.log y - Real.log p) := by
  classical
  unfold primeLogBudget
  calc
    _ = ∑ p ∈ Nat.primesBelow ⌈y⌉₊, max 0 (Real.log y - Real.log p) := by
      apply Finset.sum_congr rfl
      intro p hp
      obtain ⟨hpy, hp⟩ := Nat.mem_primesBelow.mp hp
      have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
      have hlog : Real.log p < Real.log y := Real.log_lt_log hp0 (Nat.lt_ceil.mp hpy)
      rw [Real.log_div hy.ne' hp0.ne', max_eq_right (sub_nonneg.mpr hlog.le)]
    _ = _ := by
      apply Finset.sum_subset (Nat.primesBelow_mono (Nat.ceil_le.mpr hN))
      intro p hp hnot
      have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr (Nat.mem_primesBelow.mp hp).2.pos
      have hpy : y ≤ p := by
        by_contra h
        exact hnot (Nat.mem_primesBelow.mpr
          ⟨Nat.lt_ceil.mpr (lt_of_not_ge h), (Nat.mem_primesBelow.mp hp).2⟩)
      exact max_eq_left (sub_nonpos.mpr (Real.log_le_log hy hpy))

private theorem budget_continuousAt {y : ℝ} (hy : 0 < y) :
    ContinuousAt primeLogBudget y := by
  obtain ⟨N, hN⟩ := exists_nat_gt y
  have hc : ContinuousAt
      (fun z : ℝ => ∑ p ∈ Nat.primesBelow N, max 0 (Real.log z - Real.log p)) y := by
    exact tendsto_finsetSum _ fun p _ =>
      continuousAt_const.max ((Real.continuousAt_log hy.ne').sub continuousAt_const)
  apply hc.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hy hN] with z hz
  exact budget_eq_fixed_sum hz.1 hz.2.le

private theorem budget_strictMonoOn : StrictMonoOn primeLogBudget (Set.Ici 2) := by
  intro y hy z hz hyz
  obtain ⟨N, hN⟩ := exists_nat_gt z
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy
  have hz0 : 0 < z := hy0.trans hyz
  rw [budget_eq_fixed_sum hy0 (hyz.le.trans hN.le), budget_eq_fixed_sum hz0 hN.le]
  apply Finset.sum_lt_sum
  · intro p _
    exact max_le_max_left _ (sub_le_sub_right (Real.log_le_log hy0 hyz.le) _)
  · refine ⟨2, Nat.mem_primesBelow.mpr ⟨?_, Nat.prime_two⟩, ?_⟩
    · exact_mod_cast (lt_of_le_of_lt hz hN)
    · have hlog : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hy
      have hlogz : Real.log 2 ≤ Real.log z := Real.log_le_log (by norm_num) hz
      norm_num only [Nat.cast_ofNat]
      rw [max_eq_right (sub_nonneg.mpr hlog), max_eq_right (sub_nonneg.mpr hlogz)]
      exact sub_lt_sub_right (Real.log_lt_log hy0 hyz) _

private theorem budget_two : primeLogBudget 2 = 0 := by
  simp [primeLogBudget]

private theorem log_ratio_two_le_budget {y : ℝ} (hy : 2 < y) :
    Real.log y - Real.log 2 ≤ primeLogBudget y := by
  classical
  have hy0 : 0 < y := lt_trans (by norm_num) hy
  rw [budget_eq_fixed_sum hy0 (Nat.le_ceil y)]
  have htwo : 2 ∈ Nat.primesBelow ⌈y⌉₊ :=
    Nat.mem_primesBelow.mpr ⟨Nat.lt_ceil.mpr (by exact_mod_cast hy), Nat.prime_two⟩
  have h := Finset.single_le_sum
    (f := fun p : ℕ => max 0 (Real.log y - Real.log p))
    (fun p _ => le_max_left _ _) htwo
  exact (le_max_right _ _).trans (by simpa using h)

/-- Every positive budget has exactly one prime threshold strictly above two. -/
theorem exists_unique_prime_log_budget {T : ℝ} (hT : 0 < T) :
    ∃! y : ℝ, 2 < y ∧ T = primeLogBudget y := by
  let b := Real.exp (T + Real.log 2)
  have hb : 2 < b := by
    calc
      2 = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ < b := Real.exp_lt_exp.mpr (by linarith)
  have hupper : T ≤ primeLogBudget b := by
    have h := log_ratio_two_le_budget hb
    dsimp [b] at h
    rw [Real.log_exp] at h
    linarith
  have hc : ContinuousOn primeLogBudget (Set.Icc 2 b) := by
    intro y hy
    exact (budget_continuousAt (lt_of_lt_of_le (by norm_num) hy.1)).continuousWithinAt
  obtain ⟨y, hy, hvalue⟩ := intermediate_value_Icc hb.le hc
    (show T ∈ Set.Icc (primeLogBudget 2) (primeLogBudget b) from
      ⟨by rw [budget_two]; exact hT.le, hupper⟩)
  have hy2 : 2 < y := by
    apply lt_of_le_of_ne hy.1
    intro heq
    subst y
    rw [budget_two] at hvalue
    linarith
  refine ⟨y, ⟨hy2, hvalue.symm⟩, ?_⟩
  intro z hz
  exact budget_strictMonoOn.injOn hz.1.le hy2.le (hz.2.symm.trans hvalue.symm)

end

end D5.S3.Arith.PrimeLogBudget
