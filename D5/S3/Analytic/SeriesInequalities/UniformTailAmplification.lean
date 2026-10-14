/- GID: D5/S3/Analytic/SeriesInequalities/UniformTailAmplification
   generality: G
   mirror-B: D5/B/S3/Analytic/SeriesInequalities/UniformTailAmplification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: One diverging multiplier preserves uniform tails with arbitrarily small mass cost. -/

/- The declarations construct a noncomputable weight for an arbitrary family
   of infinite series. They neither certify a finite instance nor enumerate
   a bounded domain, and provide no checker or numeric reduction. -/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Order

noncomputable section
open Filter Finset
open scoped BigOperators ENNReal NNReal Topology
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.SeriesInequalities.UniformTailAmplification

private lemma threshold_tsum (f : ℕ → ℝ≥0∞) (N : ℕ) :
    (∑' n, if N ≤ n then f n else 0) = ∑' k, f (N + k) := by
  have h := Summable.sum_add_tsum_nat_add'
    (f := fun n => if N ≤ n then f n else 0) (k := N) ENNReal.summable
  have hzero : (∑ n ∈ range N, if N ≤ n then f n else 0) = 0 := by
    apply sum_eq_zero
    intro n hn
    simp [Nat.not_le.mpr (mem_range.mp hn)]
  simpa [hzero, Nat.add_comm] using h.symm

private lemma tail_antitone (f : ℕ → ℝ≥0∞) :
    Antitone (fun N => ∑' k, f (N + k)) := by
  intro M N hMN
  change (∑' k, f (N + k)) ≤ ∑' k, f (M + k)
  rw [← threshold_tsum, ← threshold_tsum]
  apply ENNReal.tsum_le_tsum
  intro n
  split_ifs with hN hM
  · exact le_rfl
  · exact False.elim (hM (hMN.trans hN))
  · exact zero_le
  · exact le_rfl

private def staircase (N : ℕ → ℕ) (n : ℕ) : ℕ :=
  1 + ((range n).filter (fun j => N j ≤ n)).card

private lemma staircase_monotone (N : ℕ → ℕ) : Monotone (staircase N) := by
  intro m n hmn
  apply Nat.add_le_add_left
  apply card_le_card
  intro j hj
  rcases mem_filter.mp hj with ⟨hj, hNj⟩
  exact mem_filter.mpr ⟨mem_range.mpr ((mem_range.mp hj).trans_le hmn), hNj.trans hmn⟩

private lemma staircase_mul (N : ℕ → ℕ) (hN : ∀ j, j + 1 ≤ N j)
    (f : ℕ → ℝ≥0∞) (n : ℕ) :
    (staircase N n : ℝ≥0∞) * f n =
      f n + ∑' j, if N j ≤ n then f n else 0 := by
  rw [tsum_eq_sum (s := range n)]
  · rw [← sum_filter]
    simp [staircase, Nat.cast_add, add_mul, sum_const, nsmul_eq_mul]
  · intro j hj
    have hnj : n ≤ j := Nat.le_of_not_gt (by simpa only [mem_range] using hj)
    have hfalse : ¬ N j ≤ n := by have := hN j; omega
    simp [hfalse]

private lemma weighted_tail_bound (N : ℕ → ℕ) (hN : ∀ j, j + 1 ≤ N j)
    (f : ℕ → ℝ≥0∞) (b : ℕ → ℝ≥0∞)
    (hb : ∀ j, (∑' k, f (N j + k)) ≤ b j) (M J : ℕ) :
    (∑' k, (staircase N (M + k) : ℝ≥0∞) * f (M + k)) ≤
      (J + 1 : ℕ) * (∑' k, f (M + k)) + ∑' k, b (k + J) := by
  let F : ℕ → ℝ≥0∞ := fun j => ∑' k,
    if N j ≤ M + k then f (M + k) else 0
  have hFmass (j : ℕ) : F j ≤ ∑' k, f (M + k) :=
    ENNReal.tsum_le_tsum (fun k => by split_ifs <;> simp)
  have hFbudget (j : ℕ) : F j ≤ b j := by
    apply le_trans _ (hb j)
    rw [← threshold_tsum]
    exact ENNReal.tsum_comp_le_tsum_of_injective
      (fun _ _ h => Nat.add_left_cancel h) (fun n => if N j ≤ n then f n else 0)
  have hsplit := Summable.sum_add_tsum_nat_add'
    (f := F) (k := J) ENNReal.summable
  calc
    (∑' k, (staircase N (M + k) : ℝ≥0∞) * f (M + k)) =
        (∑' k, f (M + k)) + ∑' j, F j := by
      simp_rw [staircase_mul N hN f]
      rw [ENNReal.tsum_add, ENNReal.tsum_comm]
    _ = (∑' k, f (M + k)) +
        ((∑ j ∈ range J, F j) + ∑' k, F (k + J)) := by rw [hsplit]
    _ ≤ (∑' k, f (M + k)) +
        ((∑ _j ∈ range J, ∑' k, f (M + k)) + ∑' k, b (k + J)) := by
      exact add_le_add le_rfl (add_le_add (sum_le_sum (fun j _ => hFmass j))
        (ENNReal.tsum_le_tsum (fun k => hFbudget (k + J))))
    _ = (J + 1 : ℕ) * (∑' k, f (M + k)) + ∑' k, b (k + J) := by
      simp only [sum_const, card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      ring

/-- One natural multiplier works simultaneously for every member of a family
whose nonnegative series tails are uniformly small. Neither a uniform bound
on the total masses nor pointwise finiteness of those masses is assumed. -/
theorem exists_uniform_tail_amplification
    {X : Type*} (a : X → ℕ → ℝ≥0∞) (δ : ℝ≥0) (hδ : 0 < δ)
    (hUT : ∀ ε : ℝ≥0, 0 < ε →
      ∃ N : ℕ, ∀ x, (∑' k, a x (N + k)) ≤ (ε : ℝ≥0∞)) :
    ∃ w : ℕ → ℕ,
      (∀ n, 1 ≤ w n) ∧ Monotone w ∧
      Tendsto w atTop atTop ∧
      (∀ x, (∑' n, (w n : ℝ≥0∞) * a x n) ≤
        (∑' n, a x n) + (δ : ℝ≥0∞)) ∧
      (∀ ε : ℝ≥0, 0 < ε → ∃ M : ℕ, ∀ x,
        (∑' k, (w (M + k) : ℝ≥0∞) * a x (M + k)) ≤ (ε : ℝ≥0∞)) := by
  classical
  let b : ℕ → ℝ≥0 := fun j => δ * (1 / 2) ^ (j + 1)
  have hbpos (j : ℕ) : 0 < b j := by dsimp [b]; positivity
  have hbsum : (∑' j, (b j : ℝ≥0∞)) = (δ : ℝ≥0∞) := by
    simp only [b, ENNReal.coe_mul, ENNReal.coe_pow]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_add_one]
    norm_num
    rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]
  have hselect : ∀ j, ∃ M, ∀ n ≥ M,
      j + 1 ≤ n ∧ ∀ x, (∑' k, a x (n + k)) ≤ (b j : ℝ≥0∞) := by
    intro j
    obtain ⟨M, hM⟩ := hUT (b j) (hbpos j)
    refine ⟨max M (j + 1), fun n hn => ⟨(le_max_right _ _).trans hn, ?_⟩⟩
    intro x
    exact (tail_antitone (a x) ((le_max_left _ _).trans hn)).trans (hM x)
  obtain ⟨N, hmono, hN⟩ := extraction_forall_of_eventually' hselect
  have hNlower : ∀ j, j + 1 ≤ N j := fun j => (hN j).1
  let w := staircase N
  have hwmono : Monotone w := staircase_monotone N
  have hwlarge (J : ℕ) : J + 2 ≤ w (N J) := by
    have hsub : range (J + 1) ⊆ (range (N J)).filter (fun j => N j ≤ N J) := by
      intro j hj
      have hjJ : j ≤ J := by have := mem_range.mp hj; omega
      exact mem_filter.mpr ⟨mem_range.mpr (by have := hNlower J; omega),
        hmono.monotone hjJ⟩
    have hcard := card_le_card hsub
    simp only [card_range] at hcard
    change J + 2 ≤ 1 + _
    omega
  refine ⟨w, fun n => by dsimp [w, staircase]; omega, hwmono, ?_, ?_, ?_⟩
  · refine tendsto_atTop_atTop.2 fun J => ?_
    exact ⟨N J, fun n hn => (by omega : J ≤ J + 2).trans ((hwlarge J).trans (hwmono hn))⟩
  · intro x
    calc
      (∑' n, (w n : ℝ≥0∞) * a x n) =
          (∑' n, a x n) + ∑' j, ∑' k, a x (N j + k) := by
        simp_rw [w, staircase_mul N hNlower (a x)]
        rw [ENNReal.tsum_add, ENNReal.tsum_comm]
        congr 1
        exact tsum_congr (fun j => threshold_tsum (a x) (N j))
      _ ≤ (∑' n, a x n) + ∑' j, (b j : ℝ≥0∞) :=
        add_le_add le_rfl (ENNReal.tsum_le_tsum (fun j => (hN j).2 x))
      _ = (∑' n, a x n) + (δ : ℝ≥0∞) := by rw [hbsum]
  · intro ε hε
    have hbudget := ENNReal.tendsto_sum_nat_add (fun j => (b j : ℝ≥0∞))
      (by rw [hbsum]; exact ENNReal.coe_ne_top)
    have hehalf : (0 : ℝ≥0∞) < ((ε / 2 : ℝ≥0) : ℝ≥0∞) := by positivity
    obtain ⟨J, hJ⟩ := ((tendsto_order.1 hbudget).2 _ hehalf).exists
    let q : ℝ≥0 := (ε / 2) / (J + 1)
    have hq : 0 < q := by dsimp [q]; positivity
    obtain ⟨M, hM⟩ := hUT q hq
    refine ⟨M, fun x => ?_⟩
    have hcancel : (J + 1 : ℕ) * (q : ℝ≥0∞) = ((ε / 2 : ℝ≥0) : ℝ≥0∞) := by
      rw [← ENNReal.coe_natCast, ← ENNReal.coe_mul]
      congr 1
      dsimp [q]
      field_simp
      simp only [Nat.cast_add, Nat.cast_one]
    calc
      (∑' k, (w (M + k) : ℝ≥0∞) * a x (M + k)) ≤
          (J + 1 : ℕ) * (∑' k, a x (M + k)) + ∑' k, (b (k + J) : ℝ≥0∞) :=
        weighted_tail_bound N hNlower (a x) (fun j => (b j : ℝ≥0∞))
          (fun j => (hN j).2 x) M J
      _ ≤ (J + 1 : ℕ) * (q : ℝ≥0∞) + ((ε / 2 : ℝ≥0) : ℝ≥0∞) :=
        add_le_add (mul_le_mul_right (hM x) _) hJ.le
      _ = (ε : ℝ≥0∞) := by rw [hcancel, ← ENNReal.coe_add]; congr 1; ring

end D5.S3.Analytic.SeriesInequalities.UniformTailAmplification
