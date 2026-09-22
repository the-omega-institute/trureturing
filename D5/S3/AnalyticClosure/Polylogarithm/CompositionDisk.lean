/- GID: D5/S3/AnalyticClosure/Polylogarithm/CompositionDisk
   generality: G
   mirror-B: D5/B/S3/AnalyticClosure/Polylogarithm/CompositionDisk
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict positive-composition coefficients and their unit-disk scalar series. -/

import D5.S3.Weil.Probability.AnalyticLogarithmicContinuation
import Mathlib.Data.PNat.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators NNReal ENNReal Topology

namespace D5.S3.AnalyticClosure.Polylogarithm.CompositionDisk

/-- Xu--Zhao, equation (7): the finite strict nested sum, with largest index at most N. -/
def H : List ℕ+ → ℕ → ℝ
  | [], _ => 1
  | k :: ks, N => ∑ m ∈ Finset.range N, H ks m / ((m + 1 : ℕ) : ℝ) ^ (k : ℕ)

/-- A strict positive tuple: choose m+1 at the current bound N, then recurse below m+1. -/
def StrictIndices : ℕ → ℕ → Type
  | 0, _ => PUnit
  | r + 1, N => (m : Fin N) × StrictIndices r m.val

instance strictIndicesFintype (r N : ℕ) : Fintype (StrictIndices r N) := by
  induction r generalizing N with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ r ih =>
    change Fintype ((m : Fin N) × StrictIndices r m.val)
    letI : ∀ m : Fin N, Fintype (StrictIndices r m.val) := fun m => ih m.val
    infer_instance

/-- The reciprocal product over the strict tuple, using the source's exponent order. -/
def strictWeight : (ks : List ℕ+) → (N : ℕ) → StrictIndices ks.length N → ℝ
  | [], _, _ => 1
  | k :: ks, _, ⟨m, is⟩ =>
      strictWeight ks m.val is / ((m.val + 1 : ℕ) : ℝ) ^ (k : ℕ)

/-- Equation (7) with independent dependent-sum indices n1 > ... > nd > 0. -/
def strictNestedSeries (head : ℕ+) (tail : List ℕ+) (z : ℂ) : ℂ :=
  ∑' n : ℕ, (((∑ i : StrictIndices tail.length n, strictWeight tail n i) /
    ((n + 1 : ℕ) : ℝ) ^ (head : ℕ) : ℝ) : ℂ) * z ^ (n + 1)

/-- Product along the unique minimal strict tuple (length, ..., 1). -/
def leading : List ℕ+ → ℝ
  | [] => 1
  | k :: ks => leading ks / ((ks.length + 1 : ℕ) : ℝ) ^ (k : ℕ)

def depth (tail : List ℕ+) : ℕ := tail.length + 1

/-- Coefficients after removing the exact depth power of z in equation (7). -/
def coefficient (head : ℕ+) (tail : List ℕ+) (n : ℕ) : ℝ :=
  H tail (n + tail.length) / ((n + depth tail : ℕ) : ℝ) ^ (head : ℕ)

def normalized (head : ℕ+) (tail : List ℕ+) (z : ℂ) : ℂ :=
  ∑' n : ℕ, (coefficient head tail n : ℂ) * z ^ n

/-- The source series grouped by its largest strict index. The empty word is 1. -/
def source : List ℕ+ → ℂ → ℂ
  | [], _ => 1
  | head :: tail, z =>
      ∑' n : ℕ, ((H tail n / ((n + 1 : ℕ) : ℝ) ^ (head : ℕ) : ℝ) : ℂ) *
        z ^ (n + 1)

def li (head : ℕ+) (tail : List ℕ+) (z : ℂ) : ℂ :=
  z ^ depth tail * normalized head tail z

/-- Assign the removable value explicitly; complex division is total at zero. -/
def logarithmicDerivative (head : ℕ+) (tail : List ℕ+) (z : ℂ) : ℂ :=
  if z = 0 then (depth tail : ℂ) else z * deriv (li head tail) z / li head tail z

/-- The full disk target. This definition asserts no proof of its inhabitance. -/
def diskStatement : Prop :=
  ∀ (head : ℕ+) (tail : List ℕ+),
    (∀ z : ℂ, ‖z‖ < 1 →
      Summable (fun n : ℕ => ‖(coefficient head tail n : ℂ) * z ^ n‖)) ∧
    AnalyticOnNhd ℂ (normalized head tail) (Metric.ball 0 1) ∧
    (∀ z : ℂ, ‖z‖ < 1 → normalized head tail z ≠ 0) ∧
    AnalyticOnNhd ℂ (logarithmicDerivative head tail) (Metric.ball 0 1) ∧
    (∀ z : ℂ, ‖z‖ < 1 → 0 < (logarithmicDerivative head tail z).re)

/-- The recursive strict-index sum has polynomial growth, vanishes below its depth,
and has the positive minimal-tuple coefficient at its first nonzero index. -/
theorem source_coefficient_control : ∀ (ks : List ℕ+) (N : ℕ),
    0 ≤ H ks N ∧ H ks N ≤ (N : ℝ) ^ ks.length ∧
    (N < ks.length → H ks N = 0) ∧
    (ks.length ≤ N → 0 < H ks N) ∧ H ks ks.length = leading ks := by
  intro ks
  induction ks with
  | nil => intro N; simp [H, leading]
  | cons k ks ih =>
    intro N
    have hn : ∀ m, 0 ≤ H ks m / ((m + 1 : ℕ) : ℝ) ^ (k : ℕ) := by
      intro m
      exact div_nonneg (ih m).1 (by positivity)
    have hb : H (k :: ks) N ≤ (N : ℝ) ^ (ks.length + 1) := by
      calc
        H (k :: ks) N ≤ ∑ _m ∈ Finset.range N, (N : ℝ) ^ ks.length := by
          apply Finset.sum_le_sum
          intro m hm
          have hmN : (m : ℝ) ≤ N := by exact_mod_cast (Finset.mem_range.mp hm).le
          have hd : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ (k : ℕ) :=
            one_le_pow₀ (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m))
          exact (div_le_self (ih m).1 hd).trans
            ((ih m).2.1.trans (pow_le_pow_left₀ (by positivity) hmN _))
        _ = (N : ℝ) ^ (ks.length + 1) := by simp [pow_succ, mul_comm]
    have hz : N < (k :: ks).length → H (k :: ks) N = 0 := by
      intro hN
      apply Finset.sum_eq_zero
      intro m hm
      have hmL : m < ks.length := by
        simp only [List.length_cons] at hN
        have := Finset.mem_range.mp hm
        omega
      rw [(ih m).2.2.1 hmL, zero_div]
    have hp : (k :: ks).length ≤ N → 0 < H (k :: ks) N := by
      intro hN
      apply Finset.sum_pos'
      · exact fun m _ => hn m
      · refine ⟨ks.length, Finset.mem_range.mpr ?_, ?_⟩
        · simp only [List.length_cons] at hN; omega
        · exact div_pos ((ih ks.length).2.2.2.1 le_rfl) (by positivity)
    have hl : H (k :: ks) (k :: ks).length = leading (k :: ks) := by
      simp only [H, List.length_cons, Finset.sum_range_succ, leading]
      have hzero : (∑ m ∈ Finset.range ks.length,
          H ks m / ((m + 1 : ℕ) : ℝ) ^ (k : ℕ)) = 0 := by
        apply Finset.sum_eq_zero
        intro m hm
        rw [(ih m).2.2.1 (Finset.mem_range.mp hm), zero_div]
      rw [hzero, zero_add, (ih ks.length).2.2.2.2]
    exact ⟨Finset.sum_nonneg (fun m _ => hn m), hb, hz, hp, hl⟩

/-- Absolute convergence and the exact source normalization for every positive composition.
No recurrence or zero-free hypothesis is used. -/
theorem source_series (head : ℕ+) (tail : List ℕ+) :
    (∀ n, 0 < coefficient head tail n) ∧
    normalized head tail 0 = (leading (head :: tail) : ℂ) ∧
    (∀ z : ℂ, ‖z‖ < 1 →
      Summable (fun n : ℕ => ‖(coefficient head tail n : ℂ) * z ^ n‖)) ∧
    AnalyticOnNhd ℂ (normalized head tail) (Metric.ball 0 1) ∧
    (∀ z : ℂ, ‖z‖ < 1 → li head tail z = source (head :: tail) z) ∧
    analyticOrderAt (li head tail) 0 = (depth tail : ℕ∞) ∧
    (∀ z : ℂ, ‖z‖ < 1 → li head tail z = strictNestedSeries head tail z) := by
  have hcpos : ∀ n, 0 < coefficient head tail n := by
    intro n
    exact div_pos ((source_coefficient_control tail (n + tail.length)).2.2.2.1
      (Nat.le_add_left _ _)) (by unfold depth; positivity)
  have hcbound : ∀ n, coefficient head tail n ≤ (n + depth tail : ℕ) ^ tail.length := by
    intro n
    have hd : (1 : ℝ) ≤ ((n + depth tail : ℕ) : ℝ) ^ (head : ℕ) := by
      apply one_le_pow₀
      exact_mod_cast (show 1 ≤ n + depth tail by unfold depth; omega)
    exact (div_le_self (source_coefficient_control tail _).1 hd).trans
      ((source_coefficient_control tail _).2.1.trans
        (pow_le_pow_left₀ (by positivity) (by unfold depth; push_cast; linarith) _))
  have hpoly : ∀ (k c : ℕ) (r : ℝ), 0 ≤ r → r < 1 →
      Summable (fun n : ℕ => ((n + c : ℕ) : ℝ) ^ k * r ^ n) := by
    intro k c r hr hr1
    by_cases hr0 : r = 0
    · subst r
      simpa using (summable_nat_add_iff 1 (f := fun n : ℕ =>
        ((n + c : ℕ) : ℝ) ^ k * (0 : ℝ) ^ n)).mp (by simp)
    · have hnorm : ‖r‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hr] using hr1
      have hs0 : Summable (fun n : ℕ => (n : ℝ) ^ k * r ^ n) :=
        summable_pow_mul_geometric_of_norm_lt_one k hnorm
      have hs : Summable (fun n : ℕ => ((n + c : ℕ) : ℝ) ^ k * r ^ (n + c)) :=
        (summable_nat_add_iff c).mpr hs0
      apply (hs.mul_right (r ^ c)⁻¹).congr
      intro n
      simp only [pow_add]
      field_simp [hr0]
  have hsum : ∀ r : ℝ≥0, r < 1 →
      Summable (fun n => ‖(coefficient head tail n : ℂ)‖ * (r : ℝ) ^ n) := by
    intro r hr
    apply Summable.of_nonneg_of_le
      (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg r.property n))
      (fun n => ?_) (hpoly tail.length (depth tail) r r.property hr)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hcpos n)]
    exact mul_le_mul_of_nonneg_right (hcbound n) (pow_nonneg r.property n)
  have habs : ∀ z : ℂ, ‖z‖ < 1 →
      Summable (fun n : ℕ => ‖(coefficient head tail n : ℂ) * z ^ n‖) := by
    intro z hz
    simpa only [norm_mul, norm_pow, coe_nnnorm] using hsum ‖z‖₊ hz
  have ha : AnalyticOnNhd ℂ (normalized head tail) (Metric.ball 0 1) :=
    D5.S3.Weil.Probability.AnalyticLogarithmicContinuation.scalar_series_analytic_unit_disk
      (fun n => (coefficient head tail n : ℂ)) hsum
  have hvalue : normalized head tail 0 = (coefficient head tail 0 : ℂ) := by
    unfold normalized
    rw [tsum_eq_single 0 (fun n hn => by simp [zero_pow hn])]
    simp
  have hzero : normalized head tail 0 = (leading (head :: tail) : ℂ) := by
    rw [hvalue]
    simp [coefficient, depth,
      (source_coefficient_control tail tail.length).2.2.2.2, leading]
  have hsource : ∀ z : ℂ, ‖z‖ < 1 → li head tail z = source (head :: tail) z := by
    intro z hz
    let b : ℕ → ℂ := fun n =>
      ((H tail n / ((n + 1 : ℕ) : ℝ) ^ (head : ℕ) : ℝ) : ℂ) * z ^ (n + 1)
    have hbs : Summable b := by
      apply Summable.of_norm_bounded
        ((hpoly tail.length 0 ‖z‖ (norm_nonneg _) hz).mul_right ‖z‖)
      intro n
      have hnn := (source_coefficient_control tail n).1
      have hdd : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ (head : ℕ) :=
        one_le_pow₀ (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
      dsimp [b]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hnn
        (by positivity)), norm_pow, pow_succ]
      simpa only [Nat.add_zero, pow_succ, mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_of_nonneg_right ((div_le_self hnn hdd).trans
          (source_coefficient_control tail n).2.1) (pow_nonneg (norm_nonneg z) (n + 1))
    have hprefix : ∑ n ∈ Finset.range tail.length, b n = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      simp [b, (source_coefficient_control tail n).2.2.1 (Finset.mem_range.mp hn)]
    have heq := hbs.sum_add_tsum_nat_add tail.length
    rw [hprefix, zero_add] at heq
    rw [li, normalized, source, ← heq, ← tsum_mul_left]
    apply tsum_congr
    intro n
    simp only [b, coefficient, depth, Nat.add_assoc, pow_add, pow_one]
    ring
  have ha0 := ha 0 (by simp)
  have hn0 : normalized head tail 0 ≠ 0 := by
    rw [hvalue]
    exact_mod_cast ne_of_gt (hcpos 0)
  refine ⟨hcpos, hzero, habs, ha, hsource, ?_, ?_⟩
  · exact (analyticAt_id.pow (depth tail) |>.mul ha0).analyticOrderAt_eq_natCast.mpr
      ⟨normalized head tail, ha0, hn0, by
        filter_upwards [] with z
        simp [smul_eq_mul]⟩
  · have hstrict : ∀ (ks : List ℕ+) (N : ℕ),
        H ks N = ∑ i : StrictIndices ks.length N, strictWeight ks N i := by
      intro ks
      induction ks with
      | nil =>
        intro N
        change (1 : ℝ) = ∑ _i : PUnit, (1 : ℝ)
        simp
      | cons k ks ih =>
        intro N
        change (∑ m ∈ Finset.range N, H ks m / ((m + 1 : ℕ) : ℝ) ^ (k : ℕ)) =
          ∑ p : (m : Fin N) × StrictIndices ks.length m.val,
            strictWeight ks p.1.val p.2 / ((p.1.val + 1 : ℕ) : ℝ) ^ (k : ℕ)
        rw [Fintype.sum_sigma]
        simp_rw [div_eq_mul_inv, ← Finset.sum_mul, ← ih]
        exact (Fin.sum_univ_eq_sum_range _ N).symm
    intro z hz
    rw [hsource z hz]
    unfold source strictNestedSeries
    apply tsum_congr
    intro n
    rw [hstrict tail n]

#print axioms source_coefficient_control
#print axioms source_series

end D5.S3.AnalyticClosure.Polylogarithm.CompositionDisk
