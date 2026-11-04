/- GID: D5/S0/Asymptotics/GeneratingFunctions/KotesovecA022629
   generality: I
   mirror-B: D5/B/S0/Asymptotics/GeneratingFunctions/KotesovecA022629
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Weighted distinct-partition coefficients satisfy Kotesovec's logarithmic limit. -/

/-
admission_basis: open-problem-resolution (#21434; Proved).
Direct frozen dependencies: none (only pinned Mathlib).
escape_witness: none.
proof_shape: subset_monomial = bind-only; consumers: coefficient_expansion.
proof_shape: coefficient_expansion = bind-only; consumers: coefficient_pos, weighted_distinct_subset_log_sandwich.
proof_shape: triangle_twice = bind-only; consumers: cardinal_triangle_le, triangle_ge, index_real_bounds.
proof_shape: cardinal_triangle_le = bind-only; consumers: product_log_upper.
proof_shape: index_spec = bind-only; consumers: factorial_witness, index_real_bounds.
proof_shape: index_pos = bind-only; consumers: factorial_witness, factorial_log_root_lower.
proof_shape: triangle_ge = bind-only; consumers: index_next, factorial_witness.
proof_shape: index_next = bind-only; consumers: index_real_bounds.
proof_shape: index_le = bind-only; consumers: factorial_witness.
proof_shape: exp_sum_bound = bind-only; consumers: count_exp_bound.
proof_shape: count_exp_bound = bind-only; consumers: count_log_bound.
proof_shape: count_log_bound = bind-only; consumers: weighted_distinct_subset_log_sandwich.
proof_shape: product_log_upper = bind-only; consumers: weighted_distinct_subset_log_sandwich.
proof_shape: factorial_witness = bind-only; consumers: coefficient_pos, weighted_distinct_subset_log_sandwich.
proof_shape: factorial_log_lower = bind-only; consumers: factorial_log_root_lower.
proof_shape: index_real_bounds = bind-only; consumers: factorial_log_root_lower.
proof_shape: factorial_log_root_lower = bind-only; consumers: weighted_distinct_subset_log_sandwich.
proof_shape: ratio_of_sqrt_log_error = bind-only; consumers: all_exponents.
proof_shape: coefficient_pos = bind-only; consumers: weighted_distinct_subset_log_sandwich.
proof_shape: weighted_distinct_subset_log_sandwich = bind-only; consumers: all_exponents.
proof_shape: all_exponents = bind-only; consumers: KotesovecA022629.result, KotesovecA092484.result, KotesovecA265840.result, KotesovecA265841.result, KotesovecA265842.result.
proof_shape: result = bind-only; external named settlement.
The general coefficient expression is inline; a retains the source expression.
The triangular sum is inline: DivisorNimBoundArithmetic.triangle is at S3.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21754.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Sum
import Mathlib.Algebra.Order.Group.Int.Sum
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Order.Interval.Finset.SuccPred

open scoped BigOperators Topology
open Finset Polynomial Filter

namespace D5.S0.Asymptotics.GeneratingFunctions.KotesovecA022629

/-- The degree-n coefficient of the source's locally finite product. -/
noncomputable def a (n : ℕ) : ℕ :=
  (∏ k ∈ Finset.Icc 1 n,
    (1 + Polynomial.C (k ^ 1) * Polynomial.X ^ k : Polynomial ℕ)).coeff n

/-- The OEIS conjecture; the limit is along all natural indices. -/
def claim : Prop :=
  Filter.Tendsto
    (fun n : ℕ => Real.log (a n : ℝ) / (Real.sqrt ((n : ℝ) / 2) * (Real.log (2 * (n : ℝ)) - 2)))
    Filter.atTop (nhds (1 : ℝ))

private def partitions (n : ℕ) : Finset (Finset ℕ) :=
  ((Icc 1 n).powerset).filter (fun s => ∑ k ∈ s, k = n)

private theorem subset_monomial (r : ℕ) (s : Finset ℕ) :
    (∏ k ∈ s, (C (k ^ r) * X ^ k : Polynomial ℕ)) =
      C ((∏ k ∈ s, k) ^ r) * X ^ (∑ k ∈ s, k) := by
  rw [Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow, Finset.prod_pow_eq_pow_sum]

private theorem coefficient_expansion (r n : ℕ) :
    ((∏ k ∈ Finset.Icc 1 n,
      (1 + Polynomial.C (k ^ r) * Polynomial.X ^ k : Polynomial ℕ)).coeff n) = ∑ s ∈ partitions n, (∏ k ∈ s, k) ^ r := by
  classical
  unfold partitions
  rw [Finset.prod_one_add]
  simp_rw [subset_monomial, finsetSum_coeff, coeff_C_mul_X_pow]
  simp [Finset.sum_filter, eq_comm]


private theorem triangle_twice (m : ℕ) : 2 * (∑ k ∈ Icc 1 m, k) = m * (m + 1) := by
  have heq : (∑ k ∈ range (m + 1), k) = (∑ k ∈ Icc 1 m, k) := by
    simpa [Ico_add_one_right_eq_Icc] using
      (Finset.sum_range_eq_add_Ico (fun k : ℕ => k) (Nat.succ_pos m))
  have h := Finset.sum_range_id_mul_two (m + 1)
  rw [heq] at h
  simpa [mul_comm] using h

private theorem cardinal_triangle_le (s : Finset ℕ) (hp : ∀ k ∈ s, 1 ≤ k) :
    s.card * (s.card + 1) ≤ 2 * ∑ k ∈ s, k := by
  classical
  have hl : ∀ k ∈ s.map (Nat.castEmbedding : ℕ ↪ ℤ), (1 : ℤ) ≤ k := by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := mem_map.mp hk
    change (1 : ℤ) ≤ (j : ℤ)
    exact_mod_cast hp j hj
  have h := Finset.sum_range_le_sum hl
  simp only [card_map, sum_map, Nat.castEmbedding_apply] at h
  have hnat : (∑ i ∈ range s.card, (1 + i)) ≤ ∑ k ∈ s, k := by
    have hc : ((∑ i ∈ range s.card, (1 + i) : ℕ) : ℤ) ≤
        ((∑ k ∈ s, k : ℕ) : ℤ) := by
      simpa only [Nat.cast_sum, Nat.cast_add, Nat.cast_one] using h
    exact_mod_cast hc
  have heq : (∑ i ∈ range s.card, (1 + i)) = (∑ k ∈ Icc 1 s.card, k) := by
    simpa [Nat.Ico_zero_eq_range, Ico_add_one_right_eq_Icc, add_comm] using
      (Finset.sum_Ico_add' (fun k : ℕ => k) 0 s.card 1)
  rw [heq] at hnat
  have ht := triangle_twice s.card
  omega

private def index (n : ℕ) : ℕ := Nat.findGreatest (fun m => (∑ k ∈ Icc 1 m, k) ≤ n) n

private theorem index_spec (n : ℕ) : (∑ k ∈ Icc 1 (index n), k) ≤ n := by
  exact Nat.findGreatest_spec (P := fun m => (∑ k ∈ Icc 1 m, k) ≤ n) (m := 0)
    (Nat.zero_le n) (by simp)

private theorem index_pos (n : ℕ) (hn : 1 ≤ n) : 1 ≤ index n := by
  exact Nat.le_findGreatest hn (by simpa using hn)

private theorem triangle_ge (m : ℕ) : m ≤ (∑ k ∈ Icc 1 m, k) := by
  have h := triangle_twice m
  generalize (∑ k ∈ Icc 1 m, k) = t at *
  nlinarith

private theorem index_next (n : ℕ) : n < (∑ k ∈ Icc 1 (index n + 1), k) := by
  by_cases hb : index n + 1 ≤ n
  · exact lt_of_not_ge (Nat.findGreatest_is_greatest (P := fun m => (∑ k ∈ Icc 1 m, k) ≤ n) (n := n)
      (k := index n + 1) (Nat.lt_succ_self _) hb)
  · have hi := triangle_ge (index n + 1)
    omega

private theorem index_le (n : ℕ) : index n ≤ n := Nat.findGreatest_le n

private theorem exp_sum_bound (t : ℝ) (ht : 0 < t) (n : ℕ) :
    (∑ k ∈ Icc 1 n, Real.exp (-t * k)) ≤ 1 / t := by
  let q := Real.exp (-t)
  have hqpos : 0 < q := Real.exp_pos _
  have hqone : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hden : 0 < 1 - q := by linarith
  have hp (k : ℕ) : q ^ k = Real.exp (-t * k) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hg := geom_sum_Ico_le_of_lt_one (m := 1) (n := n + 1) hqpos.le hqone
  simp_rw [hp] at hg
  rw [Ico_add_one_right_eq_Icc] at hg
  have he : (Real.exp t - 1) * q = 1 - q := by
    dsimp only [q]
    rw [sub_mul, one_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hsmall := mul_le_mul_of_nonneg_right (Real.add_one_le_exp t) hqpos.le
  have hqt : t * q ≤ 1 - q := by nlinarith
  have hS : 0 ≤ ∑ k ∈ Icc 1 n, Real.exp (-t * k) :=
    sum_nonneg (fun _ _ => (Real.exp_pos _).le)
  have hgeom : (∑ k ∈ Icc 1 n, Real.exp (-t * k)) * (1 - q) ≤ q := by
    have hh := (le_div_iff₀ hden).mp hg
    simpa only [Nat.cast_one, mul_one] using hh
  have hmul := mul_le_mul_of_nonneg_left hqt hS
  have hfinal : ((∑ k ∈ Icc 1 n, Real.exp (-t * k)) * t) * q ≤ q := by
    nlinarith
  have hcancel := (le_div_iff₀ hqpos).mpr hfinal
  apply (le_div_iff₀ ht).mpr
  simpa only [div_self hqpos.ne'] using hcancel

private theorem count_exp_bound (n : ℕ) (t : ℝ) (ht : 0 < t) :
    ((partitions n).card : ℝ) * Real.exp (-t * n) ≤ Real.exp (1 / t) := by
  classical
  have hsum : ((partitions n).card : ℝ) * Real.exp (-t * n) =
      ∑ s ∈ partitions n, ∏ k ∈ s, Real.exp (-t * k) := by
    have hterm (s : Finset ℕ) (hs : s ∈ partitions n) :
        (∏ k ∈ s, Real.exp (-t * k)) = Real.exp (-t * n) := by
      rw [← Real.exp_sum, ← mul_sum]
      have hn : ∑ k ∈ s, k = n := (mem_filter.mp hs).2
      rw [← Nat.cast_sum, hn]
    calc
      _ = ∑ _s ∈ partitions n, Real.exp (-t * n) := by simp
      _ = _ := sum_congr rfl (fun s hs => (hterm s hs).symm)
  calc
    _ = ∑ s ∈ partitions n, ∏ k ∈ s, Real.exp (-t * k) := hsum
    _ ≤ ∑ s ∈ (Icc 1 n).powerset, ∏ k ∈ s, Real.exp (-t * k) := by
      apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      intro s hs hsn
      positivity
    _ = ∏ k ∈ Icc 1 n, (1 + Real.exp (-t * k)) := (prod_one_add _).symm
    _ ≤ Real.exp (∑ k ∈ Icc 1 n, Real.exp (-t * k)) :=
      Real.prod_one_add_le_exp_sum _ (fun k => (Real.exp_pos _).le)
    _ ≤ Real.exp (1 / t) := Real.exp_le_exp.mpr (exp_sum_bound t ht n)

private theorem count_log_bound (n : ℕ) (hn : 1 ≤ n) :
    Real.log ((partitions n).card : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by
  have hnn : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsq : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnn
  have h := count_exp_bound n (1 / Real.sqrt n) (by positivity)
  have he : ((partitions n).card : ℝ) ≤
      Real.exp (2 * Real.sqrt (n : ℝ)) := by
    have h1 : (1 / Real.sqrt (n : ℝ)) * n = Real.sqrt n := by
      rw [one_div_mul_eq_div, div_eq_iff hsq.ne']
      nlinarith [Real.sq_sqrt hnn.le]
    simp only [neg_mul, h1, one_div_one_div] at h
    have hh := mul_le_mul_of_nonneg_right h (Real.exp_pos (Real.sqrt n)).le
    rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one,
      ← Real.exp_add] at hh
    simpa [two_mul] using hh
  have hp : (partitions n).Nonempty := by
    refine ⟨{n}, mem_filter.mpr ⟨mem_powerset.mpr ?_, by simp⟩⟩
    intro k hk
    simp only [mem_singleton] at hk
    subst k
    exact mem_Icc.mpr ⟨hn, le_rfl⟩
  exact (Real.log_le_iff_le_exp (by exact_mod_cast card_pos.mpr hp)).mpr he

private theorem product_log_upper (s : Finset ℕ) (n : ℕ)
    (hp : ∀ k ∈ s, 1 ≤ k) (hsum : ∑ k ∈ s, k = n) (hn : 2 ≤ n) :
    Real.log ((∏ k ∈ s, k : ℕ) : ℝ) ≤
      Real.sqrt (2 * (n : ℝ)) * (Real.log (Real.sqrt (2 * (n : ℝ)) / 2) + 1) := by
  let R := Real.sqrt (2 * (n : ℝ))
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hR : 0 < R := Real.sqrt_pos.mpr (by positivity)
  have hRsq : R ^ 2 = 2 * (n : ℝ) := Real.sq_sqrt (by positivity)
  have hRtwo : 2 ≤ R := by
    have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hA : 0 < R / 2 := by positivity
  have hlog : 0 ≤ Real.log (R / 2) := Real.log_nonneg (by linarith)
  have hc : (s.card : ℝ) ≤ R := by
    have hh := cardinal_triangle_le s hp
    rw [hsum] at hh
    have hr : (s.card : ℝ) * (s.card + 1) ≤ 2 * n := by exact_mod_cast hh
    have hm : 0 ≤ (s.card : ℝ) := by positivity
    nlinarith
  have ht (k : ℕ) (hk : k ∈ s) :
      Real.log (k : ℝ) ≤ Real.log (R / 2) + (k : ℝ) / (R / 2) - 1 := by
    have hkpos : 0 < (k : ℝ) := by exact_mod_cast hp k hk
    have hl := Real.log_le_sub_one_of_pos (div_pos hkpos hA)
    rw [Real.log_div hkpos.ne' hA.ne'] at hl
    linarith
  have hslog : Real.log ((∏ k ∈ s, k : ℕ) : ℝ) = ∑ k ∈ s, Real.log (k : ℝ) := by
    rw [Nat.cast_prod]
    exact Real.log_prod (fun k hk => by
      have : 0 < (k : ℝ) := by exact_mod_cast hp k hk
      exact this.ne')
  have htotal := sum_le_sum ht
  have hsumR : (∑ k ∈ s, (k : ℝ)) = (n : ℝ) := by
    rw [← Nat.cast_sum, hsum]
  simp only [sum_sub_distrib, sum_add_distrib, sum_const, nsmul_eq_mul,
    ← sum_div] at htotal
  have hquot : (n : ℝ) / (R / 2) = R := by
    apply (div_eq_iff hA.ne').mpr
    nlinarith
  rw [hsumR, hquot] at htotal
  have hmono := mul_le_mul_of_nonneg_right hc hlog
  rw [hslog]
  dsimp only [R] at *
  nlinarith

private theorem factorial_witness (n : ℕ) (hn : 1 ≤ n) :
    ∃ s : Finset ℕ, s ⊆ Icc 1 n ∧ (∑ k ∈ s, k) = n ∧
      (index n).factorial ≤ ∏ k ∈ s, k := by
  classical
  let m := index n
  let d := n - (∑ k ∈ Icc 1 m, k)
  let s := insert (m + d) (Icc 1 (m - 1))
  have hm : 1 ≤ m := index_pos n hn
  have htri : (∑ k ∈ Icc 1 m, k) ≤ n := index_spec n
  have hmt : m ≤ (∑ k ∈ Icc 1 m, k) := triangle_ge m
  have hmn : m ≤ n := index_le n
  have hmd : m + d ≤ n := by dsimp [d]; omega
  have hlast : m + d ∉ Icc 1 (m - 1) := by simp; omega
  have hI : Icc 1 m = insert m (Icc 1 (m - 1)) := by
    simpa using (Finset.insert_Icc_pred_right_eq_Icc (a := 1) (b := m) hm).symm
  have hnot : m ∉ Icc 1 (m - 1) := by simp; omega
  have hrec : (∑ k ∈ Icc 1 m, k) = m + (∑ k ∈ Icc 1 (m - 1), k) := by
    rw [hI, sum_insert hnot]
  have hp : (∏ k ∈ Icc 1 (m - 1), k) = (m - 1).factorial := by
    simpa only [Finset.Ico_add_one_right_eq_Icc] using prod_Ico_id_eq_factorial (m - 1)
  refine ⟨s, ?_, ?_, ?_⟩
  · intro k hk
    rcases mem_insert.mp hk with hk | hk
    · subst k
      exact mem_Icc.mpr ⟨by omega, hmd⟩
    · exact mem_Icc.mpr ⟨(mem_Icc.mp hk).1, by have := (mem_Icc.mp hk).2; omega⟩
  · change (∑ k ∈ insert (m + d) (Icc 1 (m - 1)), k) = n
    rw [sum_insert hlast]
    change m + d + (∑ k ∈ Icc 1 (m - 1), k) = n
    dsimp [d]
    omega
  · change m.factorial ≤ ∏ k ∈ insert (m + d) (Icc 1 (m - 1)), k
    rw [prod_insert hlast, hp]
    have hfac : m.factorial = m * (m - 1).factorial := by
      have hh := Nat.factorial_succ (m - 1)
      rw [Nat.sub_add_cancel hm] at hh
      exact hh
    rw [hfac]
    exact Nat.mul_le_mul_right _ (Nat.le_add_right m d)

private theorem factorial_log_lower (m : ℕ) (hm : 1 ≤ m) :
    (m : ℝ) * Real.log m - m + 1 ≤ Real.log (m.factorial : ℝ) := by
  have hmono : MonotoneOn Real.log (Set.Icc (1 : ℝ) m) := by
    apply Real.strictMonoOn_log.monotoneOn.mono
    intro x hx
    have := hx.1
    simpa only [Set.mem_Ioi] using (show 0 < x by linarith)
  have hi := MonotoneOn.integral_le_sum_Ico (f := Real.log) hm
    (by simpa only [Nat.cast_one] using hmono)
  rw [Finset.sum_Ico_eq_sub _ hm, sum_range_one] at hi
  simp only [zero_add, Real.log_one, sub_zero,
    Nat.cast_add, Nat.cast_one] at hi
  rw [Real.sum_log_add_one_eq_log_factorial] at hi
  simpa [integral_log] using hi

private theorem index_real_bounds (n : ℕ) (hn : 1 ≤ n) :
    (index n : ℝ) ≤ Real.sqrt (2 * (n : ℝ)) ∧
      Real.sqrt (2 * (n : ℝ)) < (index n : ℝ) + 2 := by
  let R := Real.sqrt (2 * (n : ℝ))
  have hm : 1 ≤ index n := index_pos n hn
  have h0 : 0 ≤ R := Real.sqrt_nonneg _
  have hR : R ^ 2 = 2 * (n : ℝ) := Real.sq_sqrt (by positivity)
  have htri := index_spec n
  have hnext := index_next n
  have h1 := triangle_twice (index n)
  have h2 := triangle_twice (index n + 1)
  have htriR : ((∑ k ∈ Icc 1 (index n), k : ℕ) : ℝ) ≤ n := by exact_mod_cast htri
  have hnextR : (n : ℝ) < ((∑ k ∈ Icc 1 (index n + 1), k : ℕ) : ℝ) := by exact_mod_cast hnext
  have h1R : 2 * ((∑ k ∈ Icc 1 (index n), k : ℕ) : ℝ) = (index n : ℝ) * (index n + 1) := by
    exact_mod_cast h1
  have h2R : 2 * ((∑ k ∈ Icc 1 (index n + 1), k : ℕ) : ℝ) = (index n + 1 : ℝ) * (index n + 2) := by
    exact_mod_cast h2
  constructor <;> dsimp only [R] at * <;> nlinarith [Nat.cast_nonneg (α := ℝ) (index n)]

private theorem factorial_log_root_lower (n : ℕ) (hn : 1 ≤ n) :
    Real.sqrt (2 * (n : ℝ)) * (Real.log (Real.sqrt (2 * (n : ℝ))) - 1) -
      2 * Real.log (Real.sqrt (2 * (n : ℝ))) - 1 ≤
        Real.log ((index n).factorial : ℝ) := by
  let m := (index n : ℝ)
  let R := Real.sqrt (2 * (n : ℝ))
  have hmnat : 1 ≤ index n := index_pos n hn
  have hm : 1 ≤ m := by
    change (1 : ℝ) ≤ (index n : ℝ)
    exact_mod_cast hmnat
  have hmp : 0 < m := by linarith
  have hbounds := index_real_bounds n hn
  change m ≤ R ∧ R < m + 2 at hbounds
  have hRp : 0 < R := lt_of_lt_of_le hmp hbounds.1
  have hlR : 0 ≤ Real.log R := Real.log_nonneg (by linarith [hbounds.1])
  have hlog := Real.log_le_sub_one_of_pos (div_pos hRp hmp)
  rw [Real.log_div hRp.ne' hmp.ne'] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog hmp.le
  have hcancel : m * (R / m - 1) = R - m := by field_simp [hmp.ne']
  rw [hcancel] at hmul
  have hgap := mul_le_mul_of_nonneg_right (le_of_lt hbounds.2) hlR
  have hfac := factorial_log_lower (index n) hmnat
  change m * Real.log m - m + 1 ≤ _ at hfac
  change R * (Real.log R - 1) - 2 * Real.log R - 1 ≤ _
  nlinarith

private theorem ratio_of_sqrt_log_error (r K : ℝ) (hr : 0 < r) (f : ℕ → ℝ)
    (h : ∀ᶠ n : ℕ in atTop, |f n - r * Real.sqrt (2 * (n : ℝ)) *
        (Real.log (Real.sqrt (2 * (n : ℝ))) - 1)| ≤
          K * Real.sqrt (2 * (n : ℝ))) :
    Tendsto (fun n : ℕ => f n /
      (r * Real.sqrt (2 * (n : ℝ)) * (Real.log (Real.sqrt (2 * (n : ℝ))) - 1)))
      atTop (nhds 1) := by
  let R : ℕ → ℝ := fun n => Real.sqrt (2 * (n : ℝ))
  have hR : Tendsto R atTop atTop :=
    Real.tendsto_sqrt_atTop.comp ((tendsto_natCast_atTop_atTop :
      Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have hL : Tendsto (fun n => Real.log (R n) - 1) atTop atTop :=
    by simpa [sub_eq_add_neg] using
      (tendsto_atTop_add_const_right atTop (-1 : ℝ) (Real.tendsto_log_atTop.comp hR))
  have hD : Tendsto (fun n => r * (Real.log (R n) - 1)) atTop atTop :=
    hL.const_mul_atTop hr
  have he : Tendsto (fun n => K / (r * (Real.log (R n) - 1))) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hD
  have hl : Tendsto (fun n => 1 - K / (r * (Real.log (R n) - 1))) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub he
  have hu : Tendsto (fun n => 1 + K / (r * (Real.log (R n) - 1))) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add he
  have hevent : ∀ᶠ n in atTop,
      1 - K / (r * (Real.log (R n) - 1)) ≤
          f n / (r * R n * (Real.log (R n) - 1)) ∧
      f n / (r * R n * (Real.log (R n) - 1)) ≤
          1 + K / (r * (Real.log (R n) - 1)) := by
    filter_upwards [h, hR.eventually_gt_atTop 0, hL.eventually_gt_atTop 0] with n hn hRn hLn
    change |f n - r * R n * (Real.log (R n) - 1)| ≤ K * R n at hn
    have hB : 0 < r * R n * (Real.log (R n) - 1) := by positivity
    have hc : K * R n / (r * R n * (Real.log (R n) - 1)) =
        K / (r * (Real.log (R n) - 1)) := by
      field_simp [hRn.ne', hr.ne', hLn.ne']
    have ha := abs_le.mp hn
    constructor
    · calc
        _ = (r * R n * (Real.log (R n) - 1) - K * R n) /
            (r * R n * (Real.log (R n) - 1)) := by
          rw [sub_div, div_self hB.ne', hc]
        _ ≤ _ := (div_le_div_iff_of_pos_right hB).mpr (by linarith)
    · calc
        _ ≤ (r * R n * (Real.log (R n) - 1) + K * R n) /
            (r * R n * (Real.log (R n) - 1)) :=
          (div_le_div_iff_of_pos_right hB).mpr (by linarith)
        _ = _ := by rw [add_div, div_self hB.ne', hc]
  change Tendsto (fun n => f n / (r * R n * (Real.log (R n) - 1))) atTop (nhds 1)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu
    (hevent.mono (fun _ hn => hn.1)) (hevent.mono (fun _ hn => hn.2))



private theorem coefficient_pos (r n : ℕ) (hn : 1 ≤ n) : 0 < ((∏ k ∈ Finset.Icc 1 n,
      (1 + Polynomial.C (k ^ r) * Polynomial.X ^ k : Polynomial ℕ)).coeff n) := by
  obtain ⟨s, hs, hsum, hprod⟩ := factorial_witness n hn
  have hmem : s ∈ partitions n := mem_filter.mpr ⟨mem_powerset.mpr hs, hsum⟩
  have hweight : (∏ k ∈ s, k) ^ r ≤ ((∏ k ∈ Finset.Icc 1 n,
      (1 + Polynomial.C (k ^ r) * Polynomial.X ^ k : Polynomial ℕ)).coeff n) := by
    rw [coefficient_expansion]
    exact single_le_sum (f := fun t : Finset ℕ => (∏ k ∈ t, k) ^ r) (fun t ht => Nat.zero_le _) hmem
  have hp : 0 < ∏ k ∈ s, k := lt_of_lt_of_le (Nat.factorial_pos _) hprod
  exact lt_of_lt_of_le (pow_pos hp r) hweight

private theorem weighted_distinct_subset_log_sandwich (r n : ℕ) (hr : 1 ≤ r) (hn : 2 ≤ n) :
    (let R := Real.sqrt (2 * (n : ℝ))
     let B := (r : ℝ) * R * (Real.log R - 1)
     B - 2 * r * Real.log R - r ≤ Real.log (((∏ k ∈ Finset.Icc 1 n,
      (1 + Polynomial.C (k ^ r) * Polynomial.X ^ k : Polynomial ℕ)).coeff n) : ℝ) ∧
     Real.log (((∏ k ∈ Finset.Icc 1 n,
      (1 + Polynomial.C (k ^ r) * Polynomial.X ^ k : Polynomial ℕ)).coeff n) : ℝ) ≤ B + r * R * (2 - Real.log 2) + 2 * Real.sqrt n) := by
  let R := Real.sqrt (2 * (n : ℝ))
  let U := R * (Real.log (R / 2) + 1)
  have hnp : 1 ≤ n := by omega
  have hap : 0 < (((∏ k ∈ Finset.Icc 1 n,
      (1 + Polynomial.C (k ^ r) * Polynomial.X ^ k : Polynomial ℕ)).coeff n) : ℝ) := by exact_mod_cast coefficient_pos r n hnp
  have hrR : 0 ≤ (r : ℝ) := by positivity
  have hRp : 0 < R := Real.sqrt_pos.mpr (by positivity)
  obtain ⟨s, hs, hsum, hprod⟩ := factorial_witness n hnp
  have hmem : s ∈ partitions n := mem_filter.mpr ⟨mem_powerset.mpr hs, hsum⟩
  have hfac : (index n).factorial ^ r ≤ ((∏ k ∈ Finset.Icc 1 n,
      (1 + Polynomial.C (k ^ r) * Polynomial.X ^ k : Polynomial ℕ)).coeff n) := by
    rw [coefficient_expansion]
    exact (pow_le_pow_left' hprod r).trans (single_le_sum (f := fun t : Finset ℕ => (∏ k ∈ t, k) ^ r) (fun t ht => Nat.zero_le _) hmem)
  have hfacR : ((index n).factorial : ℝ) ^ r ≤ (((∏ k ∈ Finset.Icc 1 n,
      (1 + Polynomial.C (k ^ r) * Polynomial.X ^ k : Polynomial ℕ)).coeff n) : ℝ) := by exact_mod_cast hfac
  have hlogfac := Real.log_le_log (by positivity : 0 < ((index n).factorial : ℝ) ^ r) hfacR
  rw [Real.log_pow] at hlogfac
  have hroot := mul_le_mul_of_nonneg_left (factorial_log_root_lower n hnp) hrR
  have hsum_upper : (((∏ k ∈ Finset.Icc 1 n,
      (1 + Polynomial.C (k ^ r) * Polynomial.X ^ k : Polynomial ℕ)).coeff n) : ℝ) ≤ ((partitions n).card : ℝ) * Real.exp (r * U) := by
    rw [coefficient_expansion, Nat.cast_sum]
    calc
      _ ≤ ∑ t ∈ partitions n, Real.exp (r * U) := by
        apply sum_le_sum
        intro t ht
        have htp : ∀ k ∈ t, 1 ≤ k := by
          intro k hk
          exact (mem_Icc.mp ((mem_powerset.mp (mem_filter.mp ht).1) hk)).1
        have hts : ∑ k ∈ t, k = n := (mem_filter.mp ht).2
        have hprodp : 0 < (∏ k ∈ t, k : ℕ) := prod_pos (fun k hk => htp k hk)
        have hlog := product_log_upper t n htp hts hn
        have hpower := mul_le_mul_of_nonneg_left hlog hrR
        rw [Nat.cast_pow]
        apply (Real.log_le_iff_le_exp (by positivity : 0 < ((∏ k ∈ t, k : ℕ) : ℝ) ^ r)).mp
        simpa only [Real.log_pow] using hpower
      _ = _ := by simp
  have hqp : 0 < ((partitions n).card : ℝ) := by
    have hq : 0 < (partitions n).card := card_pos.mpr ⟨s, hmem⟩
    exact_mod_cast hq
  have hupper := Real.log_le_log hap hsum_upper
  rw [Real.log_mul hqp.ne' (Real.exp_ne_zero _), Real.log_exp] at hupper
  have hcount := count_log_bound n hnp
  have hlogdiv : Real.log (R / 2) = Real.log R - Real.log 2 :=
    Real.log_div hRp.ne' (by norm_num)
  constructor
  · nlinarith
  · dsimp only [U] at hupper
    rw [hlogdiv] at hupper
    dsimp only [R] at *
    nlinarith

theorem all_exponents (r : ℕ) (hr : 1 ≤ r) :
    Filter.Tendsto
      (fun n : ℕ => Real.log (((∏ k ∈ Finset.Icc 1 n,
      (1 + Polynomial.C (k ^ r) * Polynomial.X ^ k : Polynomial ℕ)).coeff n) : ℝ) /
        ((r : ℝ) * Real.sqrt ((n : ℝ) / 2) * (Real.log (2 * (n : ℝ)) - 2)))
      Filter.atTop (nhds (1 : ℝ)) := by
  have hrp : 0 < (r : ℝ) := by exact_mod_cast hr
  have he : ∀ᶠ n : ℕ in atTop, |Real.log (((∏ k ∈ Finset.Icc 1 n,
      (1 + Polynomial.C (k ^ r) * Polynomial.X ^ k : Polynomial ℕ)).coeff n) : ℝ) - (r : ℝ) * Real.sqrt (2 * (n : ℝ)) *
        (Real.log (Real.sqrt (2 * (n : ℝ))) - 1)| ≤
          (3 * r + 2 : ℝ) * Real.sqrt (2 * (n : ℝ)) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    let R := Real.sqrt (2 * (n : ℝ))
    have h := weighted_distinct_subset_log_sandwich r n hr hn
    dsimp only at h
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hRp : 0 < R := Real.sqrt_pos.mpr (by positivity)
    have hRone : 1 ≤ R := by
      have hRsq : R ^ 2 = 2 * (n : ℝ) := Real.sq_sqrt (by positivity)
      nlinarith
    have hlog : Real.log R ≤ R := Real.log_le_self hRp.le
    have hrl := mul_le_mul_of_nonneg_left hlog hrp.le
    have hr1 := mul_le_mul_of_nonneg_left hRone hrp.le
    have hsqrt : Real.sqrt (n : ℝ) ≤ R := Real.sqrt_le_sqrt (by linarith)
    have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
    have hx : 0 ≤ (r : ℝ) * R * Real.log 2 := by positivity
    change |Real.log (((∏ k ∈ Finset.Icc 1 n,
      (1 + Polynomial.C (k ^ r) * Polynomial.X ^ k : Polynomial ℕ)).coeff n) : ℝ) - (r : ℝ) * R * (Real.log R - 1)| ≤ (3 * r + 2 : ℝ) * R
    change (r : ℝ) * R * (Real.log R - 1) - 2 * r * Real.log R - r ≤ _ ∧
      _ ≤ (r : ℝ) * R * (Real.log R - 1) + r * R * (2 - Real.log 2) + 2 * Real.sqrt n at h
    rw [abs_le]
    constructor <;> nlinarith
  have hlim := ratio_of_sqrt_log_error (r : ℝ) (3 * r + 2) hrp (fun n => Real.log (((∏ k ∈ Finset.Icc 1 n,
      (1 + Polynomial.C (k ^ r) * Polynomial.X ^ k : Polynomial ℕ)).coeff n) : ℝ)) he
  have hden (n : ℕ) :
      (r : ℝ) * Real.sqrt (2 * (n : ℝ)) * (Real.log (Real.sqrt (2 * (n : ℝ))) - 1) =
        (r : ℝ) * Real.sqrt ((n : ℝ) / 2) * (Real.log (2 * (n : ℝ)) - 2) := by
    have hs : Real.sqrt (2 * (n : ℝ)) = 2 * Real.sqrt ((n : ℝ) / 2) := by
      have h1 := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * n)
      have h2 := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (n : ℝ) / 2)
      have h3 := Real.sqrt_nonneg (2 * (n : ℝ))
      have h4 := Real.sqrt_nonneg ((n : ℝ) / 2)
      nlinarith
    rw [Real.log_sqrt (by positivity), hs]
    ring
  exact hlim.congr (fun n => by rw [hden n])

theorem result : claim := by
  simpa only [claim, a, Nat.cast_one, one_mul] using
    all_exponents 1 (by norm_num)

end D5.S0.Asymptotics.GeneratingFunctions.KotesovecA022629
