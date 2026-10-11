/- GID: D5/S3/Factorization/Combinatorics/MixedPrimeHistoryAsymptotics
   generality: G
   mirror-B: D5/B/S3/Factorization/Combinatorics/MixedPrimeHistoryAsymptotics
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Subcritical geometric control of the actual weighted mixed prime histories. -/

import D5.S3.Factorization.Combinatorics.MixedPrimeHistoryGenerating
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

namespace D5.S3.Factorization.Combinatorics.MixedPrimeHistoryAsymptotics

open D5.S3.Factorization.Combinatorics.MixedPrimeHistoryCount
open D5.S3.Factorization.Combinatorics.MixedPrimeHistoryGenerating
open scoped BigOperators

/-- The prime-supported geometric series, on its disk of convergence. -/
noncomputable def primeSeries {𝕜 : Type*} [NormedField 𝕜] (z : 𝕜) : 𝕜 :=
  ∑' q : ℕ, if q.Prime then z ^ q else 0

private theorem length_lt_endpoint (n : ℕ) (hn : 0 < n)
    (w : List PrimeLetter) (hw : endpoint w = n) : w.length < n := by
  by_cases he : w = []
  · simp [he, hn]
  · have hb := sharp_length_bound w he
    rw [hw] at hb
    omega

private theorem weighted_length_sum (t : ℝ) (n N : ℕ) (hn : 0 < n) (hN : n ≤ N) :
    weightedCount t n = ∑ k ∈ Finset.range N, (lengthCount k n : ℝ) * t ^ k := by
  classical
  let s := (reachable_finite n hn).2.toFinset
  have hmaps : ∀ w ∈ s, w.length ∈ Finset.range N := by
    intro w hw
    have he : endpoint w = n := (reachable_finite n hn).2.mem_toFinset.mp hw
    exact Finset.mem_range.mpr ((length_lt_endpoint n hn w he).trans_le hN)
  rw [weightedCount, dif_pos hn, ← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_congr rfl
  intro k hk
  have hs : (↑(s.filter (fun w => w.length = k)) : Set (List PrimeLetter)) =
      {w | endpoint w = n ∧ w.length = k} := by
    ext w
    simp [s, historyFibre]
  have hc : (s.filter (fun w => w.length = k)).card = lengthCount k n := by
    change _ = ({w : List PrimeLetter | endpoint w = n ∧ w.length = k} : Set _).ncard
    rw [← hs, Set.ncard_coe_finset]
  calc
    ∑ w ∈ s with w.length = k, t ^ w.length =
        ∑ w ∈ s with w.length = k, t ^ k := by
          apply Finset.sum_congr rfl
          intro w hw
          rw [(Finset.mem_filter.mp hw).2]
    _ = _ := by simp [hc]

private theorem weighted_nonneg (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    0 ≤ weightedCount t n := by
  classical
  unfold weightedCount
  split_ifs
  · exact Finset.sum_nonneg (fun _ _ => pow_nonneg ht _)
  · exact le_rfl

private theorem weighted_zero (t : ℝ) : weightedCount t 0 = 0 := by
  simp [weightedCount]

private theorem weighted_one (t : ℝ) : weightedCount t 1 = 1 := by
  rw [weighted_length_sum t 1 1 (by omega) le_rfl]
  have h := mixed_coefficient 1 0 1 (by omega) le_rfl
  simpa [mixedPolynomial] using congrArg (fun x : ℕ => (x : ℝ)) h.symm

private theorem weighted_recurrence (t : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    weightedCount t n = t *
      ((∑ q ∈ (Finset.range n).filter Nat.Prime, weightedCount t (n - q)) +
       (∑ q ∈ n.primeFactors, weightedCount t (n / q))) := by
  classical
  have hz : lengthCount 0 n = 0 := by
    have h := mixed_coefficient n 0 n (by omega) le_rfl
    simpa [mixedPolynomial, Polynomial.coeff_X, show 1 ≠ n by omega] using h.symm
  have hl (k : ℕ) : lengthCount (k + 1) n =
      (∑ q ∈ (Finset.range n).filter Nat.Prime, lengthCount k (n - q)) +
      (∑ q ∈ n.primeFactors, lengthCount k (n / q)) := by
    simpa using length_recurrence (k + 1) n (by omega) hn
  rw [weighted_length_sum t n n (by omega) le_rfl]
  conv_lhs => rw [show Finset.range n = Finset.range ((n - 1) + 1) by congr 1; omega,
    Finset.sum_range_succ']
  simp only [hz, Nat.cast_zero, zero_mul, add_zero]
  simp_rw [hl,
    Nat.cast_add, Nat.cast_sum, add_mul, Finset.sum_mul, pow_succ]
  rw [Finset.sum_add_distrib, Finset.sum_comm, Finset.sum_comm (s := Finset.range (n - 1))]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro q hq
    have hqn := Finset.mem_range.mp (Finset.mem_filter.mp hq).1
    have hqp := (Finset.mem_filter.mp hq).2.pos
    rw [weighted_length_sum t (n - q) (n - 1) (by omega) (by omega), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  · apply Finset.sum_congr rfl
    intro q hq
    have hpos := Nat.div_pos (Nat.le_of_mem_primeFactors hq)
      (Nat.pos_of_mem_primeFactors hq)
    have hlt := Nat.div_lt_self (show 0 < n by omega)
      (Nat.prime_of_mem_primeFactors hq).one_lt
    rw [weighted_length_sum t (n / q) (n - 1) hpos (by omega), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring

private theorem prime_summable (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun q : ℕ => if q.Prime then r ^ q else 0) := by
  apply Summable.of_nonneg_of_le
    (fun q => by split_ifs <;> positivity)
    (fun q => show (if q.Prime then r ^ q else 0) ≤ r ^ q by
      split_ifs
      · exact le_rfl
      · exact pow_nonneg hr q)
    (summable_geometric_of_lt_one hr hr1)

/-- Below the prime-series threshold, one constant controls every actual endpoint. -/
theorem subcritical_bound (t r : ℝ) (ht : 0 < t) (hr : 0 < r) (hr1 : r < 1)
    (hsub : t * primeSeries r < 1) :
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, weightedCount t n * r ^ n ≤ B := by
  classical
  have hs0 : 0 ≤ Real.sqrt r := Real.sqrt_nonneg r
  have hs1 : Real.sqrt r < 1 := by
    simpa using Real.sqrt_lt_sqrt hr.le hr1
  have hlim : Filter.Tendsto
      (fun n : ℕ => t * (primeSeries r + (n : ℝ) * (Real.sqrt r) ^ n))
      Filter.atTop (nhds (t * primeSeries r)) := by
    simpa using (tendsto_self_mul_const_pow_of_lt_one hs0 hs1).const_add
      (primeSeries r) |>.const_mul t
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    ((tendsto_order.mp hlim).2 1 hsub)
  let M := max N 2
  let B := 1 + ∑ k ∈ Finset.range M, weightedCount t k * r ^ k
  have hB : 0 < B := by
    have h := Finset.sum_nonneg (s := Finset.range M)
      (fun k _ => mul_nonneg (weighted_nonneg t ht.le k) (pow_nonneg hr.le k))
    dsimp [B]
    linarith
  refine ⟨B, hB, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hsmall : n < M
    · have h := Finset.single_le_sum
        (fun k (_ : k ∈ Finset.range M) =>
          mul_nonneg (weighted_nonneg t ht.le k) (pow_nonneg hr.le k))
        (Finset.mem_range.mpr hsmall)
      dsimp [B]
      linarith
    · have hn : 2 ≤ n := le_trans (le_max_right N 2) (Nat.le_of_not_gt hsmall)
      have ha :
          (∑ q ∈ (Finset.range n).filter Nat.Prime,
            weightedCount t (n - q) * r ^ n) ≤ B * primeSeries r := by
        calc
          _ ≤ ∑ q ∈ (Finset.range n).filter Nat.Prime, B * r ^ q := by
            apply Finset.sum_le_sum
            intro q hq
            have hqlt := Finset.mem_range.mp (Finset.mem_filter.mp hq).1
            have hqpos := (Finset.mem_filter.mp hq).2.pos
            calc
              weightedCount t (n - q) * r ^ n =
                  (weightedCount t (n - q) * r ^ (n - q)) * r ^ q := by
                    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hqlt.le]
              _ ≤ B * r ^ q := mul_le_mul_of_nonneg_right
                (ih (n - q) (by omega)) (pow_nonneg hr.le q)
          _ = B * (∑ q ∈ (Finset.range n).filter Nat.Prime, r ^ q) :=
            (Finset.mul_sum _ _ _).symm
          _ ≤ B * primeSeries r := by
            apply mul_le_mul_of_nonneg_left _ hB.le
            rw [Finset.sum_filter]
            exact Summable.sum_le_tsum (Finset.range n)
              (fun q _ => by split_ifs <;> positivity) (prime_summable r hr.le hr1)
      have hm : (∑ q ∈ n.primeFactors, weightedCount t (n / q) * r ^ n) ≤
          B * ((n : ℝ) * (Real.sqrt r) ^ n) := by
        have hcard : n.primeFactors.card ≤ n := by
          calc
            n.primeFactors.card ≤ (Finset.Icc 1 n).card := Finset.card_le_card (by
              intro q hq
              exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_primeFactors hq,
                Nat.le_of_mem_primeFactors hq⟩)
            _ = n := by simp
        calc
          _ ≤ ∑ _q ∈ n.primeFactors, B * (Real.sqrt r) ^ n := by
            apply Finset.sum_le_sum
            intro q hq
            have hq2 := (Nat.prime_of_mem_primeFactors hq).two_le
            have hqn : n / q < n := Nat.div_lt_self (by omega) (by omega)
            have hhalf : n / q ≤ n / 2 := Nat.div_le_div_left hq2 (by omega)
            have hexp : n ≤ 2 * (n - n / q) := by omega
            have hp : r ^ (n - n / q) ≤ (Real.sqrt r) ^ n := by
              calc
                _ = (Real.sqrt r) ^ (2 * (n - n / q)) := by
                  rw [pow_mul, Real.sq_sqrt hr.le]
                _ ≤ _ := pow_le_pow_of_le_one hs0 hs1.le hexp
            calc
              weightedCount t (n / q) * r ^ n =
                  (weightedCount t (n / q) * r ^ (n / q)) * r ^ (n - n / q) := by
                    rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hqn.le]
              _ ≤ B * r ^ (n - n / q) := mul_le_mul_of_nonneg_right
                (ih _ hqn) (pow_nonneg hr.le _)
              _ ≤ B * (Real.sqrt r) ^ n := mul_le_mul_of_nonneg_left hp hB.le
          _ = B * ((n.primeFactors.card : ℝ) * (Real.sqrt r) ^ n) := by
            simp only [Finset.sum_const, nsmul_eq_mul]
            ring
          _ ≤ B * ((n : ℝ) * (Real.sqrt r) ^ n) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (pow_nonneg hs0 _)) hB.le
      calc
        weightedCount t n * r ^ n = t *
            ((∑ q ∈ (Finset.range n).filter Nat.Prime,
                weightedCount t (n - q) * r ^ n) +
             (∑ q ∈ n.primeFactors, weightedCount t (n / q) * r ^ n)) := by
              rw [weighted_recurrence t n hn]
              simp only [← Finset.sum_mul]
              ring
        _ ≤ t * (B * primeSeries r + B * ((n : ℝ) * (Real.sqrt r) ^ n)) :=
          mul_le_mul_of_nonneg_left (add_le_add ha hm) ht.le
        _ = B * (t * (primeSeries r + (n : ℝ) * (Real.sqrt r) ^ n)) := by ring
        _ ≤ B * 1 := mul_le_mul_of_nonneg_left
          (hN n (le_trans (le_max_left N 2) (Nat.le_of_not_gt hsmall))).le hB.le
        _ = B := mul_one B

end D5.S3.Factorization.Combinatorics.MixedPrimeHistoryAsymptotics
