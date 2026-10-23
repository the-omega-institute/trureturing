/- GID: D5/S3/Arith/Robin/GA2ForcedPrimeSource
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/GA2ForcedPrimeSource
   mirror-E: none(waiver:qualitative-attainment-and-tail-estimate)
   anchors: []
   utility: none
   digest: An actual GA2 witness yields an attained Robin maximum on every divisible forced base. -/

import D5.S3.Arith.Robin.PaddingRatio
import D5.S3.Arith.GoldenResourceOptimalInteger
import Mathlib.Data.Finset.Max
import Mathlib.Order.Filter.AtTopBot.Ring
import Mathlib.Topology.Algebra.Order.Field

namespace D5.S3.Arith.Robin.GA2ForcedPrimeSource

open Filter
open scoped Topology
open D5.S3.Arith.Robin.PaddingRatio (robinRatio)
open D5.S3.Arith.GoldenResourceOptimalInteger (reciprocal_divisor_sum)

noncomputable section

/-- The literal all-positive-integer-multiplier GA2 condition. The positive
constant `exp gamma` in `robinRatio` cancels from every comparison. -/
def actualGA2 (q : ℕ) : Prop :=
  3 ≤ q ∧ ∀ a : ℕ, 1 ≤ a → robinRatio (a * q) ≤ robinRatio q

private theorem log_domains {n : ℕ} (hn : 3 ≤ n) :
    1 < Real.log (n : ℝ) ∧ 0 < Real.log (Real.log (n : ℝ)) := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 1 < Real.log (n : ℝ) :=
    (Real.lt_log_iff_exp_lt (by linarith)).mpr
      (Real.exp_one_lt_three.trans_le hnR)
  exact ⟨hlog, Real.log_pos hlog⟩

private theorem ratio_eq (n : ℕ) :
    robinRatio n = ((ArithmeticFunction.sigma 1 n : ℝ) / n) /
      (Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ))) := by
  simp only [robinRatio, div_eq_mul_inv, mul_inv_rev]
  ring

private theorem ratio_pos {n : ℕ} (hn : 3 ≤ n) : 0 < robinRatio n := by
  have hn0 : n ≠ 0 := by omega
  have hs : 0 < (ArithmeticFunction.sigma 1 n : ℝ) := by
    exact_mod_cast ArithmeticFunction.sigma_pos 1 n hn0
  rw [ratio_eq]
  exact div_pos (div_pos hs (by exact_mod_cast (show 0 < n by omega)))
    (mul_pos (Real.exp_pos _) (log_domains hn).2)

private theorem abundancy_mono {n L : ℕ} (hn : 1 ≤ n) (hL : 1 ≤ L)
    (hd : n ∣ L) :
    (ArithmeticFunction.sigma 1 n : ℝ) / n ≤
      (ArithmeticFunction.sigma 1 L : ℝ) / L := by
  rw [← reciprocal_divisor_sum hn, ← reciprocal_divisor_sum hL]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Nat.divisors_subset_of_dvd (by omega) hd)
    (fun d _ _ => inv_nonneg.mpr (Nat.cast_nonneg d))

/-- A GA2 integer controls the actual Robin objective at every `n >= 3`,
including integers not divisible by it, via the literal lcm. -/
theorem robinRatio_le_ga2_tail_envelope {q n : ℕ}
    (hga : actualGA2 q) (hn : 3 ≤ n) :
    robinRatio n ≤ robinRatio q *
      (1 + Real.log (q : ℝ) /
        (Real.log (n : ℝ) * Real.log (Real.log (n : ℝ)))) := by
  have hq : 3 ≤ q := hga.1
  let L := Nat.lcm q n
  have hq0 : q ≠ 0 := by omega
  have hn0 : n ≠ 0 := by omega
  have hL0 : L ≠ 0 := Nat.lcm_ne_zero hq0 hn0
  have hnL : n ∣ L := Nat.dvd_lcm_right q n
  have hqL : q ∣ L := Nat.dvd_lcm_left q n
  have hL : 3 ≤ L := hn.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hL0) hnL)
  have hLle : L ≤ q * n := Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega))
    (Nat.lcm_dvd_mul q n)
  have hLga : robinRatio L ≤ robinRatio q := by
    obtain ⟨a, ha⟩ := hqL
    have ha1 : 1 ≤ a := by
      by_contra h
      have : a = 0 := by omega
      simp only [this, Nat.mul_zero] at ha
      exact hL0 ha
    simpa only [ha, Nat.mul_comm q a] using hga.2 a ha1
  have hLn := (log_domains hn).2
  have hLL := (log_domains hL).2
  have hlogn : 0 < Real.log (n : ℝ) := by linarith [(log_domains hn).1]
  have hlogq : 0 < Real.log (q : ℝ) := by linarith [(log_domains hq).1]
  have hgamma := Real.exp_pos Real.eulerMascheroniConstant
  have hfirst : robinRatio n ≤ robinRatio q *
      (Real.log (Real.log (L : ℝ)) / Real.log (Real.log (n : ℝ))) := by
    rw [ratio_eq n]
    apply (div_le_iff₀ (mul_pos hgamma hLn)).mpr
    calc
      _ ≤ (ArithmeticFunction.sigma 1 L : ℝ) / L :=
        abundancy_mono (by omega) (by omega) hnL
      _ = robinRatio L *
          (Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (L : ℝ))) := by
        rw [ratio_eq L]
        exact (div_mul_cancel₀ _ (mul_pos hgamma hLL).ne').symm
      _ ≤ robinRatio q *
          (Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (L : ℝ))) :=
        mul_le_mul_of_nonneg_right hLga (mul_pos hgamma hLL).le
      _ = _ := by field_simp [hLn.ne']
  have hlogprod : 0 < Real.log ((q : ℝ) * n) := by
    rw [Real.log_mul (by positivity) (by positivity)]
    positivity
  have hlogs : Real.log (Real.log (L : ℝ)) ≤
      Real.log (Real.log ((q : ℝ) * n)) :=
    Real.log_le_log (by linarith [(log_domains hL).1])
      (Real.log_le_log (by exact_mod_cast (Nat.pos_of_ne_zero hL0))
        (by exact_mod_cast hLle))
  have hdiff : Real.log (Real.log ((q : ℝ) * n)) -
      Real.log (Real.log (n : ℝ)) =
      Real.log (1 + Real.log (q : ℝ) / Real.log (n : ℝ)) := by
    rw [← Real.log_div hlogprod.ne' hlogn.ne',
      Real.log_mul (by positivity) (by positivity)]
    congr 1
    field_simp [hlogn.ne']
    ring
  have hinc : Real.log (Real.log ((q : ℝ) * n)) ≤
      Real.log (Real.log (n : ℝ)) + Real.log (q : ℝ) / Real.log (n : ℝ) := by
    have := Real.log_le_sub_one_of_pos
      (show 0 < 1 + Real.log (q : ℝ) / Real.log (n : ℝ) by positivity)
    rw [← hdiff] at this
    linarith
  have hdist : Real.log (Real.log (L : ℝ)) / Real.log (Real.log (n : ℝ)) ≤
      1 + Real.log (q : ℝ) /
        (Real.log (n : ℝ) * Real.log (Real.log (n : ℝ))) := by
    apply (div_le_iff₀ hLn).mpr
    calc
      _ ≤ Real.log (Real.log (n : ℝ)) + Real.log (q : ℝ) / Real.log (n : ℝ) :=
        hlogs.trans hinc
      _ = _ := by field_simp [hLn.ne']
  exact hfirst.trans (mul_le_mul_of_nonneg_left hdist (ratio_pos hq).le)

/-- A divisible actual GA2 witness gives an attained maximum of the actual
Robin objective over all positive multiples of the forced base. The selected
integer is itself GA2. No bounded-search or fixed-price maximum is assumed. -/
theorem exists_robin_maximizer_multiple_of_ga2 {m q : ℕ} (hm : 3 ≤ m)
    (hmq : m ∣ q) (hga : actualGA2 q) :
    ∃ N : ℕ, m ≤ N ∧ m ∣ N ∧ robinRatio q ≤ robinRatio N ∧ actualGA2 N ∧
      ∀ n : ℕ, 1 ≤ n → m ∣ n → robinRatio n ≤ robinRatio N := by
  classical
  have hq : 1 ≤ q := by have := hga.1; omega
  by_cases hbest : ∀ n : ℕ, 1 ≤ n → m ∣ n → robinRatio n ≤ robinRatio q
  · exact ⟨q, Nat.le_of_dvd (by omega) hmq, hmq, le_rfl, hga, hbest⟩
  push Not at hbest
  obtain ⟨n₀, hn₀, hmn₀, hbetter⟩ := hbest
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hprod := hlog.atTop_mul_atTop₀ (Real.tendsto_log_atTop.comp hlog)
  have hcorrection := tendsto_const_nhds.div_atTop hprod (a := Real.log (q : ℝ))
  have hlimit : Tendsto (fun n : ℕ => robinRatio q *
      (1 + Real.log (q : ℝ) /
        (Real.log (n : ℝ) * Real.log (Real.log (n : ℝ)))))
      atTop (𝓝 (robinRatio q)) := by
    simpa only [Function.comp_def, add_zero, mul_one] using
      (hcorrection.const_add 1).const_mul (robinRatio q)
  obtain ⟨K, hK⟩ := eventually_atTop.mp ((tendsto_order.mp hlimit).2 _ hbetter)
  let T := max K (n₀ + 1)
  let s := (Finset.range T).filter fun n => 1 ≤ n ∧ m ∣ n
  have hn₀s : n₀ ∈ s := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      ((Nat.lt_succ_self n₀).trans_le (le_max_right _ _)), hn₀, hmn₀⟩
  obtain ⟨N, hNs, hNmax⟩ := s.exists_max_image robinRatio ⟨n₀, hn₀s⟩
  have hNpos : 1 ≤ N := (Finset.mem_filter.mp hNs).2.1
  have hmN : m ∣ N := (Finset.mem_filter.mp hNs).2.2
  have hmax : ∀ n : ℕ, 1 ≤ n → m ∣ n → robinRatio n ≤ robinRatio N := by
    intro n hn hmn
    by_cases hnT : n < T
    · exact hNmax n (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hnT, hn, hmn⟩)
    · have hn3 : 3 ≤ n := hm.trans (Nat.le_of_dvd (by omega) hmn)
      have hKn : K ≤ n := (le_max_left _ _).trans (Nat.le_of_not_gt hnT)
      exact (robinRatio_le_ga2_tail_envelope hga hn3).trans
        ((hK n hKn).le.trans (hNmax n₀ hn₀s))
  refine ⟨N, Nat.le_of_dvd (by omega) hmN, hmN, hmax q hq hmq, ?_, hmax⟩
  refine ⟨hm.trans (Nat.le_of_dvd (by omega) hmN), ?_⟩
  intro a ha
  exact hmax (a * N) (Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by omega) (by omega))) (hmN.trans (dvd_mul_left N a))

#print axioms actualGA2
#print axioms log_domains
#print axioms ratio_eq
#print axioms ratio_pos
#print axioms abundancy_mono
#print axioms robinRatio_le_ga2_tail_envelope
#print axioms exists_robin_maximizer_multiple_of_ga2

end
end D5.S3.Arith.Robin.GA2ForcedPrimeSource
