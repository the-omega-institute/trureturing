/- GID: D5/S3/Factorization/JordanCototientRecordLimitInfinity
   generality: G
   mirror-B: D5/B/S3/Factorization/JordanCototientRecordLimitInfinity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Eventual strict Jordan-cototient records are exactly one and the even naturals. -/

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

/- The OEIS A004277 comment of Hal M. Switkay (2025-11-30) supplies the
   definitions and conjectures the eventual record set. The per-input theorem,
   including its quantitative min-prime-factor bounds, is derived here. -/

open Finset Filter Set

namespace D5.S3.Factorization.JordanCototientRecordLimitInfinity

/-- The real-parameter Jordan totient from the source comment. -/
noncomputable def J (k : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ k * ∏ p ∈ n.primeFactors, (1 - (p : ℝ) ^ (-k))

/-- The Jordan cototient is the difference between the ambient power and `J`. -/
noncomputable def CoJ (k : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ k - J k n

/-- `n` is a strict Jordan-cototient record at parameter `k`. -/
def StrictRecord (k : ℝ) (n : ℕ) : Prop :=
  ∀ m, 1 ≤ m → m < n → CoJ k m < CoJ k n

private lemma rpow_inv_factor_nonneg (k : ℝ) (p : ℕ) :
    0 ≤ (p : ℝ) ^ (-k) :=
  Real.rpow_nonneg (Nat.cast_nonneg p) _

private lemma rpow_inv_factor_le_one {k : ℝ} (hk : 0 ≤ k) {p : ℕ} (hp : 2 ≤ p) :
    (p : ℝ) ^ (-k) ≤ 1 := by
  exact Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast (show 1 ≤ p by omega)) (neg_nonpos.mpr hk)

private lemma one_sub_prod_le_sum {ι : Type*} [LinearOrder ι]
    (s : Finset ι) (x : ι → ℝ)
    (hx0 : ∀ i ∈ s, 0 ≤ x i) (hx1 : ∀ i ∈ s, x i ≤ 1) :
    1 - ∏ i ∈ s, (1 - x i) ≤ ∑ i ∈ s, x i := by
  rw [Finset.prod_one_sub_ordered]
  simp only [sub_sub_cancel]
  apply Finset.sum_le_sum
  intro i hi
  have hprod0 : 0 ≤ ∏ j ∈ s with j < i, (1 - x j) := by
    apply Finset.prod_nonneg
    intro j hj
    exact sub_nonneg.mpr (hx1 j (Finset.mem_filter.mp hj).1)
  have hprod1 : ∏ j ∈ s with j < i, (1 - x j) ≤ 1 := by
    apply Finset.prod_le_one₀
    · intro j hj
      exact sub_nonneg.mpr (hx1 j (Finset.mem_filter.mp hj).1)
    · intro j hj
      linarith [hx0 j (Finset.mem_filter.mp hj).1]
  exact mul_le_of_le_one_right (hx0 i hi) hprod1

private lemma le_one_sub_prod {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) {i : ι} (hi : i ∈ s)
    (hx0 : ∀ j ∈ s, 0 ≤ x j) (hx1 : ∀ j ∈ s, x j ≤ 1) :
    x i ≤ 1 - ∏ j ∈ s, (1 - x j) := by
  classical
  have hprod : ∏ j ∈ s, (1 - x j) ≤ ∏ j ∈ ({i} : Finset ι), (1 - x j) := by
    apply Finset.prod_le_prod_of_subset_of_le_one₀
    · simpa using hi
    · intro j hj
      exact sub_nonneg.mpr (hx1 j hj)
    · intro j hj _
      linarith [hx0 j hj]
  have := sub_le_sub_left hprod 1
  simpa using this

private lemma coJ_factor (k : ℝ) (n : ℕ) :
    CoJ k n = (n : ℝ) ^ k * (1 - ∏ p ∈ n.primeFactors, (1 - (p : ℝ) ^ (-k))) := by
  simp only [CoJ, J]
  ring

private lemma minFac_mem_primeFactors {n : ℕ} (hn : 1 < n) :
    n.minFac ∈ n.primeFactors := by
  exact (Nat.mem_primeFactors_of_ne_zero (by omega)).mpr
    ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd n⟩

private lemma rpow_quotient_identity {n : ℕ} (hn : 1 < n) (k : ℝ) :
    (n : ℝ) ^ k * (n.minFac : ℝ) ^ (-k) = ((n / n.minFac : ℕ) : ℝ) ^ k := by
  rw [Real.rpow_neg (by positivity)]
  rw [← div_eq_mul_inv, ← Real.div_rpow (by positivity) (by positivity)]
  rw [Nat.cast_div_charZero (Nat.minFac_dvd n)]

/-- The smallest-prime-factor term gives a lower bound for the cototient. -/
theorem coJ_lower_bound {k : ℝ} (hk : 0 < k) {n : ℕ} (hn : 1 < n) :
    ((n / n.minFac : ℕ) : ℝ) ^ k ≤ CoJ k n := by
  rw [coJ_factor, ← rpow_quotient_identity hn k]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Nat.cast_nonneg n) k)
  apply le_one_sub_prod n.primeFactors (fun p => (p : ℝ) ^ (-k)) (minFac_mem_primeFactors hn)
  · intro p hp
    exact rpow_inv_factor_nonneg k p
  · intro p hp
    exact rpow_inv_factor_le_one hk.le (Nat.prime_of_mem_primeFactors hp).two_le

/-- The number of distinct prime factors times the min-factor scale bounds the cototient above. -/
theorem coJ_upper_bound {k : ℝ} (hk : 0 < k) {n : ℕ} (hn : 1 < n) :
    CoJ k n ≤ n.primeFactors.card * ((n / n.minFac : ℕ) : ℝ) ^ k := by
  rw [coJ_factor]
  calc
    (n : ℝ) ^ k * (1 - ∏ p ∈ n.primeFactors, (1 - (p : ℝ) ^ (-k)))
        ≤ (n : ℝ) ^ k * (n.primeFactors.card * (n.minFac : ℝ) ^ (-k)) := by
          apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Nat.cast_nonneg n) k)
          calc
            1 - ∏ p ∈ n.primeFactors, (1 - (p : ℝ) ^ (-k))
                ≤ ∑ p ∈ n.primeFactors, (p : ℝ) ^ (-k) := by
                  apply one_sub_prod_le_sum
                  · intro p hp
                    exact rpow_inv_factor_nonneg k p
                  · intro p hp
                    exact rpow_inv_factor_le_one hk.le
                      (Nat.prime_of_mem_primeFactors hp).two_le
            _ ≤ ∑ _p ∈ n.primeFactors, (n.minFac : ℝ) ^ (-k) := by
                  apply Finset.sum_le_sum
                  intro p hp
                  apply Real.rpow_le_rpow_of_nonpos
                    (by exact_mod_cast Nat.minFac_pos n)
                  · exact_mod_cast Nat.minFac_le_of_dvd
                      (Nat.prime_of_mem_primeFactors hp).two_le
                      (Nat.dvd_of_mem_primeFactors hp)
                  · exact neg_nonpos.mpr hk.le
            _ = n.primeFactors.card * (n.minFac : ℝ) ^ (-k) := by simp
    _ = n.primeFactors.card * ((n / n.minFac : ℕ) : ℝ) ^ k := by
          rw [← rpow_quotient_identity hn k]
          ring

/-- Every prime has Jordan cototient one for every real parameter. -/
theorem coJ_prime {p : ℕ} (hp : p.Prime) (k : ℝ) : CoJ k p = 1 := by
  rw [coJ_factor, hp.primeFactors]
  simp only [Finset.prod_singleton]
  have hpow : (p : ℝ) ^ k * (p : ℝ) ^ (-k) = 1 := by
    rw [← Real.rpow_add (by exact_mod_cast hp.pos)]
    simp
  nlinarith

private lemma eventually_const_mul_rpow_lt_rpow {C a b : ℝ}
    (ha : 0 < a) (hab : a < b) :
    ∃ K : ℝ, ∀ k > K, C * a ^ k < b ^ k := by
  have hb : 0 < b := ha.trans hab
  have hq0 : 0 < a / b := div_pos ha hb
  have hq1 : a / b < 1 := (div_lt_one hb).mpr hab
  have ht : Tendsto (fun k : ℝ => C * (a / b) ^ k) atTop (nhds 0) := by
    simpa using (tendsto_rpow_atTop_of_base_lt_one (a / b) (by linarith) hq1).const_mul C
  have hev : ∀ᶠ k : ℝ in atTop, C * (a / b) ^ k < 1 :=
    (tendsto_order.mp ht).2 1 zero_lt_one
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp hev
  refine ⟨K, fun k hk => ?_⟩
  have h := hK k hk.le
  have hbk : 0 < b ^ k := Real.rpow_pos_of_pos hb k
  rw [Real.div_rpow ha.le hb.le] at h
  rw [← (div_lt_one hbk)]
  simpa [mul_div_assoc] using h

/-- The Jordan cototient of one is zero. -/
@[simp] theorem coJ_one (k : ℝ) : CoJ k 1 = 0 := by
  simp [CoJ, J]

private lemma quotient_le_half {m : ℕ} (hm : 1 < m) :
    ((m / m.minFac : ℕ) : ℝ) ≤ (m : ℝ) / 2 := by
  rw [Nat.cast_div_charZero (Nat.minFac_dvd m)]
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg m) (by norm_num)
    (by exact_mod_cast (Nat.minFac_prime (by omega)).two_le)

private lemma card_primeFactors_le_of_lt {m n : ℕ} (hmn : m < n) :
    m.primeFactors.card ≤ n := by
  calc
    m.primeFactors.card ≤ (Finset.range n).card := by
      apply Finset.card_le_card
      rw [Finset.subset_range]
      intro p hp
      exact (Nat.le_of_mem_primeFactors hp).trans_lt hmn
    _ = n := Finset.card_range n

private lemma even_quotient_eq_half {n : ℕ} (hn : Even n) :
    ((n / n.minFac : ℕ) : ℝ) = (n : ℝ) / 2 := by
  have hdvd : 2 ∣ n := even_iff_two_dvd.mp hn
  rw [(Nat.minFac_eq_two_iff n).mpr hdvd]
  exact Nat.cast_div_charZero hdvd

/-- Each positive even integer is eventually a strict Jordan-cototient record. -/
theorem eventual_strictRecord_of_even {n : ℕ} (hn1 : 1 ≤ n) (heven : Even n) :
    ∃ K : ℝ, ∀ k > K, StrictRecord k n := by
  have hn2 : 2 ≤ n := by
    have hdvd : 2 ∣ n := even_iff_two_dvd.mp heven
    rcases hdvd with ⟨c, rfl⟩
    cases c with
    | zero => simp at hn1
    | succ c => omega
  have ha : 0 < ((n - 1 : ℕ) : ℝ) / 2 := by
    have : 0 < n - 1 := by omega
    positivity
  have hab : ((n - 1 : ℕ) : ℝ) / 2 < (n : ℝ) / 2 := by
    rw [div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)]
    exact_mod_cast Nat.sub_lt (by omega : 0 < n) (by omega : 0 < (1 : ℕ))
  obtain ⟨K, hK⟩ := eventually_const_mul_rpow_lt_rpow
    (C := (n : ℝ)) ha hab
  refine ⟨max K 0, fun k hk m hm1 hmn => ?_⟩
  have hk0 : 0 < k := lt_of_le_of_lt (le_max_right K 0) hk
  have hlower : ((n : ℝ) / 2) ^ k ≤ CoJ k n := by
    rw [← even_quotient_eq_half heven]
    exact coJ_lower_bound hk0 (lt_of_lt_of_le Nat.one_lt_two hn2)
  by_cases hmone : m = 1
  · subst m
    rw [coJ_one]
    exact (Real.rpow_pos_of_pos (by positivity) k).trans_le hlower
  · have hm2 : 1 < m := by omega
    have hcard : (m.primeFactors.card : ℝ) ≤ n := by
      exact_mod_cast card_primeFactors_le_of_lt hmn
    have hquot : ((m / m.minFac : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) / 2 := by
      calc
        ((m / m.minFac : ℕ) : ℝ) ≤ (m : ℝ) / 2 := quotient_le_half hm2
        _ ≤ ((n - 1 : ℕ) : ℝ) / 2 := by
          gcongr
          exact_mod_cast (show m ≤ n - 1 by omega)
    calc
      CoJ k m ≤ m.primeFactors.card * ((m / m.minFac : ℕ) : ℝ) ^ k :=
        coJ_upper_bound hk0 hm2
      _ ≤ (n : ℝ) * (((n - 1 : ℕ) : ℝ) / 2) ^ k := by
        apply mul_le_mul hcard
        · exact Real.rpow_le_rpow (by positivity) hquot hk0.le
        · exact Real.rpow_nonneg (by positivity) k
        · positivity
      _ < ((n : ℝ) / 2) ^ k := hK k (lt_of_le_of_lt (le_max_left K 0) hk)
      _ ≤ CoJ k n := hlower

private lemma quotient_le_third_of_not_even {n : ℕ} (hn : 1 < n) (hodd : ¬ Even n) :
    ((n / n.minFac : ℕ) : ℝ) ≤ (n : ℝ) / 3 := by
  have hmf_ne : n.minFac ≠ 2 := by
    intro h
    apply hodd
    exact even_iff_two_dvd.mpr ((Nat.minFac_eq_two_iff n).mp h)
  have hmf3 : 3 ≤ n.minFac := by
    have hmf2 : 2 ≤ n.minFac := (Nat.minFac_prime (by omega : n ≠ 1)).two_le
    omega
  rw [Nat.cast_div_charZero (Nat.minFac_dvd n)]
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg n) (by norm_num)
    (by exact_mod_cast hmf3)

private lemma card_primeFactors_le_succ (n : ℕ) : n.primeFactors.card ≤ n + 1 := by
  calc
    n.primeFactors.card ≤ (Finset.range (n + 1)).card := by
      apply Finset.card_le_card
      rw [Finset.subset_range]
      intro p hp
      exact (Nat.le_of_mem_primeFactors hp).trans_lt (Nat.lt_succ_self n)
    _ = n + 1 := Finset.card_range (n + 1)

/-- Each odd integer at least five eventually loses to its even predecessor. -/
theorem eventual_loses_to_predecessor_of_odd {n : ℕ} (hn5 : 5 ≤ n) (hodd : ¬ Even n) :
    ∃ K : ℝ, ∀ k > K, CoJ k n < CoJ k (n - 1) := by
  have hn1 : 1 < n := by omega
  have hpred1 : 1 < n - 1 := by omega
  have hpred_even : Even (n - 1) := by
    obtain ⟨c, hc⟩ := Nat.not_even_iff_odd.mp hodd
    rw [even_iff_two_dvd]
    use c
    omega
  have ha : 0 < (n : ℝ) / 3 := by positivity
  have hab : (n : ℝ) / 3 < ((n - 1 : ℕ) : ℝ) / 2 := by
    have hn3 : (3 : ℝ) < n := by exact_mod_cast (show 3 < n by omega)
    have hsub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      exact_mod_cast (Nat.cast_sub (by omega : 1 ≤ n) : ((n - 1 : ℕ) : ℝ) = _)
    rw [hsub]
    linarith
  obtain ⟨K, hK⟩ := eventually_const_mul_rpow_lt_rpow
    (C := ((n + 1 : ℕ) : ℝ)) ha hab
  refine ⟨max K 0, fun k hk => ?_⟩
  have hk0 : 0 < k := lt_of_le_of_lt (le_max_right K 0) hk
  have hlower : (((n - 1 : ℕ) : ℝ) / 2) ^ k ≤ CoJ k (n - 1) := by
    rw [← even_quotient_eq_half hpred_even]
    exact coJ_lower_bound hk0 hpred1
  have hcard : (n.primeFactors.card : ℝ) ≤ (n + 1 : ℕ) := by
    exact_mod_cast card_primeFactors_le_succ n
  have hquot : ((n / n.minFac : ℕ) : ℝ) ≤ (n : ℝ) / 3 :=
    quotient_le_third_of_not_even hn1 hodd
  calc
    CoJ k n ≤ n.primeFactors.card * ((n / n.minFac : ℕ) : ℝ) ^ k :=
      coJ_upper_bound hk0 hn1
    _ ≤ ((n + 1 : ℕ) : ℝ) * ((n : ℝ) / 3) ^ k := by
      apply mul_le_mul hcard
      · exact Real.rpow_le_rpow (by positivity) hquot hk0.le
      · exact Real.rpow_nonneg (by positivity) k
      · positivity
    _ < (((n - 1 : ℕ) : ℝ) / 2) ^ k :=
      hK k (lt_of_le_of_lt (le_max_left K 0) hk)
    _ ≤ CoJ k (n - 1) := hlower

/-- Three is never a strict record because its cototient ties that of two. -/
theorem not_strictRecord_three (k : ℝ) : ¬ StrictRecord k 3 := by
  intro h
  have h23 := h 2 (by omega) (by omega)
  rw [coJ_prime (by norm_num : Nat.Prime 2), coJ_prime (by norm_num : Nat.Prime 3)] at h23
  exact (lt_irrefl 1 h23)

private theorem not_eventual_strictRecord_of_not_even {n : ℕ} (hn : 1 < n)
    (hodd : ¬ Even n) :
    ¬ ∃ K : ℝ, ∀ k > K, StrictRecord k n := by
  rintro ⟨K, hK⟩
  by_cases hn3 : n = 3
  · subst n
    exact not_strictRecord_three (K + 1) (hK (K + 1) (by linarith))
  · have hn2 : n ≠ 2 := by
      intro h
      subst n
      exact hodd (by norm_num)
    have hn4 : n ≠ 4 := by
      intro h
      subst n
      exact hodd (by norm_num)
    have hn5 : 5 ≤ n := by omega
    obtain ⟨L, hL⟩ := eventual_loses_to_predecessor_of_odd hn5 hodd
    let k := max K L + 1
    have hkK : K < k := by
      dsimp [k]
      linarith [le_max_left K L]
    have hkL : L < k := by
      dsimp [k]
      linarith [le_max_right K L]
    have hrecord := hK k hkK
    have hlose := hL k hkL
    have hreverse : CoJ k (n - 1) < CoJ k n :=
      hrecord (n - 1) (by omega) (by omega)
    exact (lt_asymm hlose hreverse)

/-- Per input, eventual strict Jordan-cototient records are exactly one and the even naturals. -/
theorem a004277_eventual_record_iff :
    ∀ n ≥ 1, (∃ K : ℝ, ∀ k > K, StrictRecord k n) ↔ (n = 1 ∨ Even n) := by
  intro n hn
  constructor
  · intro heventual
    by_cases hn1 : n = 1
    · exact Or.inl hn1
    · right
      by_contra hodd
      exact not_eventual_strictRecord_of_not_even (by omega) hodd heventual
  · rintro (rfl | heven)
    · refine ⟨0, fun k hk m hm hmlt => ?_⟩
      omega
    · exact eventual_strictRecord_of_even hn heven

example (k : ℝ) : CoJ k 2 = 1 := coJ_prime (by norm_num) k
example (k : ℝ) : CoJ k 3 = 1 := coJ_prime (by norm_num) k
example : 1 ≤ 4 ∧ Even 4 := by norm_num
example : 5 ≤ 5 ∧ ¬ Even 5 := by norm_num
example : ∃ K : ℝ, ∀ k > K, StrictRecord k 4 :=
  eventual_strictRecord_of_even (by norm_num) (by norm_num)
example : ∃ K : ℝ, ∀ k > K, CoJ k 5 < CoJ k (5 - 1) :=
  eventual_loses_to_predecessor_of_odd (by norm_num) (by norm_num)
example : CoJ 2 4 = 4 := by
  have hpf : Nat.primeFactors 4 = {2} := by
    calc
      Nat.primeFactors 4 = Nat.primeFactors (2 ^ 2) := by norm_num
      _ = Nat.primeFactors 2 := Nat.primeFactors_pow 2 (by norm_num)
      _ = {2} := Nat.Prime.primeFactors (by norm_num)
  norm_num [CoJ, J, hpf]

end D5.S3.Factorization.JordanCototientRecordLimitInfinity
