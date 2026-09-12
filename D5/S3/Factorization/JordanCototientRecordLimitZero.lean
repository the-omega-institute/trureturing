/- GID: D5/S3/Factorization/JordanCototientRecordLimitZero
   generality: G
   mirror-B: D5/B/S3/Factorization/JordanCototientRecordLimitZero
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Eventual small-parameter records are one, two, four, and the non-prime-powers. -/

import D5.S3.Factorization.JordanCototientRecordLimitInfinity
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Tactic.IntervalCases

/- The OEIS A387335 comment of Hal M. Switkay (2025-11-30) conjectures
   this pointwise eventual record set. The proof compares the right-hand
   first-order terms at zero and takes a finite intersection for each input. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset Filter Set SignType
open scoped BigOperators

noncomputable section

namespace D5.S3.Factorization.JordanCototientRecordLimitZero

open D5.S3.Factorization.JordanCototientRecordLimitInfinity

private lemma coJ_factor (k : ℝ) (n : ℕ) :
    CoJ k n = (n : ℝ) ^ k *
      (1 - ∏ p ∈ n.primeFactors, (1 - (p : ℝ) ^ (-k))) := by
  simp only [CoJ, J]
  ring

private lemma hasDerivAt_euler_factor (p : ℕ) (hp : p.Prime) :
    HasDerivAt (fun k : ℝ => 1 - (p : ℝ) ^ (-k)) (Real.log p) 0 := by
  have hneg : HasDerivAt (fun k : ℝ => -k) (-1) 0 := (hasDerivAt_id 0).neg
  have hrpow := HasDerivAt.const_rpow (a := (p : ℝ)) (by exact_mod_cast hp.pos) hneg
  have hraw := (hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).sub hrpow
  have hderiv : (0 : ℝ) - Real.log p * (-1) * (p : ℝ) ^ (-(0 : ℝ)) = Real.log p := by
    norm_num
  rw [hderiv] at hraw
  have hexplicit : HasDerivAt (fun k : ℝ => 1 - (p : ℝ) ^ (-k)) (Real.log p) 0 :=
    hraw.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun _ => rfl))
  exact hexplicit

private lemma prod_euler_factor_zero_of_two_le_card {n : ℕ}
    (hn : 2 ≤ n.primeFactors.card) :
    ∏ p ∈ n.primeFactors, (1 - (p : ℝ) ^ (-(0 : ℝ))) = 0 := by
  have hnonempty : n.primeFactors.Nonempty := Finset.card_pos.mp (by omega)
  apply Finset.prod_eq_zero hnonempty.choose_spec
  simp

private lemma prod_erase_euler_factor_zero {n p : ℕ}
    (hn : 2 ≤ n.primeFactors.card) :
    ∏ q ∈ n.primeFactors.erase p, (1 - (q : ℝ) ^ (-(0 : ℝ))) = 0 := by
  obtain ⟨q, hq, hqp⟩ := Finset.exists_mem_ne (show 1 < n.primeFactors.card by omega) p
  apply Finset.prod_eq_zero (i := q) (Finset.mem_erase.mpr ⟨hqp, hq⟩)
  simp

private lemma hasDerivAt_euler_product_of_two_le_card {n : ℕ}
    (hn : 2 ≤ n.primeFactors.card) :
    HasDerivAt
      (fun k : ℝ => ∏ p ∈ n.primeFactors, (1 - (p : ℝ) ^ (-k))) 0 0 := by
  have hprod := HasDerivAt.fun_finsetProd
    (u := n.primeFactors)
    (f := fun (p : ℕ) (k : ℝ) => 1 - (p : ℝ) ^ (-k))
    (f' := fun p => Real.log p)
    (x := (0 : ℝ))
    (fun p hp => hasDerivAt_euler_factor p (Nat.prime_of_mem_primeFactors hp))
  have hsum :
      (∑ i ∈ n.primeFactors,
        (∏ j ∈ n.primeFactors.erase i, (1 - (j : ℝ) ^ (-(0 : ℝ)))) • Real.log i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [prod_erase_euler_factor_zero hn]
    simp
  rw [hsum] at hprod
  exact hprod

private lemma hasDerivAt_coJ_of_two_le_card {n : ℕ}
    (hn : 2 ≤ n.primeFactors.card) :
    HasDerivAt (fun k : ℝ => CoJ k n) (Real.log n) 0 := by
  have hn1 : 1 < n := Nat.nonempty_primeFactors.mp (Finset.card_pos.mp (by omega))
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnPower : HasDerivAt (fun k : ℝ => (n : ℝ) ^ k) (Real.log n) 0 := by
    simpa using (Real.hasStrictDerivAt_const_rpow hnpos 0).hasDerivAt
  have hprod := hasDerivAt_euler_product_of_two_le_card hn
  have hcomplement := (hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).sub hprod
  have hprodZero := prod_euler_factor_zero_of_two_le_card hn
  have hraw := hnPower.mul hcomplement
  have hexplicit : HasDerivAt
      (fun k : ℝ => (n : ℝ) ^ k *
        (1 - ∏ p ∈ n.primeFactors, (1 - (p : ℝ) ^ (-k))))
      (Real.log n *
        (1 - ∏ p ∈ n.primeFactors, (1 - (p : ℝ) ^ (-(0 : ℝ)))) +
          (n : ℝ) ^ (0 : ℝ) * (0 - 0)) 0 :=
    hraw.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun _ => rfl))
  rw [hprodZero] at hexplicit
  norm_num at hexplicit
  exact hexplicit.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun k => coJ_factor k n))

private lemma coJ_prime_pow (p a : ℕ) (hp : p.Prime) (ha : 0 < a) (k : ℝ) :
    CoJ k (p ^ a) = ((p ^ (a - 1) : ℕ) : ℝ) ^ k := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
  rw [coJ_factor, Nat.primeFactors_prime_pow (by omega) hp]
  simp only [Finset.prod_singleton, sub_sub_cancel]
  rw [Real.rpow_neg (by exact_mod_cast hp.pos.le)]
  rw [← div_eq_mul_inv, ← Real.div_rpow (by positivity) (by exact_mod_cast hp.pos.le)]
  congr 1
  push_cast
  rw [pow_succ]
  rw [mul_div_cancel_right₀ _ (by exact_mod_cast hp.ne_zero)]

private lemma hasDerivAt_coJ_prime_pow (p a : ℕ) (hp : p.Prime) (ha : 0 < a) :
    HasDerivAt (fun k : ℝ => CoJ k (p ^ a)) (Real.log (p ^ (a - 1) : ℕ)) 0 := by
  have hbase : (0 : ℝ) < ((p ^ (a - 1) : ℕ) : ℝ) := by
    exact_mod_cast pow_pos hp.pos (a - 1)
  have h := (Real.hasStrictDerivAt_const_rpow hbase 0).hasDerivAt
  simpa using h.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun k => coJ_prime_pow p a hp ha k))

private lemma eventually_lt_of_hasDerivAt {f g : ℝ → ℝ} {f' g' : ℝ}
    (hf : HasDerivAt f f' 0) (hg : HasDerivAt g g' 0)
    (hzero : f 0 = g 0) (hderiv : f' < g') :
    ∀ᶠ k : ℝ in nhdsWithin 0 (Ioi 0), f k < g k := by
  let h : ℝ → ℝ := fun k => g k - f k
  have hh : HasDerivAt h (g' - f') 0 := hg.sub hf
  have hsign : ∀ᶠ k : ℝ in nhds 0, sign (h k) = sign (k - 0) := by
    apply eventually_nhdsWithin_sign_eq_of_deriv_pos
    · rw [hh.deriv]
      linarith
    · simp [h, hzero]
  filter_upwards [hsign.filter_mono inf_le_left, self_mem_nhdsWithin] with k hk hpos
  have hkpos : 0 < k := by simpa only [Set.mem_Ioi] using hpos
  have hs : sign (h k) = 1 := by
    exact hk.trans (sign_pos (sub_pos.mpr hkpos))
  exact sub_pos.mp ((sign_eq_one_iff.mp hs) : 0 < g k - f k)

private lemma coJ_zero_of_one_lt {n : ℕ} (hn : 1 < n) : CoJ 0 n = 1 := by
  rw [coJ_factor]
  have hnonempty : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr hn
  have hprod : ∏ p ∈ n.primeFactors, (1 - (p : ℝ) ^ (-(0 : ℝ))) = 0 := by
    apply Finset.prod_eq_zero hnonempty.choose_spec
    simp
  rw [hprod]
  norm_num

private lemma log_nat_lt_log_nat {a b : ℕ} (ha : 0 < a) (hab : a < b) :
    Real.log a < Real.log b := by
  apply Real.strictMonoOn_log
  · simpa only [Set.mem_Ioi] using (show (0 : ℝ) < a by exact_mod_cast ha)
  · simpa only [Set.mem_Ioi] using (show (0 : ℝ) < b by exact_mod_cast ha.trans hab)
  · exact_mod_cast hab

private lemma hasDerivAt_coJ_of_one_lt {n : ℕ} (hn : 1 < n) :
    ∃ d : ℝ, HasDerivAt (fun k : ℝ => CoJ k n) d 0 ∧ d ≤ Real.log n := by
  by_cases hcard : 2 ≤ n.primeFactors.card
  · exact ⟨Real.log n, hasDerivAt_coJ_of_two_le_card hcard, le_rfl⟩
  · have hcardPos : 0 < n.primeFactors.card :=
      Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr hn)
    have hcardOne : n.primeFactors.card = 1 := by omega
    have hpp : IsPrimePow n := isPrimePow_iff_card_primeFactors_eq_one.mpr hcardOne
    obtain ⟨p, a, hp, ha, rfl⟩ := (isPrimePow_nat_iff _).mp hpp
    refine ⟨Real.log (p ^ (a - 1) : ℕ), hasDerivAt_coJ_prime_pow p a hp ha, ?_⟩
    exact (log_nat_lt_log_nat (pow_pos hp.pos _)
      ((Nat.pow_lt_pow_iff_right hp.one_lt).mpr (Nat.sub_lt ha zero_lt_one))).le

private lemma card_primeFactors_mul_prime_pow_ge_two (q p a : ℕ)
    (hq : q.Prime) (hp : p.Prime) (hqp : q ≠ p) (ha : 0 < a) :
    2 ≤ (q * p ^ a).primeFactors.card := by
  have hqmem : q ∈ (q * p ^ a).primeFactors := by
    apply (Nat.mem_primeFactors_of_ne_zero (mul_ne_zero hq.ne_zero (pow_ne_zero _ hp.ne_zero))).mpr
    exact ⟨hq, dvd_mul_right q (p ^ a)⟩
  have hpmem : p ∈ (q * p ^ a).primeFactors := by
    apply (Nat.mem_primeFactors_of_ne_zero (mul_ne_zero hq.ne_zero (pow_ne_zero _ hp.ne_zero))).mpr
    exact ⟨hp, dvd_mul_of_dvd_right (dvd_pow_self p ha.ne') q⟩
  exact Finset.one_lt_card_iff_nontrivial.mpr ⟨q, hqmem, p, hpmem, hqp⟩

private lemma eventually_loses_odd_prime_pow {p a : ℕ}
    (hp : p.Prime) (hpodd : p ≠ 2) (ha : 2 ≤ a) :
    ∀ᶠ k : ℝ in nhdsWithin 0 (Ioi 0), CoJ k (p ^ a) < CoJ k (2 * p ^ (a - 1)) := by
  have hpgt : 2 < p := (hp.two_le.lt_or_eq).resolve_right (Ne.symm hpodd)
  have hcard : 2 ≤ (2 * p ^ (a - 1)).primeFactors.card :=
    card_primeFactors_mul_prime_pow_ge_two 2 p (a - 1) Nat.prime_two hp
      (Ne.symm hpodd) (by omega)
  apply eventually_lt_of_hasDerivAt (hasDerivAt_coJ_prime_pow p a hp (by omega))
    (hasDerivAt_coJ_of_two_le_card hcard)
  · have hleft : 1 < p ^ a := one_lt_pow₀ hp.one_lt (by omega)
    have hright : 1 < 2 * p ^ (a - 1) := by
      exact one_lt_two.trans_le (Nat.le_mul_of_pos_right 2 (pow_pos hp.pos _))
    rw [coJ_zero_of_one_lt hleft, coJ_zero_of_one_lt hright]
  · apply log_nat_lt_log_nat (by positivity)
    exact lt_mul_of_one_lt_left (pow_pos hp.pos _) (by norm_num)

private lemma eventually_loses_two_pow {a : ℕ} (ha : 3 ≤ a) :
    ∀ᶠ k : ℝ in nhdsWithin 0 (Ioi 0), CoJ k (2 ^ a) < CoJ k (3 * 2 ^ (a - 2)) := by
  have hcard : 2 ≤ (3 * 2 ^ (a - 2)).primeFactors.card :=
    card_primeFactors_mul_prime_pow_ge_two 3 2 (a - 2) Nat.prime_three Nat.prime_two
      (by norm_num) (by omega)
  apply eventually_lt_of_hasDerivAt
    (hasDerivAt_coJ_prime_pow 2 a Nat.prime_two (by omega))
    (hasDerivAt_coJ_of_two_le_card hcard)
  · have hleft : 1 < 2 ^ a := one_lt_pow₀ (by norm_num) (by omega)
    have hright : 1 < 3 * 2 ^ (a - 2) := by
      exact (show 1 < 3 by norm_num).trans_le
        (Nat.le_mul_of_pos_right 3 (pow_pos (by norm_num) _))
    rw [coJ_zero_of_one_lt hleft, coJ_zero_of_one_lt hright]
  · apply log_nat_lt_log_nat (by positivity)
    rw [show a - 1 = (a - 2) + 1 by omega, pow_succ]
    rw [mul_comm (2 ^ (a - 2)) 2]
    exact (Nat.mul_lt_mul_right (pow_pos (by norm_num) (a - 2))).2 (by norm_num)

private lemma eventually_strictRecord_of_two_le_card {n : ℕ}
    (hn : 2 ≤ n.primeFactors.card) :
    ∀ᶠ k : ℝ in nhdsWithin 0 (Ioi 0), StrictRecord k n := by
  let I : Finset ℕ := Finset.Ico 1 n
  have hEach : ∀ m ∈ I, ∀ᶠ k : ℝ in nhdsWithin 0 (Ioi 0), CoJ k m < CoJ k n := by
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Ico.mp hm).1
    have hmn : m < n := (Finset.mem_Ico.mp hm).2
    by_cases hmone : m = 1
    · subst m
      have hpositive : ∀ᶠ k : ℝ in nhdsWithin 0 (Ioi 0), 0 < CoJ k n := by
        filter_upwards [self_mem_nhdsWithin] with k hk
        have hn1 : 1 < n := Nat.nonempty_primeFactors.mp (Finset.card_pos.mp (by omega))
        have hquot : 0 < n / n.minFac :=
          Nat.div_pos (Nat.minFac_le (by omega)) (Nat.minFac_pos n)
        exact (Real.rpow_pos_of_pos (by exact_mod_cast hquot) k).trans_le
          (coJ_lower_bound hk hn1)
      simpa using hpositive
    · have hmgt : 1 < m := by omega
      obtain ⟨d, hd, hdle⟩ := hasDerivAt_coJ_of_one_lt hmgt
      apply eventually_lt_of_hasDerivAt hd (hasDerivAt_coJ_of_two_le_card hn)
      · rw [coJ_zero_of_one_lt hmgt,
          coJ_zero_of_one_lt (Nat.nonempty_primeFactors.mp (Finset.card_pos.mp (by omega)))]
      · exact hdle.trans_lt (log_nat_lt_log_nat (by omega) hmn)
  have hAll : ∀ᶠ k : ℝ in nhdsWithin 0 (Ioi 0), ∀ m ∈ I, CoJ k m < CoJ k n :=
    (Finset.eventually_all I).2 hEach
  filter_upwards [hAll] with k hk
  intro m hm1 hmn
  exact hk m (Finset.mem_Ico.mpr ⟨hm1, hmn⟩)

private lemma strictRecord_two (k : ℝ) : StrictRecord k 2 := by
  intro m hm hmlt
  have hmone : m = 1 := by omega
  subst m
  rw [coJ_one, coJ_prime Nat.prime_two]
  norm_num

private lemma strictRecord_four {k : ℝ} (hk : 0 < k) : StrictRecord k 4 := by
  have hfour : CoJ k 4 = (2 : ℝ) ^ k := by
    convert coJ_prime_pow 2 2 Nat.prime_two (by norm_num) k using 1 <;> norm_num
  intro m hm hmlt
  interval_cases m
  · rw [coJ_one, hfour]
    exact (Real.rpow_pos_of_pos (by norm_num) k)
  · rw [coJ_prime Nat.prime_two, hfour]
    exact Real.one_lt_rpow (by norm_num) hk
  · rw [coJ_prime Nat.prime_three, hfour]
    exact Real.one_lt_rpow (by norm_num) hk

private lemma not_eventual_of_prime_pow_outside {n : ℕ} (hn : 1 ≤ n)
    (hn1 : n ≠ 1) (hn2 : n ≠ 2) (hn4 : n ≠ 4)
    (hpp : IsPrimePow n) :
    ¬ ∃ ε : ℝ, 0 < ε ∧ ∀ k : ℝ, 0 < k → k < ε → StrictRecord k n := by
  obtain ⟨p, a, hp, ha, hpa⟩ := (isPrimePow_nat_iff _).mp hpp
  subst n
  intro heventual
  obtain ⟨ε, hε, hrecord⟩ := heventual
  by_cases ha1 : a = 1
  · subst a
    simp only [pow_one] at hn2 hn4 hrecord ⊢
    have hpgt : 2 < p := hp.two_le.lt_of_ne (Ne.symm hn2)
    have hrec := hrecord (ε / 2) (by positivity) (by linarith) 2 (by omega) hpgt
    rw [coJ_prime Nat.prime_two, coJ_prime hp] at hrec
    exact (lt_irrefl 1 hrec)
  by_cases hp2 : p = 2
  · subst p
    have ha3 : 3 ≤ a := by
      have ha2 : 2 ≤ a := by omega
      by_contra h
      have : a = 2 := by omega
      subst a
      simp at hn4
    have hlose := eventually_loses_two_pow ha3
    have hsmall : ∀ᶠ k : ℝ in nhdsWithin 0 (Ioi 0), k ∈ Ioo 0 ε :=
      Ioo_mem_nhdsGT hε
    obtain ⟨k, hklose, hk⟩ := Filter.nonempty_of_mem (hlose.and hsmall)
    have hcomp_lt : 3 * 2 ^ (a - 2) < 2 ^ a := by
      rw [show a = (a - 2) + 2 by omega, pow_add]
      rw [mul_comm (2 ^ (a - 2)) (2 ^ 2)]
      exact (Nat.mul_lt_mul_right (pow_pos (by norm_num) (a - 2))).2 (by norm_num)
    have hwitness : 1 ≤ 3 * 2 ^ (a - 2) :=
      Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num)))
    exact (lt_asymm hklose (hrecord k hk.1 hk.2 _ hwitness hcomp_lt))
  · have ha2 : 2 ≤ a := by omega
    have hlose := eventually_loses_odd_prime_pow hp hp2 ha2
    have hsmall : ∀ᶠ k : ℝ in nhdsWithin 0 (Ioi 0), k ∈ Ioo 0 ε :=
      Ioo_mem_nhdsGT hε
    obtain ⟨k, hklose, hk⟩ := Filter.nonempty_of_mem (hlose.and hsmall)
    have hcomp_lt : 2 * p ^ (a - 1) < p ^ a := by
      rw [show a = (a - 1) + 1 by omega, pow_succ]
      rw [mul_comm (p ^ (a - 1)) p]
      exact (Nat.mul_lt_mul_right (pow_pos hp.pos (a - 1))).2
        ((hp.two_le.lt_or_eq).resolve_right (Ne.symm hp2))
    have hwitness : 1 ≤ 2 * p ^ (a - 1) :=
      Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by norm_num) (pow_ne_zero _ hp.ne_zero))
    exact (lt_asymm hklose (hrecord k hk.1 hk.2 _ hwitness hcomp_lt))

/-- For each positive input, the strict records for all sufficiently small positive parameters
are exactly one, two, four, and the naturals with at least two distinct prime factors. -/
theorem a387335_eventual_record_iff :
    ∀ n ≥ 1,
      (∃ ε : ℝ, 0 < ε ∧ ∀ k : ℝ, 0 < k → k < ε → StrictRecord k n) ↔
        (n ∈ ({1, 2, 4} : Finset ℕ) ∨ 2 ≤ n.primeFactors.card) := by
  intro n hn
  constructor
  · intro heventual
    by_cases hn1 : n = 1
    · simp [hn1]
    by_cases hn2 : n = 2
    · simp [hn2]
    by_cases hn4 : n = 4
    · simp [hn4]
    right
    by_contra hcard
    have hcardPos : 0 < n.primeFactors.card :=
      Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr (by omega))
    have hcardOne : n.primeFactors.card = 1 := by omega
    exact not_eventual_of_prime_pow_outside hn hn1 hn2 hn4
      (isPrimePow_iff_card_primeFactors_eq_one.mpr hcardOne) heventual
  · rintro (hsmall | hcard)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hsmall
      rcases hsmall with rfl | rfl | rfl
      · exact ⟨1, by norm_num, fun _ _ _ m _ hmlt => by omega⟩
      · exact ⟨1, by norm_num, fun k _ _ => strictRecord_two k⟩
      · exact ⟨1, by norm_num, fun _ hk _ => strictRecord_four hk⟩
    · have hev := eventually_strictRecord_of_two_le_card hcard
      rcases mem_nhdsGT_iff_exists_Ioo_subset.mp hev with ⟨ε, hε, hsubset⟩
      exact ⟨ε, hε, fun k hk hkε => hsubset ⟨hk, hkε⟩⟩

end D5.S3.Factorization.JordanCototientRecordLimitZero
