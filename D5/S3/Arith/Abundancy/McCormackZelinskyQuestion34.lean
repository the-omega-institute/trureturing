/- GID: D5/S3/Arith/Abundancy/McCormackZelinskyQuestion34
   generality: I
   mirror-B: D5/B/S3/Arith/Abundancy/McCormackZelinskyQuestion34
   mirror-E: none(waiver:symbolic-logarithmic-inequality)
   anchors: [mathlib/module/Mathlib.Data.Nat.Totient]
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S3/Arith/Abundancy/McCormackZelinskyQuestion34.claim; result=D5/S3/Arith/Abundancy/McCormackZelinskyQuestion34.result; claim=D5/S3/Arith/Abundancy/McCormackZelinskyQuestion34.claim
   digest: Odd pseudoperfect divisor sets containing one have A strictly below C. -/

import D5.S3.Arith.Abundancy.WeightedTotientEulerDensity
import D5.S3.Arith.Abundancy.ZelinskyZhangDoublePrimitive

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Finset Real
open scoped BigOperators

namespace D5.S3.Arith.Abundancy.McCormackZelinskyQuestion34

open WeightedTotientEulerDensity
open ZelinskyZhangDoublePrimitive

/-- The existence asked for in McCormack--Zelinsky Question 34. -/
def claim : Prop :=
  ∃ n : ℕ, Odd n ∧ PrimitiveNonDeficient n ∧
    ∃ S : Finset ℕ, S ⊆ n.divisors ∧ 1 ∈ S ∧
      ∑ d ∈ S, d = 2 * n ∧ weightC S n < weightA S n

private theorem small_odd_totient_aux (n : ℕ) (hn : Odd n)
    (hsmall : Nat.totient n < 8) : n = 1 ∨ n = 3 ∨ n = 5 ∨ n = 7 ∨ n = 9 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h1 : n = 1
    · exact Or.inl h1
    have hn0 : 0 < n := by
      obtain ⟨k, hk⟩ := hn
      omega
    obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd h1
    have hpodd : Odd p := hn.of_dvd_nat hpn
    have hphi : Nat.totient p ≤ Nat.totient n :=
      Nat.le_of_dvd (Nat.totient_pos.mpr hn0) (Nat.totient_dvd_of_dvd hpn)
    rw [Nat.totient_prime hp] at hphi
    have hp8 : p < 9 := by omega
    have hp3 : p ∈ ({3, 5, 7} : Finset ℕ) := by
      have hpp := hp.two_le
      have hpodd' : p % 2 = 1 := by
        obtain ⟨k, hk⟩ := hpodd
        omega
      interval_cases p <;> norm_num at *
    let m := n / p
    have hmul : p * m = n := Nat.mul_div_cancel' hpn
    have hmdvd : m ∣ n := by
      rw [← hmul]
      exact dvd_mul_left m p
    have hmlt : m < n := Nat.div_lt_self hn0 hp.one_lt
    have hmphi : Nat.totient m < 8 :=
      (Nat.le_of_dvd (Nat.totient_pos.mpr hn0)
        (Nat.totient_dvd_of_dvd hmdvd)).trans_lt hsmall
    have hm := ih m hmlt (hn.of_dvd_nat hmdvd) hmphi
    have hmset : m ∈ ({1, 3, 5, 7, 9} : Finset ℕ) := by simpa using hm
    have hfinite : ∀ p ∈ ({3, 5, 7} : Finset ℕ),
        ∀ m ∈ ({1, 3, 5, 7, 9} : Finset ℕ), Nat.totient (p * m) < 8 →
          p * m = 1 ∨ p * m = 3 ∨ p * m = 5 ∨ p * m = 7 ∨ p * m = 9 := by
      decide
    rw [← hmul] at hsmall ⊢
    exact hfinite p hp3 m hmset hsmall

private lemma log_margin :
    2 * log 2 < (512 * log 2 + 80 * log 3) / 315 := by
  have h : log (8 : ℝ) < log 9 := log_lt_log (by norm_num) (by norm_num)
  have h8 : log (8 : ℝ) = 3 * log 2 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, log_pow]
    norm_num
  have h9 : log (9 : ℝ) = 2 * log 3 := by
    rw [show (9 : ℝ) = 3 ^ (2 : ℕ) by norm_num, log_pow]
    norm_num
  rw [h8, h9] at h
  have h2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  linarith

private lemma log_sum_lower (T : Finset ℕ)
    (hpos : ∀ e ∈ T, 0 < e)
    (hodd : ∀ e ∈ T, Odd e)
    (hsum : ∑ e ∈ T, (1 : ℝ) / e = 2) :
    (512 * log 2 + 80 * log 3) / 315 ≤ ∑ e ∈ T, log (Nat.totient e) / e := by
  classical
  have hclass : ∀ e ∈ T,
      e = 1 ∨ e = 3 ∨ e = 5 ∨ e = 7 ∨ e = 9 ∨ 8 ≤ Nat.totient e := by
    intro e he
    by_cases ht : Nat.totient e < 8
    · rcases small_odd_totient_aux e (hodd e he) ht with
        h | h | h | h | h <;> simp [h]
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by omega)))))
  let E : Finset ℕ := {1, 3, 5, 7, 9}
  let f : ℕ → ℝ := fun e =>
    if e ∈ E then (log 8 - log (Nat.totient e)) / e else 0
  have hphi1 : Nat.totient 1 = 1 := by decide
  have hphi3 : Nat.totient 3 = 2 := by decide
  have hphi5 : Nat.totient 5 = 4 := by decide
  have hphi7 : Nat.totient 7 = 6 := by decide
  have hphi9 : Nat.totient 9 = 6 := by decide
  have h4 : log (4 : ℝ) = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, log_pow]
    norm_num
  have h6 : log (6 : ℝ) = log 2 + log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, log_mul (by norm_num) (by norm_num)]
  have h8 : log (8 : ℝ) = 3 * log 2 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, log_pow]
    norm_num
  have hf : ∀ e, 0 ≤ f e := by
    intro e
    dsimp [f]
    split_ifs with he
    · have ht : (Nat.totient e : ℝ) ≤ 8 := by
        simp only [E, mem_insert, mem_singleton] at he
        rcases he with rfl | rfl | rfl | rfl | rfl <;>
          norm_num [hphi1, hphi3, hphi5, hphi7, hphi9]
      have htpos : (0 : ℝ) < Nat.totient e := by
        have hep : 0 < e := by
          simp only [E, mem_insert, mem_singleton] at he
          omega
        exact_mod_cast Nat.totient_pos.mpr hep
      exact div_nonneg (sub_nonneg.mpr (log_le_log htpos ht)) (by positivity)
    · rfl
  have hpoint : ∀ e ∈ T,
      log 8 / (e : ℝ) - f e ≤ log (Nat.totient e) / e := by
    intro e he
    by_cases heE : e ∈ E
    · simp only [f, ite_eq_left heE]
      exact le_of_eq (by ring)
    · simp only [f, ite_eq_right heE, sub_zero]
      have hc := hclass e he
      have ht : 8 ≤ Nat.totient e := by
        simp only [E, mem_insert, mem_singleton, not_or] at heE
        omega
      have hepos : (0 : ℝ) < e := by exact_mod_cast hpos e he
      apply div_le_div_of_nonneg_right _ hepos.le
      exact log_le_log (by norm_num) (by exact_mod_cast ht)
  have hbound : ∑ e ∈ T, f e ≤ ∑ e ∈ E, f e := by
    calc
      _ ≤ ∑ e ∈ T ∪ E, f e :=
        sum_le_sum_of_subset_of_nonneg subset_union_left (fun e _ _ => hf e)
      _ = ∑ e ∈ E, f e := by
        symm
        apply sum_subset subset_union_right
        intro e _ he
        simp [f, he]
  have hmass : ∑ e ∈ T, log 8 / (e : ℝ) = 2 * log 8 := by
    simp_rw [div_eq_mul_inv]
    rw [← mul_sum]
    have hm : ∑ e ∈ T, (e : ℝ)⁻¹ = 2 := by simpa using hsum
    rw [hm, mul_comm]
  have hfinite : (∑ e ∈ E, f e) =
      log 8 + (log 8 - log 2) / 3 + (log 8 - log 4) / 5 +
        (log 8 - log 6) / 7 + (log 8 - log 6) / 9 := by
    norm_num [E, f, hphi1, hphi3, hphi5, hphi7, hphi9]
    ring
  -- The five exceptional odd indices exhaust the entire possible deficit.
  rw [hfinite, h4, h6, h8] at hbound
  have hh := sum_le_sum hpoint
  rw [sum_sub_distrib, hmass, h8] at hh
  linarith

private lemma weightA_upper {n : ℕ} {S : Finset ℕ} (hn : 0 < n)
    (hS : S ⊆ n.divisors) (hsum : ∑ d ∈ S, d = 2 * n) :
    weightA S n ≤ log (Nat.totient n) -
      (1 / 2 : ℝ) * ∑ d ∈ S, log (Nat.totient (n / d)) / (n / d : ℕ) := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  have hsumR : (∑ d ∈ S, (d : ℝ)) = 2 * n := by
    have hs := congrArg (fun k : ℕ => (k : ℝ)) hsum
    simpa only [Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat] using hs
  have hweights : ∑ d ∈ S, (d : ℝ) / (2 * n) = 1 := by
    rw [← sum_div, hsumR]
    field_simp
  have hpoint : ∀ d ∈ S,
      (d : ℝ) / (2 * n) * log (Nat.totient d) ≤
        (d : ℝ) / (2 * n) * log (Nat.totient n) -
          (1 / 2 : ℝ) * (log (Nat.totient (n / d)) / (n / d : ℕ)) := by
    intro d hd
    have hdp := Nat.pos_of_mem_divisors (hS hd)
    have hdvd := Nat.dvd_of_mem_divisors (hS hd)
    have hep : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdvd) hdp
    have heR : (0 : ℝ) < (n / d : ℕ) := by exact_mod_cast hep
    have hφd : (0 : ℝ) < Nat.totient d := by exact_mod_cast Nat.totient_pos.mpr hdp
    have hφe : (0 : ℝ) < Nat.totient (n / d) := by
      exact_mod_cast Nat.totient_pos.mpr hep
    have hprod : (d : ℝ) * (n / d : ℕ) = n := by
      exact_mod_cast Nat.mul_div_cancel' hdvd
    have hφ := Nat.totient_super_multiplicative d (n / d)
    rw [Nat.mul_div_cancel' hdvd] at hφ
    have hlog : log (Nat.totient d) + log (Nat.totient (n / d)) ≤
        log (Nat.totient n) := by
      rw [← log_mul hφd.ne' hφe.ne']
      apply log_le_log (mul_pos hφd hφe)
      exact_mod_cast hφ
    have hw : (d : ℝ) / (2 * n) = 1 / (2 * (n / d : ℕ)) := by
      apply (div_eq_div_iff (by positivity) (by positivity)).mpr
      nlinarith [hprod]
    have hh := mul_le_mul_of_nonneg_left hlog
      (show 0 ≤ (d : ℝ) / (2 * n) by positivity)
    have heq : (d : ℝ) / (2 * n) * log (Nat.totient (n / d)) =
        (1 / 2 : ℝ) * (log (Nat.totient (n / d)) / (n / d : ℕ)) := by
      rw [hw]
      ring
    nlinarith
  have hh := sum_le_sum hpoint
  rw [sum_sub_distrib, ← sum_mul, ← mul_sum, hweights, one_mul] at hh
  exact hh

private lemma weightC_lower {n : ℕ} {S : Finset ℕ} (hn : 0 < n)
    (hS : S ⊆ n.divisors) (h1 : 1 ∈ S) (hsum : ∑ d ∈ S, d = 2 * n) :
    log (Nat.totient n) - log 2 < weightC S n := by
  classical
  have hSne : (S.erase 1).Nonempty := by
    by_contra h
    have he := (erase_eq_empty_iff S 1).mp (not_nonempty_iff_eq_empty.mp h)
    rcases he with he | he <;> simp [he] at hsum <;> omega
  have hz : 0 < ∑ d ∈ S.erase 1, (Nat.totient (n / d) : ℝ) / (2 * d) := by
    apply sum_pos _ hSne
    intro d hd
    have hdS := (mem_erase.mp hd).2
    have hdp := Nat.pos_of_mem_divisors (hS hdS)
    have hep := Nat.div_pos (Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors (hS hdS))) hdp
    have ht := Nat.totient_pos.mpr hep
    positivity
  have ht : (0 : ℝ) < Nat.totient n := by exact_mod_cast Nat.totient_pos.mpr hn
  have hlt : (Nat.totient n : ℝ) / 2 <
      ∑ d ∈ S, (Nat.totient (n / d) : ℝ) / (2 * d) := by
    rw [← sum_erase_add _ _ h1]
    simpa using (lt_add_of_pos_left ((Nat.totient n : ℝ) / 2) hz)
  rw [← log_div ht.ne' (by norm_num)]
  exact log_lt_log (by positivity) hlt

/-- Every odd divisor-sum set containing one satisfies the strict reverse inequality. -/
theorem odd_weight_reverse {n : ℕ} {S : Finset ℕ} (hn : Odd n)
    (hS : S ⊆ n.divisors) (h1 : 1 ∈ S) (hsum : ∑ d ∈ S, d = 2 * n) :
    weightA S n < weightC S n := by
  classical
  have hnp : 0 < n := Nat.pos_of_ne_zero (Nat.mem_divisors.mp (hS h1)).2
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnp
  let T := S.image (fun d => n / d)
  have hpos : ∀ e ∈ T, 0 < e := by
    intro e he
    obtain ⟨d, hd, rfl⟩ := mem_image.mp he
    exact Nat.div_pos (Nat.le_of_dvd hnp (Nat.dvd_of_mem_divisors (hS hd)))
      (Nat.pos_of_mem_divisors (hS hd))
  have hdvd : ∀ e ∈ T, e ∣ n := by
    intro e he
    obtain ⟨d, hd, rfl⟩ := mem_image.mp he
    exact Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors (hS hd))
  have hinj : Set.InjOn (fun d => n / d) (↑S : Set ℕ) := by
    intro d hd e he hde
    have hdvd := Nat.dvd_of_mem_divisors (hS hd)
    have hevd := Nat.dvd_of_mem_divisors (hS he)
    have he0 := Nat.pos_of_mem_divisors (hS he)
    have heq0 : 0 < n / e := Nat.div_pos (Nat.le_of_dvd hnp hevd) he0
    have hdprod := Nat.mul_div_cancel' hdvd
    have heprod := Nat.mul_div_cancel' hevd
    change n / d = n / e at hde
    rw [hde] at hdprod
    exact Nat.eq_of_mul_eq_mul_right heq0 (hdprod.trans heprod.symm)
  have hmass : ∑ e ∈ T, (1 : ℝ) / e = 2 := by
    rw [show T = S.image (fun d => n / d) from rfl, sum_image hinj]
    have hp : ∀ d ∈ S, (1 : ℝ) / (n / d : ℕ) = (d : ℝ) / n := by
      intro d hd
      have hdp := Nat.pos_of_mem_divisors (hS hd)
      have hdvd := Nat.dvd_of_mem_divisors (hS hd)
      have hep := Nat.div_pos (Nat.le_of_dvd hnp hdvd) hdp
      have heR : (0 : ℝ) < (n / d : ℕ) := by exact_mod_cast hep
      apply (div_eq_div_iff heR.ne' hnR.ne').mpr
      simpa only [one_mul, Nat.cast_mul] using
        congrArg (fun k : ℕ => (k : ℝ)) (Nat.mul_div_cancel' hdvd).symm
    simp_rw [sum_congr rfl hp, ← sum_div]
    have hs : ∑ d ∈ S, (d : ℝ) = 2 * n := by
      have hs := congrArg (fun k : ℕ => (k : ℝ)) hsum
      simpa only [Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat] using hs
    rw [hs]
    field_simp
  have hl := log_sum_lower T hpos (fun e he => hn.of_dvd_nat (hdvd e he)) hmass
  have hstrict := log_margin.trans_le hl
  rw [show T = S.image (fun d => n / d) from rfl, sum_image hinj] at hstrict
  have hA := weightA_upper hnp hS hsum
  have hC := weightC_lower hnp hS h1 hsum
  linarith

/-- Question 34 has a negative answer, without needing primitiveness. -/
theorem result : ¬ claim := by
  rintro ⟨n, hn, _, S, hS, h1, hsum, hlt⟩
  exact (odd_weight_reverse hn hS h1 hsum).not_gt hlt

end D5.S3.Arith.Abundancy.McCormackZelinskyQuestion34
