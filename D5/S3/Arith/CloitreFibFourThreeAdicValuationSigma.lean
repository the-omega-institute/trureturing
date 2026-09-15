/- GID: D5/S3/Arith/CloitreFibFourThreeAdicValuationSigma
   generality: G
   mirror-B: D5/B/S3/Arith/CloitreFibFourThreeAdicValuationSigma
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: 3-adic Fibonacci valuations at indices 4n give a divisor-sum identity. -/

import Mathlib.Data.Int.Fib.Lemmas
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.Prime

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.CloitreFibFourThreeAdicValuationSigma

open Nat

private theorem fib_four_valuation {n : ℕ} (hn : 0 < n) :
    padicValNat 3 (Nat.fib (4 * n)) = padicValNat 3 n + 1 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have fib9_dvd_iff : ∀ {k : ℕ}, 0 < k → (9 ∣ Nat.fib k ↔ 12 ∣ k) := by
    intro k hk
    constructor
    · intro h9
      have h912 : 9 ∣ Nat.fib 12 := by norm_num
      have h9d : 9 ∣ Nat.fib (Nat.gcd k 12) := by
        rw [Nat.fib_gcd]
        exact Nat.dvd_gcd h9 h912
      have hdpos : 0 < Nat.gcd k 12 := Nat.gcd_pos_of_pos_left 12 hk
      have hdle : Nat.gcd k 12 ≤ 12 := Nat.gcd_le_right k (by norm_num)
      have hd : Nat.gcd k 12 = 12 := by
        interval_cases h : Nat.gcd k 12
        all_goals simp_all [Nat.fib]
      exact (Nat.gcd_eq_right_iff_dvd.mp hd)
    · intro h12
      obtain ⟨t, rfl⟩ := h12
      have hdiv : Nat.fib 12 ∣ Nat.fib (12 * t) :=
        Nat.fib_dvd 12 (12 * t) (by exact dvd_mul_right 12 t)
      exact dvd_trans (by norm_num : 9 ∣ Nat.fib 12) hdiv
  have fib_three_mul_four (m : ℕ) :
      Nat.fib (3 * (4 * m)) = Nat.fib (4 * m) * (5 * Nat.fib (4 * m) ^ 2 + 3) := by
    have hCass : Int.fib (4 * (m : ℤ) + 1) * Int.fib (4 * (m : ℤ) - 1) -
        Int.fib (4 * (m : ℤ)) ^ 2 = 1 := by
      have h := Int.fib_succ_mul_fib_pred_sub_fib_sq (4 * (m : ℤ))
      have hx : 0 ≤ 4 * (m : ℤ) := by positivity
      have hnat : (4 * (m : ℤ)).natAbs = 4 * m := by
        have hh := Int.natAbs_of_nonneg hx
        exact_mod_cast hh
      rw [hnat] at h
      have he : (-1 : ℤ) ^ (4 * m) = 1 := by
        rw [show 4 * m = 2 * (2 * m) by omega, pow_mul]
        norm_num
      simpa [he] using h
    have hrec : Int.fib (4 * (m : ℤ) + 1) =
        Int.fib (4 * (m : ℤ) - 1) + Int.fib (4 * (m : ℤ)) := by
      calc
        Int.fib (4 * (m : ℤ) + 1) = Int.fib ((4 * (m : ℤ) - 1) + 2) := by
          congr 1; ring
        _ = Int.fib (4 * (m : ℤ) - 1) + Int.fib (4 * (m : ℤ)) := by
          simpa [show (4 * (m : ℤ) - 1) + 1 = 4 * (m : ℤ) by ring] using
            (Int.fib_add_two (4 * (m : ℤ) - 1))
    have h2 : Int.fib (2 * (4 * (m : ℤ))) =
        Int.fib (4 * (m : ℤ)) * (2 * Int.fib (4 * (m : ℤ) + 1) - Int.fib (4 * (m : ℤ))) :=
      Int.fib_two_mul _
    have h2m1 : Int.fib (2 * (4 * (m : ℤ)) - 1) =
        Int.fib (4 * (m : ℤ)) ^ 2 + Int.fib (4 * (m : ℤ) - 1) ^ 2 := by
      calc
        Int.fib (2 * (4 * (m : ℤ)) - 1) = Int.fib (2 * (4 * (m : ℤ) - 1) + 1) := by
          congr 1; ring
        _ = Int.fib ((4 * (m : ℤ) - 1) + 1) ^ 2 + Int.fib (4 * (m : ℤ) - 1) ^ 2 := by
          simpa using (Int.fib_two_mul_add_one (4 * (m : ℤ) - 1))
        _ = Int.fib (4 * (m : ℤ)) ^ 2 + Int.fib (4 * (m : ℤ) - 1) ^ 2 := by
          rw [show (4 * (m : ℤ) - 1) + 1 = 4 * (m : ℤ) by ring]
    have h3 : Int.fib (3 * (4 * (m : ℤ))) =
        Int.fib (2 * (4 * (m : ℤ)) - 1) * Int.fib (4 * (m : ℤ)) +
          Int.fib (2 * (4 * (m : ℤ))) * Int.fib (4 * (m : ℤ) + 1) := by
      calc
        Int.fib (3 * (4 * (m : ℤ))) =
            Int.fib (2 * (4 * (m : ℤ)) + (4 * (m : ℤ))) := by
              congr 1; ring
        _ = Int.fib (2 * (4 * (m : ℤ)) - 1) * Int.fib (4 * (m : ℤ)) +
            Int.fib (2 * (4 * (m : ℤ))) * Int.fib ((4 * (m : ℤ)) + 1) := by
              simpa [show 2 * (4 * (m : ℤ)) - 1 = 2 * (4 * (m : ℤ)) - 1 by rfl] using
                (Int.fib_add (2 * (4 * (m : ℤ))) (4 * (m : ℤ)))
    have hz : Int.fib (3 * (4 * (m : ℤ))) =
        Int.fib (4 * (m : ℤ)) * (5 * Int.fib (4 * (m : ℤ)) ^ 2 + 3) := by
      rw [h3, h2m1, h2, hrec]
      calc
        (Int.fib (4 * (m : ℤ)) ^ 2 + Int.fib (4 * (m : ℤ) - 1) ^ 2) *
              Int.fib (4 * (m : ℤ)) +
            Int.fib (4 * (m : ℤ)) *
              (2 * (Int.fib (4 * (m : ℤ) - 1) + Int.fib (4 * (m : ℤ))) -
                Int.fib (4 * (m : ℤ))) *
              (Int.fib (4 * (m : ℤ) - 1) + Int.fib (4 * (m : ℤ))) =
            Int.fib (4 * (m : ℤ)) *
              (5 * Int.fib (4 * (m : ℤ)) ^ 2 +
                3 * (Int.fib (4 * (m : ℤ) - 1) ^ 2 +
                  Int.fib (4 * (m : ℤ) - 1) * Int.fib (4 * (m : ℤ)) -
                  Int.fib (4 * (m : ℤ)) ^ 2)) := by ring
        _ = Int.fib (4 * (m : ℤ)) * (5 * Int.fib (4 * (m : ℤ)) ^ 2 + 3) := by
          rw [hrec] at hCass
          have hpoly : Int.fib (4 * (m : ℤ) - 1) ^ 2 +
              Int.fib (4 * (m : ℤ) - 1) * Int.fib (4 * (m : ℤ)) -
              Int.fib (4 * (m : ℤ)) ^ 2 = 1 := by
            nlinarith [hCass]
          rw [hpoly]
          ring
    rw [← Int.ofNat_inj]
    have h1 : 3 * (4 * (m : ℤ)) = ((3 * (4 * m) : ℕ) : ℤ) := by norm_num
    have h2 : 4 * (m : ℤ) = ((4 * m : ℕ) : ℤ) := by norm_num
    rw [h1, h2, Int.fib_natCast] at hz
    exact hz
  have padicValNat_three_cofactor {f : ℕ} (hf3 : 3 ∣ f) :
      padicValNat 3 (5 * f ^ 2 + 3) = 1 := by
    obtain ⟨t, rfl⟩ := hf3
    have hqpos : 0 < 5 * (3 * t) ^ 2 + 3 := by positivity
    have hq3 : 3 ∣ 5 * (3 * t) ^ 2 + 3 := by
      refine ⟨15 * t ^ 2 + 1, ?_⟩
      ring
    have hq9 : ¬9 ∣ 5 * (3 * t) ^ 2 + 3 := by
      intro h
      have h' : 3 ∣ 15 * t ^ 2 + 1 := by
        apply Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 3)
        have hqeq : 5 * (3 * t) ^ 2 + 3 = 3 * (15 * t ^ 2 + 1) := by ring
        rw [hqeq] at h
        simpa [show 9 = 3 * 3 by norm_num, mul_assoc] using h
      obtain ⟨u, hu⟩ := h'
      have hmod : (15 * t ^ 2 + 1) % 3 = 1 := by
        omega
      rw [hu, Nat.mul_mod] at hmod
      norm_num at hmod
    have hge : 1 ≤ padicValNat 3 (5 * (3 * t) ^ 2 + 3) :=
      one_le_padicValNat_of_dvd hqpos.ne' hq3
    have hnle : ¬2 ≤ padicValNat 3 (5 * (3 * t) ^ 2 + 3) := by
      intro h2
      apply hq9
      have h9 : 3 ^ 2 ∣ 5 * (3 * t) ^ 2 + 3 :=
        (padicValNat_dvd_iff_le (p := 3) (n := 2) hqpos.ne').mpr h2
      simpa using h9
    omega
  have padicValNat_fib_three_mul_four {m : ℕ} (hm : 0 < m) :
      padicValNat 3 (Nat.fib (3 * (4 * m))) =
        padicValNat 3 (Nat.fib (4 * m)) + 1 := by
    have h3 : 3 ∣ Nat.fib (4 * m) := by
      simpa only [show Nat.fib 4 = 3 by norm_num] using
        (Nat.fib_dvd 4 (4 * m) (dvd_mul_right 4 m))
    have hf0 : Nat.fib (4 * m) ≠ 0 := by
      exact (Nat.fib_pos.mpr (by omega)).ne'
    rw [fib_three_mul_four]
    rw [padicValNat.mul hf0 (by positivity), padicValNat_three_cofactor h3]
  have padicValNat_fib_four_eq_one {m : ℕ} (hm : 0 < m) (hm3 : ¬3 ∣ m) :
      padicValNat 3 (Nat.fib (4 * m)) = 1 := by
    have h3 : 3 ∣ Nat.fib (4 * m) := by
      simpa only [show Nat.fib 4 = 3 by norm_num] using
        (Nat.fib_dvd 4 (4 * m) (dvd_mul_right 4 m))
    have hf0 : Nat.fib (4 * m) ≠ 0 := (Nat.fib_pos.mpr (by omega)).ne'
    have h9 : ¬9 ∣ Nat.fib (4 * m) := by
      intro h
      have h12 : 12 ∣ 4 * m := (fib9_dvd_iff (by omega)).mp h
      obtain ⟨t, ht⟩ := h12
      apply hm3
      refine ⟨3 * t, ?_⟩
      omega
    have hge : 1 ≤ padicValNat 3 (Nat.fib (4 * m)) :=
      one_le_padicValNat_of_dvd hf0 h3
    have hnle : ¬2 ≤ padicValNat 3 (Nat.fib (4 * m)) := by
      intro h2
      apply h9
      have hpow : 3 ^ 2 ∣ Nat.fib (4 * m) :=
        (padicValNat_dvd_iff_le (p := 3) (n := 2) hf0).mpr h2
      simpa using hpow
    omega
  let e := padicValNat 3 n
  let m := divMaxPow n 3
  have hmpos : 0 < m := by
    dsimp [m]
    have hdecomp := pow_padicValNat_mul_divMaxPow 3 n
    rw [Nat.mul_comm] at hdecomp
    have : 0 < 3 ^ e := by positivity
    exact (Nat.pos_of_mul_pos_right (hdecomp ▸ hn))
  have hm3 : ¬3 ∣ m := by
    dsimp [m]
    exact not_dvd_divMaxPow (by norm_num) hn.ne'
  have hdecomp : 3 ^ e * m = n := by
    dsimp [e, m]
    exact pow_padicValNat_mul_divMaxPow 3 n
  have hbase : padicValNat 3 (Nat.fib (4 * m)) = 1 :=
    padicValNat_fib_four_eq_one hmpos hm3
  have hiter : ∀ j : ℕ, padicValNat 3 (Nat.fib (4 * (3 ^ j * m))) = j + 1 := by
    intro j
    induction j with
    | zero => simpa using hbase
    | succ j ih =>
      have hrpos : 0 < 3 ^ j * m := Nat.mul_pos (by positivity) hmpos
      have hs := padicValNat_fib_three_mul_four hrpos
      calc
        padicValNat 3 (Nat.fib (4 * (3 ^ (j + 1) * m))) =
            padicValNat 3 (Nat.fib (3 * (4 * (3 ^ j * m)))) := by
              congr 2
              rw [pow_succ]
              ring
        _ = padicValNat 3 (Nat.fib (4 * (3 ^ j * m))) + 1 := hs
        _ = (j + 1) + 1 := by rw [ih]
  have hvaln : padicValNat 3 n = e := by
    rw [← hdecomp, padicValNat_base_pow_mul (by norm_num) hmpos.ne' e,
      padicValNat.eq_zero_of_not_dvd hm3, zero_add]
  calc
    padicValNat 3 (Nat.fib (4 * n)) =
        padicValNat 3 (Nat.fib (4 * (3 ^ e * m))) := by rw [hdecomp]
    _ = e + 1 := hiter e
    _ = padicValNat 3 n + 1 := by rw [hvaln]

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- The highest power of three dividing the Fibonacci number at index `4 * n`. -/
def a (n : ℕ) : ℕ := 3 ^ padicValNat 3 (Nat.fib (4 * n))

/-- The Marcus valuation formula and Bala's divisor-sum formula for every positive index. -/
theorem result (n : ℕ) (hn : 0 < n) :
    a n = 3 ^ (padicValNat 3 n + 1) ∧
    a n * (σ 1 (3 * n) - 3 * σ 1 n) = σ 1 (3 * n) - σ 1 n := by
  have sigma_three_pow_succ (k : ℕ) :
      σ 1 (3 ^ (k + 1)) = 3 * σ 1 (3 ^ k) + 1 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num)]
    have hsum : ∀ j : ℕ,
        (∑ i ∈ Finset.range (j + 2), 3 ^ i) =
          3 * (∑ i ∈ Finset.range (j + 1), 3 ^ i) + 1 := by
      intro j
      induction j with
      | zero => norm_num
      | succ j ih =>
        have hS : (∑ i ∈ Finset.range ((j + 1) + 1), 3 ^ i) =
            (∑ i ∈ Finset.range (j + 1), 3 ^ i) + 3 ^ (j + 1) := by
          rw [Finset.sum_range_succ]
        calc
          (∑ i ∈ Finset.range (Nat.succ j + 2), 3 ^ i) =
              (∑ i ∈ Finset.range (j + 2), 3 ^ i) + 3 ^ (j + 2) := by
                rw [show Nat.succ j + 2 = (j + 2) + 1 by omega,
                  Finset.sum_range_succ]
          _ = (3 * (∑ i ∈ Finset.range (j + 1), 3 ^ i) + 1) + 3 ^ (j + 2) := by
                rw [ih]
          _ = 3 * (∑ i ∈ Finset.range ((j + 1) + 1), 3 ^ i) + 1 := by
                rw [hS, pow_succ]
                ring
    simpa [Nat.add_assoc] using hsum k
  have sigma_three_pow_diff (k : ℕ) :
      σ 1 (3 ^ (k + 1)) - σ 1 (3 ^ k) = 3 ^ (k + 1) := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num)]
    have hsum : (∑ i ∈ Finset.range ((k + 1) + 1), 3 ^ i) =
        (∑ i ∈ Finset.range (k + 1), 3 ^ i) + 3 ^ (k + 1) := by
      rw [Finset.sum_range_succ]
    rw [show k + 1 + 1 = (k + 1) + 1 by omega, hsum]
    exact Nat.add_sub_cancel_left _ _
  let e := padicValNat 3 n
  let m := Nat.divMaxPow n 3
  have hmpos : 0 < m := by
    dsimp [m]
    have hdecomp := pow_padicValNat_mul_divMaxPow 3 n
    rw [Nat.mul_comm] at hdecomp
    exact Nat.pos_of_mul_pos_right (hdecomp ▸ hn)
  have hm3 : ¬3 ∣ m := by
    dsimp [m]
    exact not_dvd_divMaxPow (by norm_num) hn.ne'
  have hdecomp : 3 ^ e * m = n := by
    dsimp [e, m]
    exact pow_padicValNat_mul_divMaxPow 3 n
  have hcop : (3 ^ e).Coprime m :=
    (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr hm3 |>.pow_left e
  have h3decomp : 3 * n = 3 ^ (e + 1) * m := by
    rw [← hdecomp, pow_succ]
    ring
  have hsn : σ 1 n = σ 1 (3 ^ e) * σ 1 m := by
    rw [← hdecomp]
    exact ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop
  have hcop_succ : (3 ^ (e + 1)).Coprime m :=
    (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr hm3 |>.pow_left (e + 1)
  have hsn3 : σ 1 (3 * n) = σ 1 (3 ^ (e + 1)) * σ 1 m := by
    rw [h3decomp]
    exact ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop_succ
  have hsmpos : 0 < σ 1 m := ArithmeticFunction.sigma_pos 1 m hmpos.ne'
  have hval : padicValNat 3 (Nat.fib (4 * n)) = padicValNat 3 n + 1 :=
    fib_four_valuation hn
  have hfirst : a n = 3 ^ (padicValNat 3 n + 1) := by
    exact congrArg (fun z : ℕ => 3 ^ z) hval
  refine ⟨hfirst, ?_⟩
  simp only [a]
  rw [hval, hsn3, hsn]
  have hden : σ 1 (3 ^ (e + 1)) * σ 1 m - 3 * (σ 1 (3 ^ e) * σ 1 m) = σ 1 m := by
    rw [sigma_three_pow_succ]
    have hrewrite : (3 * σ 1 (3 ^ e) + 1) * σ 1 m =
        3 * (σ 1 (3 ^ e) * σ 1 m) + σ 1 m := by ring
    rw [hrewrite]
    exact Nat.add_sub_cancel_left _ _
  have hdenpos : 0 < σ 1 (3 * n) - 3 * σ 1 n := by
    rw [hsn3, hsn, hden]
    exact hsmpos
  have hnum : σ 1 (3 ^ (e + 1)) * σ 1 m - σ 1 (3 ^ e) * σ 1 m =
      3 ^ (e + 1) * σ 1 m := by
    have hd := sigma_three_pow_diff e
    have hmul := congrArg (fun z : ℕ => z * σ 1 m) hd
    rw [Nat.sub_mul] at hmul
    exact hmul
  rw [hden, hnum]

end D5.S3.Arith.CloitreFibFourThreeAdicValuationSigma
