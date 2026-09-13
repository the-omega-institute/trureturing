/- GID: D5/S3/Factorization/GerasimovLeastEvenDivisorCountPowerOfTwo
   generality: G
   mirror-B: D5/B/S3/Factorization/GerasimovLeastEvenDivisorCountPowerOfTwo
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Finset.NatDivisors, mathlib/module/Mathlib.Order.Lattice.Nat, mathlib/module/Mathlib.Tactic.NormNum, mathlib/module/Mathlib.Tactic.NormNum.Parity, mathlib/module/Mathlib.Tactic.NormNum.Prime]
   utility: none
   digest: The least number with n even divisors is 2^n only when n is prime or one (positive n). -/

import Mathlib.Data.Finset.NatDivisors
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

namespace D5.S3.Factorization.GerasimovLeastEvenDivisorCountPowerOfTwo

def E (m : ℕ) : ℕ := (m.divisors.filter Even).card

noncomputable def a (n : ℕ) : ℕ := sInf {m : ℕ | 0 < m ∧ E m = n}

private theorem even_divisor_count_two_pow_mul_three_pow (a b : ℕ) :
    E (2 ^ a * 3 ^ b) = a * (b + 1) := by
  classical
  unfold E
  have hcop : Nat.Coprime (2 ^ a) (3 ^ b) := by
    exact Nat.Coprime.pow a b (by norm_num : Nat.Coprime 2 3)
  rw [Nat.Coprime.divisors_mul hcop]
  rw [Finset.filter_map, Finset.card_map]
  let s : Finset (ℕ × ℕ) := (2 ^ a).divisors ×ˢ (3 ^ b).divisors
  change (s.attach.filter (fun p => Even (p.val.1 * p.val.2))).card = a * (b + 1)
  rw [Finset.filter_attach (fun x : ℕ × ℕ => Even (x.1 * x.2)) s]
  rw [Finset.card_map, Finset.card_attach]
  have hprod :
      s.filter (fun x => Even (x.1 * x.2)) =
        ((2 ^ a).divisors.filter Even) ×ˢ (3 ^ b).divisors := by
    dsimp [s]
    rw [← Finset.filter_product_left Even]
    apply Finset.filter_congr
    intro x hx
    have hx2 : x.2 ∈ (3 ^ b).divisors := (Finset.mem_product.mp hx).2
    obtain ⟨j, hj, hxj⟩ :=
      (Nat.mem_divisors_prime_pow (by norm_num : Nat.Prime 3) b).1 hx2
    have hodd : ¬Even x.2 := by
      rw [hxj, Nat.even_pow]
      norm_num
    rw [Nat.even_mul]
    simp [hodd]
  have h2 : ((2 ^ a).divisors.filter Even).card = a := by
    rw [Nat.divisors_prime_pow (by norm_num : Nat.Prime 2) a]
    rw [Finset.filter_map, Finset.card_map]
    have hfilter :
        (Finset.range (a + 1)).filter (fun j => Even (2 ^ j)) = Finset.Ico 1 (a + 1) := by
      ext j
      simp [Nat.even_pow]
      omega
    change ((Finset.range (a + 1)).filter (fun j => Even (2 ^ j))).card = a
    rw [hfilter]
    simp
  have h3 : (3 ^ b).divisors.card = b + 1 := by
    rw [Nat.divisors_prime_pow (by norm_num : Nat.Prime 3) b]
    simp
  rw [hprod, Finset.card_product, h2, h3]

theorem gerasimov_a187941 : ∀ n : ℕ, 1 ≤ n → a n = 2 ^ n → Nat.Prime n ∨ n = 1 := by
  intro n hn hpow
  by_cases hn1 : n = 1
  · exact Or.inr hn1
  have hn2 : 2 ≤ n := by omega
  by_contra hnot
  have hnp : ¬Nat.Prime n := by
    intro hp
    exact hnot (Or.inl hp)
  let d := n.minFac
  let e := n / n.minFac
  have hd : 2 ≤ d := by
    dsimp [d]
    exact (Nat.minFac_prime (by omega : n ≠ 1)).two_le
  have he : 2 ≤ e := by
    dsimp [e]
    exact le_trans hd (Nat.minFac_le_div (by omega) hnp)
  have hde : d * e = n := by
    dsimp [d, e]
    exact Nat.mul_div_cancel' (Nat.minFac_dvd n)
  let m := 2 ^ d * 3 ^ (e - 1)
  have hEm : E m = n := by
    dsimp [m]
    rw [even_divisor_count_two_pow_mul_three_pow]
    rw [Nat.sub_add_cancel (by omega : 1 ≤ e), hde]
  have hm : m ∈ {m : ℕ | 0 < m ∧ E m = n} := by
    refine ⟨?_, hEm⟩
    dsimp [m]
    positivity
  have hle : a n ≤ m := Nat.sInf_le hm
  have hthree : 3 ^ (e - 1) < 4 ^ (e - 1) := by
    apply Nat.pow_lt_pow_left (by norm_num)
    omega
  have hfour : 4 ^ (e - 1) = 2 ^ (2 * (e - 1)) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, pow_mul]
  have hexp : 2 * (e - 1) ≤ d * (e - 1) := by
    exact Nat.mul_le_mul_right (e - 1) hd
  have hpowle : 2 ^ (2 * (e - 1)) ≤ 2 ^ (d * (e - 1)) := by
    exact Nat.pow_le_pow_right (by norm_num) hexp
  have hprod : m < 2 ^ d * 2 ^ (d * (e - 1)) := by
    dsimp [m]
    exact Nat.mul_lt_mul_of_pos_left (hthree.trans_le (hfour ▸ hpowle)) (by positivity)
  have hlt : m < 2 ^ n := by
    calc
      m < 2 ^ d * 2 ^ (d * (e - 1)) := hprod
      _ = 2 ^ (d * e) := by
        rw [← pow_add]
        congr 1
        rw [Nat.mul_sub_left_distrib, Nat.mul_one]
        exact Nat.add_sub_of_le (Nat.le_mul_of_pos_right d (by omega : 0 < e))
      _ = 2 ^ n := by rw [hde]
  have : a n < 2 ^ n := lt_of_le_of_lt hle hlt
  rw [hpow] at this
  exact (Nat.lt_irrefl _ this).elim

end D5.S3.Factorization.GerasimovLeastEvenDivisorCountPowerOfTwo
