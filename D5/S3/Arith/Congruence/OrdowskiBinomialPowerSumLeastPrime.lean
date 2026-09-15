/- GID: D5/S3/Arith/Congruence/OrdowskiBinomialPowerSumLeastPrime
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/OrdowskiBinomialPowerSumLeastPrime
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Ordowski's binomial and power-sum conditions have the same least prime. -/

import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.FieldTheory.Finite.Basic

namespace D5.S3.Arith.Congruence.OrdowskiBinomialPowerSumLeastPrime

open Finset

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- OEIS A133907: least prime number `p` such that `binomial(n+p, p) mod p = 1`.
The defining set is nonempty, as established inside `result`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {p : ℕ | p.Prime ∧ (n + p).choose p ≡ 1 [MOD p]}

/-- Ordowski's conjecture: for every positive natural `n`, A133907 is the smallest
prime `p` such that the sum of `k^(p-1)` for `1 ≤ k ≤ n` is congruent to `n` modulo `p`. -/
theorem result (n : ℕ) (_hn : 0 < n) :
    IsLeast {p : ℕ | p.Prime ∧
      (∑ k ∈ Finset.Icc 1 n, k ^ (p - 1)) ≡ n [MOD p]} (a n) := by
  have hchoose (p : ℕ) (hp : p.Prime) :
      ((n + p).choose p : ZMod p) = (n / p : ℕ) + 1 := by
    let : Fact p.Prime := ⟨hp⟩
    have h := (ZMod.natCast_eq_natCast_iff _ _ _).2
      (Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := n + p) (k := p) (p := p))
    simpa [Nat.add_div_right, hp.pos, hp.ne_zero] using h
  have hsum (p : ℕ) (hp : p.Prime) :
      (∑ k ∈ Finset.Icc 1 n, (k : ZMod p) ^ (p - 1)) =
        (n : ZMod p) - (n / p : ℕ) := by
    let : Fact p.Prime := ⟨hp⟩
    have hI : Finset.Icc 1 n = Finset.Ioc 0 n := by
      simpa using (Finset.Icc_succ_left_eq_Ioc (0 : ℕ) n)
    calc
      _ = ∑ k ∈ Finset.Ioc 0 n, (1 - if p ∣ k then 1 else 0 : ZMod p) := by
        rw [hI]
        apply Finset.sum_congr rfl
        intro k _
        rw [ZMod.pow_card_sub_one]
        by_cases hk : p ∣ k <;> simp [ZMod.natCast_eq_zero_iff, hk]
      _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_boole]
        simp [Nat.Ioc_filter_dvd_card_eq_div]
  have hiff (p : ℕ) (hp : p.Prime) :
      (n + p).choose p ≡ 1 [MOD p] ↔
        (∑ k ∈ Finset.Icc 1 n, k ^ (p - 1)) ≡ n [MOD p] := by
    rw [← ZMod.natCast_eq_natCast_iff, ← ZMod.natCast_eq_natCast_iff]
    simp only [Nat.cast_one, Nat.cast_sum, Nat.cast_pow]
    rw [hchoose p hp, hsum p hp]
    simp
  have hex : {p : ℕ | p.Prime ∧ (n + p).choose p ≡ 1 [MOD p]}.Nonempty := by
    obtain ⟨p, hpn, hp⟩ := Nat.exists_infinite_primes (n + 1)
    refine ⟨p, hp, ?_⟩
    apply (ZMod.natCast_eq_natCast_iff _ _ _).1
    rw [hchoose p hp, Nat.div_eq_of_lt (by omega : n < p)]
    simp
  have ha : (a n).Prime ∧ (n + a n).choose (a n) ≡ 1 [MOD a n] :=
    Nat.sInf_mem hex
  refine ⟨⟨ha.1, (hiff (a n) ha.1).1 ha.2⟩, ?_⟩
  intro p hp
  exact Nat.sInf_le ⟨hp.1, (hiff p hp.1).2 hp.2⟩

end D5.S3.Arith.Congruence.OrdowskiBinomialPowerSumLeastPrime
