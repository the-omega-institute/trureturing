/- GID: D5/S3/Factorization/A091259
   generality: I
   mirror-B: D5/B/S3/Factorization/A091259
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The reduced sigma-three over sigma-one numerator satisfies the A353816 criterion. -/


import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/- Search receipts (2026-09-09):
   OEIS A091259 still labels Marcus's 2024-08-11 assertion a conjecture; A353816 explicitly
   states the prime-exponent criterion used below. The quadratic-form characterization is
   outside this theorem's scope. The three GoldenResource modules named in the task supply
   the existing sigma API pattern. Pinned Mathlib supplies multiplicative_factorization,
   sigma_apply_prime_pow, coprime_div_gcd_div_gcd, and orderOf_dvd_card_sub_one; these are reused.
   Repository and pinned-Mathlib searches found no A091259 theorem. Authenticated GitHub code
   search for A091259 language:Lean returned total_count=0. This is a bounded search receipt,
   not a claim that no proof exists anywhere. -/

namespace D5.S3.Factorization.A091259

open Finset

theorem mod_three_of_prime_divisors (n : ℕ) (hn : n ≠ 0)
    (h : ∀ p, p.Prime → p ∣ n → p % 3 = 1) : n % 3 = 1 := by
  induction n using induction_on_primes with
  | zero => exact (hn rfl).elim
  | one => rfl
  | prime_mul p a hp ih =>
      have ha : a ≠ 0 := by intro ha; simp [ha] at hn
      rw [Nat.mul_mod, h p hp (dvd_mul_right p a),
        ih ha (fun q hq hqa => h q hq (dvd_mul_of_dvd_right hqa p))]

theorem divisors_mul_mod_three {a b : ℕ}
    (ha : ∀ d, d ∣ a → d % 3 = 1) (hb : ∀ d, d ∣ b → d % 3 = 1) :
    ∀ d, d ∣ a * b → d % 3 = 1 := by
  have ha0 : a ≠ 0 := by intro h; simpa [h] using ha a dvd_rfl
  have hb0 : b ≠ 0 := by intro h; simpa [h] using hb b dvd_rfl
  intro d hd
  apply mod_three_of_prime_divisors d (ne_zero_of_dvd_ne_zero (mul_ne_zero ha0 hb0) hd)
  intro p hp hpd
  rcases hp.dvd_mul.mp (hpd.trans hd) with hpa | hpb
  · exact ha p hpa
  · exact hb p hpb

/-- Cancellation removes only divisors of the supplied denominator, all congruent to one. -/
theorem reduced_numerator_mod_three {a b A B : ℕ} (hb : 0 < b)
    (hB : ∀ d, d ∣ B → d % 3 = 1) (hcross : a * B = b * A) :
    (a / Nat.gcd a b) % 3 = A % 3 := by
  let g := Nat.gcd a b
  let x := a / g
  let y := b / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_right a hb
  have hgA : g * x = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
  have hgB : g * y = b := Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
  have hxy : x * B = y * A := by
    apply Nat.eq_of_mul_eq_mul_left hg
    calc
      g * (x * B) = a * B := by rw [← mul_assoc, hgA]
      _ = b * A := hcross
      _ = g * (y * A) := by rw [← mul_assoc, hgB]
  have hc : Nat.Coprime x y := Nat.coprime_div_gcd_div_gcd hg
  have hyB : y ∣ B := hc.symm.dvd_mul_left.mp (hxy ▸ dvd_mul_right y A)
  obtain ⟨t, ht⟩ := hyB
  have hy : 0 < y := by
    apply Nat.pos_of_ne_zero
    intro h
    rw [h, mul_zero] at hgB
    omega
  have hA : A = x * t := by
    apply Nat.eq_of_mul_eq_mul_left hy
    rw [← hxy, ht]
    ac_rfl
  have htmod : t % 3 = 1 := hB t (ht ▸ dvd_mul_left t y)
  change x % 3 = A % 3
  rw [hA, Nat.mul_mod, htmod, mul_one, Nat.mod_mod]

def cyclotomicThree (t : ℕ) : ℕ := t ^ 2 + t + 1

theorem cyclotomicThree_mod (t : ℕ) :
    cyclotomicThree t % 3 = if t % 3 = 1 then 0 else 1 := by
  have h : t % 3 = 0 ∨ t % 3 = 1 ∨ t % 3 = 2 := by omega
  rcases h with h | h | h <;>
    simp [cyclotomicThree, Nat.add_mod, Nat.pow_mod, h]

theorem cyclotomicThree_div_three (t : ℕ) (ht : t % 3 = 1) :
    3 ∣ cyclotomicThree t ∧ (cyclotomicThree t / 3) % 3 = 1 := by
  have heq : t = 3 * (t / 3) + 1 := by omega
  have hpoly : cyclotomicThree t = 3 * (1 + 3 * (t / 3) + 3 * (t / 3) ^ 2) := by
    unfold cyclotomicThree
    conv_lhs => rw [heq]
    ring
  rw [hpoly]
  constructor
  · exact dvd_mul_right _ _
  · simp [Nat.add_mod]

theorem cyclotomicThree_prime_divisor {t q : ℕ} (hq : q.Prime)
    (hqt : q ∣ cyclotomicThree t) (hq3 : q ≠ 3) : q % 3 = 1 := by
  let : Fact q.Prime := ⟨hq⟩
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hz : (t : ZMod q) ^ 2 + t + 1 = 0 := by
    have h := (ZMod.natCast_eq_zero_iff (cyclotomicThree t) q).2 hqt
    simpa [cyclotomicThree] using h
  have ht0 : (t : ZMod q) ≠ 0 := by intro h; simp [h] at hz
  have ht1 : (t : ZMod q) ≠ 1 := by
    intro h
    have h3 : (3 : ZMod q) = 0 := by
      convert hz using 1
      rw [h]
      ring
    have hd : q ∣ 3 := (ZMod.natCast_eq_zero_iff 3 q).1 h3
    exact hq3 ((Nat.dvd_prime (by decide : Nat.Prime 3)).1 hd |>.resolve_left hq.ne_one)
  have hc : (t : ZMod q) ^ 3 = 1 := by
    apply sub_eq_zero.mp
    calc
      (t : ZMod q) ^ 3 - 1 = (t - 1) * (t ^ 2 + t + 1) := by ring
      _ = 0 := by rw [hz, mul_zero]
  have ho : orderOf (t : ZMod q) = 3 := orderOf_eq_prime hc ht1
  have hd := ZMod.orderOf_dvd_card_sub_one ht0
  rw [ho] at hd
  have hm := Nat.mod_eq_zero_of_dvd hd
  have := hq.two_le
  omega

def strippedThree (t : ℕ) : ℕ :=
  cyclotomicThree t / (if t % 3 = 1 then 3 else 1)

/-- The removed factor of three is exact; every remaining prime divisor is one modulo three. -/
theorem strippedThree_divisors (t : ℕ) :
    ∀ d, d ∣ strippedThree t → d % 3 = 1 := by
  have hm : strippedThree t % 3 = 1 := by
    by_cases ht : t % 3 = 1
    · simpa [strippedThree, ht] using (cyclotomicThree_div_three t ht).2
    · simp [strippedThree, ht, cyclotomicThree_mod]
  have hn : strippedThree t ≠ 0 := by intro h; simp [h] at hm
  have hd : strippedThree t ∣ cyclotomicThree t := by
    unfold strippedThree
    split
    · exact Nat.div_dvd_of_dvd (cyclotomicThree_div_three t ‹_›).1
    · simp
  intro d hdt
  apply mod_three_of_prime_divisors d (ne_zero_of_dvd_ne_zero hn hdt)
  intro q hq hqd
  apply cyclotomicThree_prime_divisor hq (hqd.trans (hdt.trans hd))
  intro heq
  subst q
  have hzero := Nat.mod_eq_zero_of_dvd (hqd.trans hdt)
  omega

def localNumerator (p e : ℕ) : ℕ :=
  cyclotomicThree (p ^ (e + 1)) / (if p % 3 = 1 then 3 else 1)

theorem sigma_prime_power_cross {p : ℕ} (hp : p.Prime) (e : ℕ) :
    ArithmeticFunction.sigma 3 (p ^ e) * cyclotomicThree p =
      ArithmeticFunction.sigma 1 (p ^ e) * cyclotomicThree (p ^ (e + 1)) := by
  rw [ArithmeticFunction.sigma_apply_prime_pow hp,
    ArithmeticFunction.sigma_one_apply_prime_pow hp]
  unfold cyclotomicThree
  zify
  have h1 := geom_sum_mul (p : ℤ) (e + 1)
  have h3 : (∑ j ∈ range (e + 1), (p : ℤ) ^ (j * 3)) * ((p : ℤ) ^ 3 - 1) =
      ((p : ℤ) ^ (e + 1)) ^ 3 - 1 := by
    have h := geom_sum_mul ((p : ℤ) ^ 3) (e + 1)
    simp_rw [pow_right_comm (p : ℤ) 3] at h
    simpa only [pow_mul] using h
  apply mul_right_cancel₀ (show (p : ℤ) - 1 ≠ 0 by have := hp.two_le; omega)
  linear_combination h3 - (((p : ℤ) ^ (e + 1)) ^ 2 + (p : ℤ) ^ (e + 1) + 1) * h1

theorem localNumerator_cross {p : ℕ} (hp : p.Prime) (e : ℕ) :
    ArithmeticFunction.sigma 3 (p ^ e) * strippedThree p =
      ArithmeticFunction.sigma 1 (p ^ e) * localNumerator p e := by
  have h := sigma_prime_power_cross hp e
  unfold strippedThree localNumerator
  by_cases hp1 : p % 3 = 1
  · simp only [hp1, if_true]
    have hpk : p ^ (e + 1) % 3 = 1 := by simp [Nat.pow_mod, hp1]
    have hd := (cyclotomicThree_div_three p hp1).1
    have hn := (cyclotomicThree_div_three (p ^ (e + 1)) hpk).1
    rw [← Nat.mul_div_assoc _ hd, ← Nat.mul_div_assoc _ hn, h]
  · simpa [hp1] using h

theorem localNumerator_mod (p e : ℕ) :
    localNumerator p e % 3 = if p % 3 = 2 → Even e then 1 else 0 := by
  by_cases hp1 : p % 3 = 1
  · have hpk : p ^ (e + 1) % 3 = 1 := by simp [Nat.pow_mod, hp1]
    simpa [localNumerator, hp1] using
      (cyclotomicThree_div_three (p ^ (e + 1)) hpk).2
  · simp only [localNumerator, hp1, if_false, Nat.div_one, cyclotomicThree_mod]
    have hr : p % 3 = 0 ∨ p % 3 = 2 := by omega
    rcases hr with hp0 | hp2
    · simp [Nat.pow_mod, hp0]
    · have hpow : p ^ (e + 1) % 3 = if Even e then 2 else 1 := by
        have he : e = 2 * (e / 2) + e % 2 := by omega
        rw [he, Nat.pow_mod, hp2]
        have hh : e % 2 = 0 ∨ e % 2 = 1 := by omega
        rcases hh with hh | hh <;>
          simp [hh, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
      rw [hpow]
      by_cases he : Even e <;> simp [hp2, he]

def a353816FactorIndicator (n : ℕ) : ℕ :=
  if ∀ p ∈ n.primeFactors, p % 3 = 2 → Even (n.factorization p) then 1 else 0

theorem localNumerator_prod_mod (s : Finset ℕ) (e : ℕ → ℕ) :
    (∏ p ∈ s, localNumerator p (e p)) % 3 =
      if ∀ p ∈ s, p % 3 = 2 → Even (e p) then 1 else 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
      rw [prod_insert hp, Nat.mul_mod, localNumerator_mod, ih]
      simp only [forall_mem_insert]
      by_cases h1 : p % 3 = 2 → Even (e p)
      · by_cases h2 : ∀ q ∈ s, q % 3 = 2 → Even (e q)
        · rw [if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩]
        · rw [if_pos h1, if_neg h2, if_neg (fun h => h2 h.2)]
      · rw [if_neg h1, zero_mul, if_neg (fun h => h1 h.1), Nat.zero_mod]

/-- Michel Marcus's A091259 conjecture, with the published A353816 factor criterion. -/
theorem a091259_mod_three (n : ℕ) (hn : 0 < n) :
    ((ArithmeticFunction.sigma 3) n /
       Nat.gcd ((ArithmeticFunction.sigma 3) n) ((ArithmeticFunction.sigma 1) n)) % 3
      = a353816FactorIndicator n := by
  let A := ∏ p ∈ n.primeFactors, localNumerator p (n.factorization p)
  let B := ∏ p ∈ n.primeFactors, strippedThree p
  have hB : ∀ d, d ∣ B → d % 3 = 1 := by
    dsimp [B]
    induction n.primeFactors using Finset.induction_on with
    | empty => simp
    | @insert p s hp ih =>
        rw [prod_insert hp]
        exact divisors_mul_mod_three (strippedThree_divisors p) ih
  have hcross : ArithmeticFunction.sigma 3 n * B = ArithmeticFunction.sigma 1 n * A := by
    dsimp [A, B]
    rw [(ArithmeticFunction.isMultiplicative_sigma (k := 3)).multiplicative_factorization _ hn.ne',
      (ArithmeticFunction.isMultiplicative_sigma (k := 1)).multiplicative_factorization _ hn.ne']
    simp only [Finsupp.prod, Nat.support_factorization, ← prod_mul_distrib]
    apply prod_congr rfl
    intro p hp
    exact localNumerator_cross (Nat.prime_of_mem_primeFactors hp) (n.factorization p)
  rw [reduced_numerator_mod_three (ArithmeticFunction.sigma_pos 1 n hn.ne') hB hcross]
  exact localNumerator_prod_mod n.primeFactors n.factorization

#print axioms mod_three_of_prime_divisors
#print axioms divisors_mul_mod_three
#print axioms reduced_numerator_mod_three
#print axioms cyclotomicThree_mod
#print axioms cyclotomicThree_div_three
#print axioms cyclotomicThree_prime_divisor
#print axioms strippedThree_divisors
#print axioms sigma_prime_power_cross
#print axioms localNumerator_cross
#print axioms localNumerator_mod
#print axioms localNumerator_prod_mod
#print axioms a091259_mod_three

end D5.S3.Factorization.A091259
