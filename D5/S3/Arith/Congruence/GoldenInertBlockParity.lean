/- GID: D5/S3/Arith/Congruence/GoldenInertBlockParity
   generality: G
   mirror-B: none(waiver:all-odd-base-power-layers)
   mirror-E: none(waiver:unbounded-exact-factorization-parity)
   anchors: []
   digest: The mod-five character equals odd inert-factor parity and stays negative in every inert odd-base Fibonacci power layer. -/

import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Arith.Congruence.GoldenInertBlockParity

open Finset

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- The quadratic character of the fixed discriminant-five field, on natural inputs. -/
noncomputable def chi (n : ℕ) : ℤ := legendreSym 5 (n : ℤ)

/-- Distinct prime divisors with negative character and odd ACTUAL multiplicity. -/
noncomputable def oddInertFactors (N : ℕ) : Finset ℕ := by
  classical
  exact N.primeFactors.filter fun p => chi p = -1 ∧ Odd (N.factorization p)

/-- The exact quotient between consecutive Fibonacci power indices.
The public arithmetic hypotheses below guarantee a positive denominator and exact division. -/
def powerBlock (ell k : ℕ) : ℕ :=
  Nat.fib (ell ^ (k + 1)) / Nat.fib (ell ^ k)

@[simp] private lemma chi_zero : chi 0 = 0 := by simp [chi]
@[simp] private lemma chi_one : chi 1 = 1 := by simp [chi]

private lemma chi_mul (m n : ℕ) : chi (m * n) = chi m * chi n := by
  simpa only [chi, Nat.cast_mul] using legendreSym.mul 5 (m : ℤ) (n : ℤ)

private noncomputable def chiHom : ℕ →* ℤ where
  toFun := chi
  map_one' := chi_one
  map_mul' := chi_mul

private lemma chi_pow (n k : ℕ) : chi (n ^ k) = chi n ^ k :=
  map_pow chiHom n k

private lemma chi_congr {m n : ℕ} (h : (m : ZMod 5) = (n : ZMod 5)) :
    chi m = chi n := by
  unfold chi legendreSym
  simpa only [Int.cast_natCast] using congrArg (quadraticChar (ZMod 5)) h

private lemma chi_cases (n : ℕ) (hn : ¬5 ∣ n) : chi n = 1 ∨ chi n = -1 := by
  have hz : (n : ZMod 5) ≠ 0 := by
    rwa [ne_eq, ZMod.natCast_eq_zero_iff]
  have hz' : ((n : ℤ) : ZMod 5) ≠ 0 := by exact_mod_cast hz
  exact legendreSym.eq_one_or_neg_one (p := 5) hz'

private lemma five_not_dvd_of_chi_neg {n : ℕ} (hn : chi n = -1) : ¬5 ∣ n := by
  intro hd
  have hz : (n : ZMod 5) = 0 := (ZMod.natCast_eq_zero_iff n 5).mpr hd
  have hc : chi n = 0 := by
    change legendreSym 5 (n : ℤ) = 0
    apply (legendreSym.eq_zero_iff 5 (n : ℤ)).mpr
    exact_mod_cast hz
  omega

private lemma sign_product {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (P : ι → Prop) [DecidablePred P] :
    (∏ i ∈ s, if P i then (-1 : ℤ) else 1) = (-1 : ℤ) ^ (s.filter P).card := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    by_cases hp : P a
    · have hnot : a ∉ s.filter P := fun h => ha (mem_filter.mp h).1
      simp [ha, hp, ih, hnot, pow_succ, mul_comm]
    · simp [ha, hp, ih]

/-- A factorization-level equality, counting distinct odd-depth inert prime divisors.
It keeps every actual valuation; no squarefree or non-WSS assumption occurs. -/
theorem character_eq_odd_inert_sign (N : ℕ) (hN : N ≠ 0) (h5 : ¬5 ∣ N) :
    chi N = (-1 : ℤ) ^ (oddInertFactors N).card := by
  classical
  have hfac : (∏ p ∈ N.primeFactors, p ^ N.factorization p) = N :=
    Nat.prod_factorization_pow_eq_self hN
  have hprod : chi N = ∏ p ∈ N.primeFactors, chi p ^ N.factorization p := by
    calc
      chi N = chiHom (∏ p ∈ N.primeFactors, p ^ N.factorization p) :=
        congrArg chi hfac.symm
      _ = ∏ p ∈ N.primeFactors, chi p ^ N.factorization p := by
        simp only [map_prod, map_pow, chiHom]
  rw [hprod]
  have hpowers : ∀ p ∈ N.primeFactors,
      chi p ^ N.factorization p =
        if chi p = -1 ∧ Odd (N.factorization p) then (-1 : ℤ) else 1 := by
    intro p hp
    have hp5 : ¬5 ∣ p := fun hd => h5 (hd.trans (Nat.dvd_of_mem_primeFactors hp))
    rcases chi_cases p hp5 with hc | hc
    · simp [hc]
    · rw [hc]
      rcases Nat.even_or_odd (N.factorization p) with he | ho
      · have hnot : ¬Odd (N.factorization p) := Nat.not_odd_iff_even.mpr he
        simp [hnot, he.neg_one_pow]
      · simp [ho, ho.neg_one_pow]
  calc
    (∏ p ∈ N.primeFactors, chi p ^ N.factorization p) =
        ∏ p ∈ N.primeFactors,
          if chi p = -1 ∧ Odd (N.factorization p) then (-1 : ℤ) else 1 :=
      prod_congr rfl hpowers
    _ = (-1 : ℤ) ^ (oddInertFactors N).card :=
      sign_product N.primeFactors (fun p => chi p = -1 ∧ Odd (N.factorization p))

/-- The exact equivalence between negative character and an odd number of odd-depth inert factors. -/
theorem odd_inert_count_iff (N : ℕ) (hN : N ≠ 0) (h5 : ¬5 ∣ N) :
    Odd (oddInertFactors N).card ↔ chi N = -1 := by
  rw [character_eq_odd_inert_sign N hN h5]
  exact (neg_one_pow_eq_neg_one_iff_odd (by norm_num : (-1 : ℤ) ≠ 1)).symm

/-- The ramified mod-five recurrence at ALL indices; this is not a bounded residue scan. -/
theorem fibonacci_mod_five (n : ℕ) :
    (Nat.fib (n + 1) : ZMod 5) = ((n + 1 : ℕ) : ZMod 5) * 3 ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num
  | one => norm_num [Nat.fib_add_two]
  | more n h0 h1 =>
    rw [show n + 2 + 1 = (n + 1) + 2 by omega, Nat.fib_add_two, Nat.cast_add,
      h0, h1]
    push_cast
    simp only [pow_succ]
    ring_nf <;> norm_num

/-- Odd index preserves the quadratic character, including zero character at multiples of five. -/
theorem odd_index_character (n : ℕ) (hn : Odd n) : chi (Nat.fib n) = chi n := by
  obtain ⟨r, rfl⟩ := hn
  have hf : (Nat.fib (2 * r + 1) : ZMod 5) =
      (((2 * r + 1) * 3 ^ (2 * r) : ℕ) : ZMod 5) := by
    simpa only [Nat.cast_mul, Nat.cast_pow] using fibonacci_mod_five (2 * r)
  rw [chi_congr hf, chi_mul, chi_pow, pow_mul]
  have hsq : chi 3 ^ 2 = 1 := by
    rcases chi_cases 3 (by norm_num) with h | h <;> norm_num [h]
  rw [hsq, one_pow, mul_one]

/-- Every consecutive power layer of an odd inert base has negative character.
Primality is not required for this character equality; exact-rank assertions are separate. -/
theorem power_block_character (ell k : ℕ) (hodd : Odd ell) (hinert : chi ell = -1) :
    chi (powerBlock ell k) = -1 := by
  have hdvd : Nat.fib (ell ^ k) ∣ Nat.fib (ell ^ (k + 1)) := by
    apply Nat.fib_dvd
    exact ⟨ell, by rw [pow_succ]⟩
  have hmul : Nat.fib (ell ^ k) * powerBlock ell k = Nat.fib (ell ^ (k + 1)) :=
    Nat.mul_div_cancel' hdvd
  have hh := congrArg chi hmul
  rw [chi_mul, odd_index_character _ hodd.pow, odd_index_character _ hodd.pow,
    chi_pow, chi_pow, hinert, pow_succ] at hh
  exact mul_left_cancel₀ (pow_ne_zero k (by norm_num : (-1 : ℤ) ≠ 0)) hh

/-- Negative character forces an odd cardinality, so each actual layer supplies a witness. -/
theorem power_block_odd_inert_count (ell k : ℕ)
    (hodd : Odd ell) (hinert : chi ell = -1) :
    Odd (oddInertFactors (powerBlock ell k)).card := by
  have hneg := power_block_character ell k hodd hinert
  have hB : powerBlock ell k ≠ 0 := by
    intro hz
    rw [hz, chi_zero] at hneg
    norm_num at hneg
  exact (odd_inert_count_iff _ hB (five_not_dvd_of_chi_neg hneg)).mpr hneg

/-- An explicitly quantified prime witness with its actual odd exponent in the quotient. -/
theorem power_block_inert_witness (ell k : ℕ)
    (hodd : Odd ell) (hinert : chi ell = -1) :
    ∃ p : ℕ, p.Prime ∧ p ∣ powerBlock ell k ∧ chi p = -1 ∧
      Odd ((powerBlock ell k).factorization p) := by
  classical
  have ho := power_block_odd_inert_count ell k hodd hinert
  have hcard : 0 < (oddInertFactors (powerBlock ell k)).card := by
    obtain ⟨r, hr⟩ := ho
    omega
  obtain ⟨p, hp⟩ := card_pos.mp hcard
  have hh := mem_filter.mp hp
  exact ⟨p, Nat.prime_of_mem_primeFactors hh.1, Nat.dvd_of_mem_primeFactors hh.1,
    hh.2.1, hh.2.2⟩

end D5.S3.Arith.Congruence.GoldenInertBlockParity
