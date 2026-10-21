/- GID: D5/S3/Arith/Primes/OeisA347285PrimePowerDescent
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/OeisA347285PrimePowerDescent
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Prime-power exponent rows end at one and their absolute differences telescope. -/

/-
proof_shape: result = bind-only.
escape_witness: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19840.
admission_basis: open-problem-resolution (#18689; Proved).
The one-based prime enumeration uses the existing prime definition, exactly
Nat.nth Nat.Prime (k - 1), without a second declaration for this expression.

Direct frozen dependencies (declaration statement_id, not module pins):
  P: D5/S1/Recurrence/Parity/PrimePowerShiftLogDerivative.prime
     sha256:0a736efbf5ea49c36d6d348f1d3d21b17714ff433baaef1d2acb118a193af86b
  G: D5/S3/Arith/Primes/PrimeGap.primeGap
     sha256:883f3d2ce5b9b290eaa82a1a32f3ac3d9251cec83b8ec2e18e474c9a4f26c53b
  H: D5/S3/Arith/Primes/PrimeGap.primeGap_pos
     sha256:8b3b27a5fe11fef6a469b991ca1f3fc450703892b6a160158ee58c8f12191116
Per-declaration dependency sets inline all same-module declarations:
  e: source definition; dependencies: P; consumers: len, S, e_succ_log, e_drop,
     e_step_le, e_zero_exists, len_spec, last_eq_one, sum_abs_telescope.
  len: source definition; dependencies: P; consumers: S, len_spec, last_eq_one, result.
  S: source definition; dependencies: P; consumers: claim, result.
  claim: source definition; dependencies: P; consumers: result.
  p_prime: proof_shape: bind-only; dependencies: P; consumers: e_drop, p_next_le_square, last_eq_one.
  p_lt: proof_shape: bind-only; dependencies: P, G, H; consumers: e_drop.
  e_succ_log: proof_shape: bind-only; dependencies: P; consumers: e_drop, e_step_le, last_eq_one.
  e_drop: proof_shape: bind-only; dependencies: P, G, H; consumers: e_step_le, e_zero_exists.
  e_step_le: proof_shape: bind-only; dependencies: P, G, H; consumers: sum_abs_telescope.
  e_zero_exists: proof_shape: bind-only; dependencies: P, G, H; consumers: len_spec.
  len_spec: proof_shape: bind-only; dependencies: P, G, H; consumers: last_eq_one.
  p_next_le_square: proof_shape: bind-only; dependencies: P; consumers: last_eq_one.
  last_eq_one: proof_shape: bind-only; dependencies: P, G, H; consumers: result.
  sum_abs_telescope: proof_shape: bind-only; dependencies: P, G, H; consumers: result.
  result: proof_shape: bind-only; dependencies: P, G, H; consumers: none.
Utility is none: every proof is symbolic over arbitrary natural indices; no finite
certificate, certified instance, bounded enumeration, checker or numeric reduction occurs.
-/

import D5.S1.Recurrence.Parity.PrimePowerShiftLogDerivative
import D5.S3.Arith.Primes.PrimeGap
import Mathlib.Data.Int.NatAbs
import Mathlib.NumberTheory.Bertrand
import Mathlib.Analysis.SpecialFunctions.Log.Base

set_option autoImplicit false

namespace D5.S3.Arith.Primes.OeisA347285PrimePowerDescent

open D5.S1.Recurrence.Parity.PrimePowerShiftLogDerivative (prime)

/-- The terms of row `n`, indexed from `0`: `e n 0 = T(n,1) = n` and
`e n (j+1) = T(n,j+2) = floor(log_{p_(j+2)}(p_(j+1)^e n j))`. -/
noncomputable def e (n : ℕ) : ℕ → ℕ
  | 0 => n
  | j + 1 => ⌊Real.logb (prime (j + 2)) ((prime (j + 1) : ℝ) ^ e n j)⌋₊

open Classical in
/-- The length of row `n`: the row keeps the terms `e_k > 0`, so it ends before the first index with
`e n j = 0` (`0` if there is none). -/
noncomputable def len (n : ℕ) : ℕ := if h : ∃ j, e n j = 0 then Nat.find h else 0

/-- `S`: the sum of the absolute values of the first differences of the terms in row `n`. -/
noncomputable def S (n : ℕ) : ℕ := ∑ i ∈ Finset.range (len n - 1), ((e n (i + 1) : ℤ) - e n i).natAbs

/-- A347285 ("Conjecture: let S be the sum of the absolute values of the first differences of terms in
row n. For all n > 0, n - S = 1."). -/
def claim : Prop := ∀ n : ℕ, 0 < n → (n : ℤ) - S n = 1

private theorem p_prime (j : ℕ) : Nat.Prime (prime (j + 1)) := by
  simpa only [prime, Nat.add_sub_cancel] using
    Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime j

private theorem p_lt (j : ℕ) : prime (j + 1) < prime (j + 2) := by
  have h := D5.S3.Arith.Primes.PrimeGap.primeGap_pos j
  simpa only [D5.S3.Arith.Primes.PrimeGap.primeGap, Nat.sub_pos_iff_lt,
    prime, Nat.add_sub_cancel, show j + 2 - 1 = j + 1 from Nat.add_succ_sub_one j 1] using h

private theorem e_succ_log (n j : ℕ) :
    e n (j + 1) = Nat.log (prime (j + 2)) (prime (j + 1) ^ e n j) := by
  rw [e, ← Nat.cast_pow, Real.natFloor_logb_natCast]

private theorem e_drop (n j : ℕ) (h : 0 < e n j) : e n (j + 1) < e n j := by
  rw [e_succ_log]
  apply Nat.log_lt_of_lt_pow (pow_ne_zero _ (p_prime j).ne_zero)
  exact Nat.pow_lt_pow_left (p_lt j) (Nat.ne_zero_of_lt h)

private theorem e_step_le (n j : ℕ) : e n (j + 1) ≤ e n j := by
  by_cases h : 0 < e n j
  · exact (e_drop n j h).le
  · have hz : e n j = 0 := Nat.eq_zero_of_not_pos h
    simp [e_succ_log, hz]

private theorem e_zero_exists (n : ℕ) : ∃ j, e n j = 0 := by
  by_contra h
  push Not at h
  exact not_strictAnti_of_wellFoundedLT (e n)
    (strictAnti_nat_of_succ_lt (fun j => e_drop n j (Nat.pos_of_ne_zero (h j))))

private theorem len_spec (n : ℕ) :
    e n (len n) = 0 ∧ ∀ j < len n, 0 < e n j := by
  classical
  have h := e_zero_exists n
  simp only [len, dite_eq_left h]
  exact ⟨Nat.find_spec h, fun j hj => Nat.pos_of_ne_zero (Nat.find_min h hj)⟩

private theorem p_next_le_square (j : ℕ) : prime (j + 2) ≤ prime (j + 1) ^ 2 := by
  obtain ⟨q, hq, hpq, hqle⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (prime (j + 1)) (p_prime j).ne_zero
  have hnext : prime (j + 2) ≤ q := by
    change Nat.nth Nat.Prime (j + 2 - 1) ≤ q
    rw [show j + 2 - 1 = j + 1 from Nat.add_succ_sub_one j 1]
    apply (Nat.nth_add_one_le_iff Nat.infinite_setOfPred_prime hq).2
    simpa only [prime, Nat.add_sub_cancel] using hpq
  calc prime (j + 2) ≤ q := hnext
       _ ≤ 2 * prime (j + 1) := hqle
       _ ≤ prime (j + 1) ^ 2 := by
         simpa only [pow_two] using Nat.mul_le_mul_right (prime (j + 1)) (p_prime j).two_le

private theorem last_eq_one (n : ℕ) (hn : 0 < n) : e n (len n - 1) = 1 := by
  have hs := len_spec n
  have hl : 0 < len n := by
    apply Nat.pos_of_ne_zero
    intro hz
    have he := hs.1
    rw [hz, e] at he
    exact Nat.ne_of_gt hn he
  have hpos := hs.2 (len n - 1) (Nat.sub_one_lt_of_lt hl)
  have hz : e n ((len n - 1) + 1) = 0 := by
    simpa only [Nat.sub_add_cancel hl] using hs.1
  have hsmall : prime ((len n - 1) + 1) ^ e n (len n - 1) <
      prime ((len n - 1) + 2) := by
    rw [e_succ_log, Nat.log_eq_zero_iff] at hz
    exact hz.resolve_right (Nat.not_le_of_lt (p_prime ((len n - 1) + 1)).two_le)
  have hnot : ¬ 2 ≤ e n (len n - 1) := by
    intro hh
    have hp := p_next_le_square (len n - 1)
    have hpow : prime ((len n - 1) + 1) ^ 2 ≤
        prime ((len n - 1) + 1) ^ e n (len n - 1) :=
      Nat.pow_le_pow_right (p_prime (len n - 1)).pos hh
    exact Nat.not_le_of_lt hsmall (hp.trans hpow)
  exact Nat.le_antisymm (Nat.le_of_lt_succ (Nat.lt_of_not_ge hnot)) hpos

private theorem sum_abs_telescope (n k : ℕ) :
    (∑ i ∈ Finset.range k, ((e n (i + 1) : ℤ) - e n i).natAbs : ℕ) = n - e n k := by
  have hb : e n k ≤ n := antitone_nat_of_succ_le (e_step_le n) (Nat.zero_le k)
  apply Nat.cast_injective (R := ℤ)
  rw [Nat.cast_sub hb, Nat.cast_sum]
  calc
    (∑ i ∈ Finset.range k, (↑((e n (i + 1) : ℤ) - e n i).natAbs : ℤ)) =
        ∑ i ∈ Finset.range k, ((e n i : ℤ) - e n (i + 1)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Int.natAbs_natCast_sub_natCast_of_le (e_step_le n i),
        Nat.cast_sub (e_step_le n i)]
    _ = (e n 0 : ℤ) - e n k := Finset.sum_range_sub' _ _
    _ = (n : ℤ) - e n k := by rw [e]

theorem result : D5.S3.Arith.Primes.OeisA347285PrimePowerDescent.claim := by
  intro n hn
  have hlast := last_eq_one n hn
  have hsum := sum_abs_telescope n (len n - 1)
  change (n : ℤ) - (S n : ℤ) = 1
  rw [S, hsum, hlast]
  omega

end D5.S3.Arith.Primes.OeisA347285PrimePowerDescent
