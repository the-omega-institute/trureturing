/- GID: D5/S3/ArithSums/SpeziaA320043SquareValuesRefutation
   generality: I
   mirror-B: D5/B/S3/ArithSums/SpeziaA320043SquareValuesRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/ArithSums/SpeziaA320043SquareValuesRefutation.claim; result=D5/S3/ArithSums/SpeziaA320043SquareValuesRefutation.result; claim=D5/S3/ArithSums/SpeziaA320043SquareValuesRefutation.claim
   digest: The prime/Pell row identity supplies a fourth square index for OEIS A320043. -/

/-
admission_basis: open-problem-resolution (#24212; Refuted).
a: proof_shape: bind-only; escape_witness: none;
Direct frozen dependencies: none; consumers: claim, prime_row. Source definition.
claim: proof_shape: bind-only; escape_witness: none;
Direct frozen dependencies: none; consumer: result. Source definition.
prime_row: proof_shape: bind-only; escape_witness: none;
Direct frozen dependencies: none; consumer: prime_pell. Prime coprimality,
Finset.sum_Icc_sub and ring normalization.
prime_pell: proof_shape: bind-only; escape_witness: none;
Direct frozen dependencies: none; consumer: result. Pell rearrangement and
cast injectivity applied to prime_row.
witness_prime: proof_shape: bind-only; escape_witness: none;
Direct frozen dependencies: none; consumer: result. lucas_primality and
closed modular normalization.
result: proof_shape: bind-only; escape_witness: none;
Direct frozen dependencies: none. Apply prime_pell and witness_prime at the
explicit counterexample and normalize the three alternatives.
The public result is the designated refutation result (`basis=refutes`) and is
exempt from four-slot escape registration (CLAUDE.md §3.9).
The definitions are the expressions of #24212, under this file's namespace.
OEIS A320043, revision 43, COMMENTS (unpaginated):
"Conjecture: a(n) is not a perfect square except for n = 1, 6 and 96."
FORMULA: "a(n) = Sum_{k=1..n} (n + 1 - k)^2*k/gcd(n + 1 - k, k)^3."
The source domain is n ≥ 1. For each selected k, both gcd arguments are
positive; their common divisor cubed divides the numerator exactly. Natural
division therefore agrees with the source quotient. The empty sum at n = 0
is outside claim. Minimality and infinitely many square indices remain open.
-/

import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.ReduceModChar

namespace D5.S3.ArithSums.SpeziaA320043SquareValuesRefutation

/-- OEIS A320043, first FORMULA, with its source domain n ≥ 1 enforced in claim. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 n,
    (n + 1 - k) ^ 2 * k / (Nat.gcd (n + 1 - k) k) ^ 3

/-- A320043 COMMENTS: a(n) is not a perfect square except for n = 1, 6 and 96. -/
def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ m : ℕ, a n = m ^ 2 → n = 1 ∨ n = 6 ∨ n = 96


set_option maxHeartbeats 1000000

private theorem prime_row (p : ℕ) (hp : p.Prime) :
    (12 : ℤ) * (a (p - 1) : ℤ) = (p : ℤ) ^ 2 * ((p : ℤ) ^ 2 - 1) := by
  have hp2 := hp.two_le
  have he : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
  have hs : a (p - 1) = ∑ k ∈ Finset.Icc 1 (p - 1), (p - k) ^ 2 * k := by
    unfold a
    rw [he]
    apply Finset.sum_congr rfl
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
    have hcop : Nat.Coprime (p - k) k :=
      (Nat.coprime_sub_self_left (by omega)).mpr
        (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hk1 (by omega)))
    rw [hcop.gcd_eq_one]
    simp
  rw [hs, Nat.cast_sum, Finset.mul_sum]
  let F : ℕ → ℤ := fun k =>
    6 * (p : ℤ) ^ 2 * k * (k - 1) -
    4 * p * k * (k - 1) * (2 * k - 1) + 3 * k ^ 2 * (k - 1) ^ 2
  calc
    (∑ k ∈ Finset.Icc 1 (p - 1), (12 : ℤ) * (((p - k) ^ 2 * k : ℕ) : ℤ)) =
        ∑ k ∈ Finset.Icc 1 (p - 1), (F (k + 1) - F k) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk2 : k ≤ p := (Finset.mem_Icc.mp hk).2.trans (Nat.sub_le p 1)
      simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hk2]
      dsimp [F]
      ring
    _ = F (p - 1 + 1) - F 1 := Finset.sum_Icc_sub (by omega) F
    _ = (p : ℤ) ^ 2 * ((p : ℤ) ^ 2 - 1) := by
      rw [he]
      dsimp [F]
      ring

private theorem prime_pell (p y : ℕ) (hp : p.Prime)
    (hPell : (p : ℤ) ^ 2 - 12 * (y : ℤ) ^ 2 = 1) :
    a (p - 1) = (p * y) ^ 2 := by
  have hr := prime_row p hp
  have he : (a (p - 1) : ℤ) = ((p * y) ^ 2 : ℕ) := by
    push_cast
    have hP : (p : ℤ) ^ 2 - 1 = 12 * (y : ℤ) ^ 2 := sub_eq_iff_comm.mp hPell
    rw [hP] at hr
    nlinarith only [hr]
  exact_mod_cast he

private theorem witness_prime : Nat.Prime 708158977 := by
  apply lucas_primality 708158977 (5 : ZMod 708158977)
  · reduce_mod_char
  · intro q hq hqd
    have hf : 708158977 - 1 = 2 ^ 9 * 3 * 7 ^ 2 * 97 ^ 2 := Nat.add_one_sub_one 708158976
    rw [hf] at hqd
    have hcases : q = 2 ∨ q = 3 ∨ q = 7 ∨ q = 97 := by
      rcases hq.dvd_mul.mp hqd with h | h
      · rcases hq.dvd_mul.mp h with h | h
        · rcases hq.dvd_mul.mp h with h | h
          · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp
              (hq.dvd_of_dvd_pow h))
          · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq
              Nat.prime_three).mp h))
        · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq
            Nat.prime_seven).mp (hq.dvd_of_dvd_pow h))))
      · exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hq
          (Nat.properDivisors_eq_singleton_one_iff_prime.mp rfl)).mp (hq.dvd_of_dvd_pow h))))
    rcases hcases with rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide

/-- An additional square contradicts the three-index exclusion. -/
theorem result : ¬ claim := by
  intro hc
  have hw : a 708158976 = 144767444036350576 ^ 2 :=
    prime_pell 708158977 204427888 witness_prime (Int.sub_eq_iff_eq_add'.mpr rfl)
  have hbad := hc 708158976 (by norm_num) 144767444036350576 hw
  norm_num at hbad


end D5.S3.ArithSums.SpeziaA320043SquareValuesRefutation
