/- GID: D5/S3/Arith/Primes/FibonacciOddIndexNonsquare
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/FibonacciOddIndexNonsquare
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Lucas moduli exclude squares at every odd Fibonacci index at least three. -/

import D5.S1.Scale.LucasDoubling
import D5.S3.Arith.GoldenApparition
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Primes.FibonacciOddIndexNonsquare

open D5.S0.Carrier D5.S1.Scale
open D5.S3.Arith.GoldenApparition
set_option maxHeartbeats 800000 in
/-- Every odd Fibonacci index at least three has a dynamic Lucas modulus
with residue minus one and hence cannot be a square. -/
theorem fibonacci_odd_index_nonsquare (m : ℕ) (hm : 3 ≤ m) (hmodd : Odd m) :
    ¬ IsSquare (Nat.fib m) := by
  have hLmod (r : ℕ) : (goldenLucas (2 ^ (r + 1)) : ZMod 4) = 3 := by
    induction r with
    | zero => change (goldenLucas 2 : ZMod 4) = 3; decide
    | succ r ih =>
      have he : Even (2 ^ (r + 1)) := (Nat.even_pow).2 ⟨by decide, by omega⟩
      have hi : 2 ^ (r + 1 + 1) = 2 * 2 ^ (r + 1) := by ring
      rw [hi, golden_lucas_two_mul, he.neg_one_pow]
      push_cast
      rw [ih]
      decide
  have hsplit : ∃ t : ℕ, 0 < t ∧ (m = 4 * t + 1 ∨ m + 1 = 4 * t) := by
    have ho : m % 2 = 1 := Nat.odd_iff.mp hmodd
    by_cases h4 : m % 4 = 1
    · refine ⟨m / 4, ?_, Or.inl ?_⟩ <;> omega
    · refine ⟨(m + 1) / 4, ?_, Or.inr ?_⟩ <;> omega
  obtain ⟨t, ht, hindex⟩ := hsplit
  obtain ⟨r, s, hsodd, hts⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.ne_of_gt ht)
  let n : ℕ := 2 ^ r
  have hn : 0 < n := pow_pos (by decide) r
  let L : ℤ := goldenLucas (2 * n)
  have hLpos : 0 < L := by
    have hidx : 2 * n = (2 * n - 1) + 1 := by omega
    change 0 < goldenLucas (2 * n)
    rw [hidx, golden_lucas_succ_eq_fib_add_fib]
    have hpos : 0 < Nat.fib (2 * n - 1 + 2) := Nat.fib_pos.mpr (by omega)
    positivity
  let b : ℕ := L.toNat
  have hbcast : (b : ℤ) = L := Int.toNat_of_nonneg (le_of_lt hLpos)
  have hb4 : b % 4 = 3 := by
    have hi : 2 * n = 2 ^ (r + 1) := by dsimp [n]; ring
    have hz : ((b : ℕ) : ZMod 4) = 3 := by
      calc
        (b : ZMod 4) = (L : ZMod 4) := by rw [← hbcast]; simp
        _ = 3 := by dsimp [L]; rw [hi]; exact hLmod r
    exact (ZMod.natCast_eq_natCast_iff' b 3 4).mp hz
  have hLzero : (L : ZMod b) = 0 := by
    rw [← hbcast]
    simp
  have hchar : (phi ^ (2 * n)) ^ 2 + 1 = (L : GoldenInt) * phi ^ (2 * n) := by
    have hnorm : norm (phi ^ (2 * n)) = 1 := by
      rw [norm_phi_pow]
      exact (even_two_mul n).neg_one_pow
    have hnormGI : phi ^ (2 * n) * conj (phi ^ (2 * n)) = 1 := by
      rw [← norm_eq_mul_conj, hnorm]
      norm_num
    calc
      (phi ^ (2 * n)) ^ 2 + 1 =
          (phi ^ (2 * n) + conj (phi ^ (2 * n))) * phi ^ (2 * n) := by
            rw [pow_two]
            linear_combination -hnormGI
      _ = (L : GoldenInt) * phi ^ (2 * n) := by
        rw [add_conj_eq_trace]
        rfl
  let f := GoldenMod.reduce b
  let y : GoldenMod b := f phi
  have hanti : y ^ (4 * n) = -1 := by
    have h := congrArg f hchar
    have hscalar : f (L : GoldenInt) = 0 := by
      ext <;> simp [f, GoldenMod.reduce, hLzero]
    simp only [map_add, map_pow, map_one, map_mul, hscalar, zero_mul] at h
    have hi : 4 * n = (2 * n) * 2 := by omega
    rw [hi, pow_mul]
    dsimp [y]
    linear_combination h
  have hoddanti : y ^ (4 * n * s) = -1 := by
    rw [pow_mul, hanti, hsodd.neg_one_pow]
  have hy : y = GoldenMod.phi := by
    ext <;> simp [y, f, GoldenMod.phi]
  have hcoord : (Nat.fib m : ZMod b) = -1 := by
    rcases hindex with hi | hi
    · have him : m = 4 * n * s + 1 := by rw [hts] at hi; simpa only [n, mul_assoc] using hi
      have hp : y ^ m = -y := by rw [him, pow_add, hoddanti]; simp
      have hc := congrArg GoldenMod.b hp
      have hmap : (y ^ m).b = (Nat.fib m : ZMod b) := by
        change ((f phi) ^ m).b = _
        rw [← map_pow]
        change ((phi ^ m).b : ZMod b) = _
        rw [golden_phi_pow_b_eq_fib_index]
        simp
      rw [hmap, GoldenMod.b_neg, hy] at hc
      exact hc
    · have him : m + 1 = 4 * n * s := by rw [hts] at hi; simpa only [n, mul_assoc] using hi
      have hp : y ^ m * y = -1 := by rw [← pow_succ, him]; exact hoddanti
      have hc := congrArg GoldenMod.a hp
      have hya : y.a = 0 := by rw [hy]; rfl
      have hyb : y.b = 1 := by rw [hy]; rfl
      simp only [GoldenMod.a_mul, hya, hyb, mul_zero, mul_one,
        zero_add, GoldenMod.a_neg, GoldenMod.a_one] at hc
      have hmap : (y ^ m).b = (Nat.fib m : ZMod b) := by
        change ((f phi) ^ m).b = _
        rw [← map_pow]
        change ((phi ^ m).b : ZMod b) = _
        rw [golden_phi_pow_b_eq_fib_index]
        simp
      rw [hmap] at hc
      exact hc
  have hbodd : Odd b := Nat.odd_iff.mpr (by omega)
  have hj : jacobiSym (-1) b = -1 := by
    rw [jacobiSym.at_neg_one hbodd, ZMod.χ₄_nat_three_mod_four hb4]
  have hbad := ZMod.nonsquare_of_jacobiSym_eq_neg_one hj
  intro hsquare
  have hsq := hsquare.map (Nat.castRingHom (ZMod b))
  change IsSquare (Nat.fib m : ZMod b) at hsq
  rw [hcoord] at hsq
  exact hbad (by simpa using hsq)

#print axioms fibonacci_odd_index_nonsquare

end D5.S3.Arith.Primes.FibonacciOddIndexNonsquare
