/- GID: D5/S3/Arith/Primes/FibonacciPrimeToIndexValuation
   generality: G
   mirror-B: D5/B/S3/Arith/Primes/FibonacciPrimeToIndexValuation
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Prime-to-index Fibonacci valuations equal their original entry-rank depths. -/

import Mathlib
import D5.S0.Carrier.Ring
import D5.S1.Scale.Lucas
import D5.S3.Arith.Primes.FiniteFibonacciRankClosure

namespace D5.S3.Arith.Primes.FibonacciPrimeToIndexValuation

open D5.S0.Carrier
open D5.S3.Arith.Primes.FiniteFibonacciRankClosure

private def powerQuotient (x : GoldenInt) : ℕ → ℤ :=
  Nat.rec 0 (fun m q => (x ^ m).a + q * (x.a + x.b))

private theorem powerQuotient_spec (x : GoldenInt) (p : ℕ)
    (hb : (p : ℤ) ∣ x.b) (m : ℕ) :
    (x ^ m).b = x.b * powerQuotient x m ∧
    ((x ^ m).a : ZMod p) = (x.a : ZMod p) ^ m ∧
    ((powerQuotient x (m + 1) : ℤ) : ZMod p) =
      ((m + 1 : ℕ) : ZMod p) * (x.a : ZMod p) ^ m := by
  have hb0 : (x.b : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd x.b p).2 hb
  induction m with
  | zero =>
      simp [powerQuotient]
  | succ m ih =>
      rcases ih with ⟨ihb, iha, ihq⟩
      have hbnext : (x ^ (m + 1)).b =
          x.b * powerQuotient x (m + 1) := by
        rw [pow_succ]
        change (x ^ m * x).b =
          x.b * ((x ^ m).a + powerQuotient x m * (x.a + x.b))
        simp only [b_mul]
        rw [ihb]
        ring
      have hanext : ((x ^ (m + 1)).a : ZMod p) = (x.a : ZMod p) ^ (m + 1) := by
        rw [pow_succ]
        simp only [a_mul, Int.cast_add, Int.cast_mul]
        rw [hb0, mul_zero, add_zero, iha]
        ring
      refine ⟨hbnext, hanext, ?_⟩
      change (((x ^ (m + 1)).a + powerQuotient x (m + 1) *
        (x.a + x.b) : ℤ) : ZMod p) = _
      simp only [Int.cast_add, Int.cast_mul, hb0, add_zero, hanext, ihq]
      push_cast
      ring

private theorem golden_power_valuation (x : GoldenInt) (p m : ℕ) (hp : p.Prime)
    (hxb : x.b ≠ 0) (hpb : (p : ℤ) ∣ x.b)
    (hpa : ¬(p : ℤ) ∣ x.a) (hpm : ¬p ∣ m) :
    padicValInt p (x ^ m).b = padicValInt p x.b := by
  have : Fact p.Prime := ⟨hp⟩
  have ha0 : (x.a : ZMod p) ≠ 0 := by
    intro h
    exact hpa ((ZMod.intCast_zmod_eq_zero_iff_dvd x.a p).mp h)
  have hm0 : (m : ZMod p) ≠ 0 := by
    intro h
    exact hpm ((ZMod.natCast_eq_zero_iff m p).mp h)
  cases m with
  | zero => exact (hpm (dvd_zero p)).elim
  | succ k =>
      have hspec := powerQuotient_spec x p hpb k
      have hq0 : (powerQuotient x (k + 1) : ZMod p) ≠ 0 := by
        rw [hspec.2.2]
        exact mul_ne_zero hm0 (pow_ne_zero k ha0)
      have hqnot : ¬(p : ℤ) ∣ powerQuotient x (k + 1) := by
        intro h
        exact hq0 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h)
      have hqne : powerQuotient x (k + 1) ≠ 0 := by
        intro h
        exact hqnot (h ▸ dvd_zero _)
      have hbpow := (powerQuotient_spec x p hpb (k + 1)).1
      rw [hbpow, padicValInt.mul hxb hqne,
        padicValInt.eq_zero_of_not_dvd hqnot, add_zero]

private theorem fibonacci_valuation_stable (p r m : ℕ) (hp : p.Prime)
    (hr : 0 < r) (hpb : p ∣ Nat.fib r) (hpm : ¬p ∣ m) :
    padicValNat p (Nat.fib (r * m)) = padicValNat p (Nat.fib r) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  have hA : (phi ^ (k + 1)).a = (Nat.fib k : ℤ) := by
    simpa using congrArg GoldenInt.a (D5.S1.Scale.golden_phi_pow_eq_fib_pair k)
  have hB : (phi ^ (k + 1)).b = (Nat.fib (k + 1) : ℤ) :=
    D5.S1.Scale.golden_phi_pow_b_eq_fib_index (k + 1)
  have hBNZ : (phi ^ (k + 1)).b ≠ 0 := by
    rw [hB]
    exact_mod_cast (Nat.fib_pos.mpr (by omega : 0 < k + 1)).ne'
  have hBDiv : (p : ℤ) ∣ (phi ^ (k + 1)).b := by
    rw [hB]
    exact_mod_cast hpb
  have hADiv : ¬(p : ℤ) ∣ (phi ^ (k + 1)).a := by
    rw [hA]
    intro h
    have hNat : p ∣ Nat.fib k := by exact_mod_cast h
    have hOne : p ∣ 1 := by
      have hBoth : p ∣ Nat.gcd (Nat.fib k) (Nat.fib (k + 1)) :=
        Nat.dvd_gcd hNat hpb
      simpa [Nat.fib_coprime_fib_succ k] using hBoth
    exact hp.ne_one (Nat.dvd_one.mp hOne)
  have hval := golden_power_valuation (phi ^ (k + 1)) p m hp hBNZ hBDiv hADiv hpm
  rw [← pow_mul, hB] at hval
  simpa only [D5.S1.Scale.golden_phi_pow_b_eq_fib_index,
    padicValInt.of_nat] using hval

/-- A prime dividing `F_n` but not its index retains its first-entry
valuation. The proof factors the golden-power Fibonacci coordinate and
computes the residual quotient modulo the prime. -/
theorem fibonacci_original_rank_valuation (p n : ℕ) (hp : p.Prime)
    (hpn : p ∣ Nat.fib n) (hpIndex : ¬p ∣ n) :
    padicValNat p (Nat.fib n) = padicValNat p (Nat.fib (fibonacciRank p)) := by
  let r := rankWitness p hp
  have hrpos : 0 < r.val := r.property.1
  have hrzero : p ∣ Nat.fib r.val := r.property.2.1
  have hrmin : ∀ j, 0 < j → p ∣ Nat.fib j → r.val ≤ j := r.property.2.2
  have hrdiv : r.val ∣ n :=
    (D5.S3.Arith.FibonacciRank.fibonacci_entry_point hrpos hrzero hrmin).mp hpn
  obtain ⟨m, hm⟩ := hrdiv
  have hpm : ¬p ∣ m := by
    intro h
    apply hpIndex
    rw [hm]
    exact dvd_mul_of_dvd_right h _
  have hval := fibonacci_valuation_stable p r.val m hp hrpos hrzero hpm
  rw [hm]
  simpa [fibonacciRank, hp, r] using hval

#print axioms fibonacci_original_rank_valuation

end D5.S3.Arith.Primes.FibonacciPrimeToIndexValuation
