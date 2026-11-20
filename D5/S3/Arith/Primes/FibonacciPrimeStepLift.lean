/- GID: D5/S3/Arith/Primes/FibonacciPrimeStepLift
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/FibonacciPrimeStepLift
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Multiplication of a Fibonacci zero index by an odd prime increases its valuation exactly once. -/

import D5.S0.Carrier.Ring
import D5.S1.Scale.Lucas
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Arith.Primes.FibonacciPrimeStepLift

open Finset D5.S0.Carrier D5.S1.Scale

/-- The first-order binomial expansion at an odd prime retains an extra
factor of the prime throughout the quadratic remainder. -/
theorem prime_first_order {R : Type*} [CommRing R] (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p)
    (a b z : R) (hb : (p:R) ∣ b) :
    ∃ c : R, (a+b*z)^p = a^p + (p:R)*a^(p-1)*b*z + (p:R)*b^2*c := by
  let f (i : ℕ) := (b*z)^i * a^(p-i) * (p.choose i : R)
  have hsum : (a+b*z)^p = f 0 + f 1 + ∑ i ∈ range (p-1), f (i+2) := by
    calc
      (a+b*z)^p = ∑ i ∈ range (p+1), f i := by rw [add_comm, add_pow]
      _ = _ := by
        rw [show p+1 = ((p-1)+1)+1 by omega, sum_range_succ', sum_range_succ']
        ring
  have hd : (p:R)*b^2 ∣ ∑ i ∈ range (p-1), f (i+2) := by
    apply Finset.dvd_sum
    intro i hi
    have hi' := Finset.mem_range.mp hi
    let j := i+2
    have hj2 : 2 ≤ j := by omega
    have hjp : j ≤ p := by dsimp [j]; omega
    have hb' : b^j = b^2*b^(j-2) := by rw [← pow_add, show 2+(j-2)=j by omega]
    change (p:R)*b^2 ∣ f j
    by_cases hj : j=p
    · have hbpow : (p:R) ∣ b^(j-2) :=
        hb.trans (dvd_pow_self b (by omega))
      obtain ⟨d,hd⟩ := hbpow
      refine ⟨d*z^j*a^(p-j)*(p.choose j : R), ?_⟩
      dsimp [f]
      rw [mul_pow, hb', hd]
      ring
    · obtain ⟨d,hd⟩ := hp.dvd_choose_self (show j≠0 by omega) (by omega : j<p)
      refine ⟨b^(j-2)*z^j*a^(p-j)*(d:R), ?_⟩
      dsimp [f]
      rw [mul_pow, hb', hd, Nat.cast_mul]
      ring
  obtain ⟨c,hc⟩ := hd
  refine ⟨c, ?_⟩
  rw [hsum, hc]
  simp only [f, pow_zero, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, one_mul,
    pow_one, Nat.choose_one_right]
  ring

private theorem goldenInt_scalar_a (a : ℤ) (m : ℕ) :
    ((a : GoldenInt)^m).a = a^m := by rw [← Int.cast_pow]; rfl

private theorem goldenInt_scalar_b (a : ℤ) (m : ℕ) :
    ((a : GoldenInt)^m).b = 0 := by rw [← Int.cast_pow]; rfl

theorem goldenInt_prime_power_valuation (x : GoldenInt) (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p)
    (hb0 : x.b ≠ 0) (hb : (p:ℤ) ∣ x.b) (ha : ¬(p:ℤ) ∣ x.a) :
    padicValInt p (x^p).b = 1 + padicValInt p x.b := by
  have hx : x = (x.a : GoldenInt)+(x.b : GoldenInt)*phi := by
    ext <;> simp [phi]
  have H : (p:GoldenInt) ∣ (x.b:GoldenInt) := by
    obtain ⟨u,hu⟩ := hb
    refine ⟨(u:GoldenInt), ?_⟩
    rw [hu, Int.cast_mul, Int.cast_natCast]
  obtain ⟨c,hc⟩ := prime_first_order p hp hp3 (x.a:GoldenInt) (x.b:GoldenInt) phi H
  have hd := congrArg GoldenInt.b ((congrArg (·^p) hx).trans hc)
  have he : (x^p).b = (p:ℤ)*x.b*(x.a^(p-1)+x.b*c.b) := by
    simpa only [] using (calc
      (x^p).b = _ := hd
      _ = _ := by
        simp only [b_add, b_mul, goldenInt_scalar_a, goldenInt_scalar_b, a_natCast, b_natCast,
          a_intCast, b_intCast, phi]
        simp [goldenInt_scalar_a]
        ring)
  have : Fact p.Prime := ⟨hp⟩
  have hbZ : (x.b : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hb
  have haZ : (x.a : ZMod p) ≠ 0 := fun H => ha ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp H)
  let q := x.a^(p-1)+x.b*c.b
  have hq : ¬(p:ℤ) ∣ q := by
    intro H
    have H' := (ZMod.intCast_zmod_eq_zero_iff_dvd q p).mpr H
    dsimp [q] at H'
    rw [Int.cast_add, Int.cast_mul, Int.cast_pow, hbZ, zero_mul, add_zero] at H'
    exact (pow_ne_zero _ haZ) H'
  have hq0 : q ≠ 0 := fun H => hq (H ▸ dvd_zero _)
  have hp0 : (p:ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [he, padicValInt.mul (mul_ne_zero hp0 hb0) hq0, padicValInt.mul hp0 hb0,
    padicValInt.eq_zero_of_not_dvd hq, add_zero, padicValInt.self hp.one_lt]

/-- An odd prime appearing in a native Fibonacci number gains exactly one
valuation digit when the index is multiplied by that prime. -/
theorem fibonacci_valuation_prime_step (p r : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hr : 0 < r) (hb : p ∣ Nat.fib r) :
    padicValNat p (Nat.fib (p*r)) = 1 + padicValNat p (Nat.fib r) := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  have hA : (phi^(k+1)).a = (Nat.fib k : ℤ) := by
    simpa using congrArg GoldenInt.a (golden_phi_pow_eq_fib_pair k)
  have hB : (phi^(k+1)).b = (Nat.fib (k+1) : ℤ) :=
    golden_phi_pow_b_eq_fib_index (k+1)
  have hB0 : (phi^(k+1)).b ≠ 0 := by rw [hB]; exact_mod_cast (Nat.fib_pos.mpr (by omega : 0<k+1)).ne'
  have hBD : (p:ℤ) ∣ (phi^(k+1)).b := by rw [hB]; exact_mod_cast hb
  have hAD : ¬(p:ℤ) ∣ (phi^(k+1)).a := by
    rw [hA]
    intro H
    have hd : p ∣ Nat.fib k := by exact_mod_cast H
    have hg := Nat.dvd_gcd hd hb
    have ho : p ∣ 1 := by simpa [Nat.fib_coprime_fib_succ k] using hg
    exact hp.ne_one (Nat.dvd_one.mp ho)
  have h := goldenInt_prime_power_valuation (phi^(k+1)) p hp hp3 hB0 hBD hAD
  rw [← pow_mul, hB, golden_phi_pow_b_eq_fib_index, padicValInt.of_nat, padicValInt.of_nat] at h
  simpa [Nat.mul_comm] using h

end D5.S3.Arith.Primes.FibonacciPrimeStepLift
