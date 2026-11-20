/- GID: D5/S3/Arith/Primes/GoldenCubicBlockFibonacciLagProduct
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/GoldenCubicBlockFibonacciLagProduct
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: An exact integral sum-and-difference Fibonacci factorization of every cubic Lucas block lag. -/

import D5.S1.Scale.GoldenCubicBlockCongruences

set_option autoImplicit false

namespace D5.S3.Arith.Primes.GoldenCubicBlockFibonacciLagProduct

open D5.S0.Carrier D5.S1.Scale

/-- A trace-square polarization in the integral golden coordinates.
No choice of an algebraic or p-adic root is needed. -/
theorem trace_sq_sub_norm_mul_trace_sq (x y : GoldenInt) :
    trace (x*y)^2 - norm y * trace x^2 = 5*(x*x*y).b*y.b := by
  simp [trace, norm]
  ring

/-- The Fibonacci lag product for arbitrary indices, with the sign for an
odd difference kept explicit. It also applies when both indices agree. -/
theorem lucas_sq_sub_signed_sq (n m : ℕ) (hmn : m ≤ n) :
    goldenLucas n^2 - (-1:ℤ)^(n-m) * goldenLucas m^2 =
      5*(Nat.fib (n+m):ℤ)*(Nat.fib (n-m):ℤ) := by
  have h₁ : phi^m * phi^(n-m) = phi^n := by
    rw [← pow_add, Nat.add_sub_of_le hmn]
  have h₂ : phi^m * phi^m * phi^(n-m) = phi^(n+m) := by
    rw [mul_assoc, h₁, ← pow_add, Nat.add_comm m n]
  have h := trace_sq_sub_norm_mul_trace_sq (phi^m) (phi^(n-m))
  rw [h₁, h₂, norm_phi_pow, golden_phi_pow_b_eq_fib_index, golden_phi_pow_b_eq_fib_index] at h
  exact h

/-- The same parity makes the sign trivial. -/
theorem lucas_sq_sub_sq_of_even_difference (n m : ℕ) (hmn : m ≤ n) (he : Even (n-m)) :
    goldenLucas n^2 - goldenLucas m^2 =
      5*(Nat.fib (n+m):ℤ)*(Nat.fib (n-m):ℤ) := by
  have h := lucas_sq_sub_signed_sq n m hmn
  simpa only [he.neg_one_pow, one_mul] using h

/-- Every native cubic block difference factors into the two Fibonacci terms
at the sum and difference of the original indices, times five. -/
theorem cubic_block_fibonacci_lag_product (n m : ℕ) (hmn : m ≤ n) :
    (goldenLucas (3^n)^2+3)-(goldenLucas (3^m)^2+3) =
      5*(Nat.fib (3^n+3^m):ℤ)*(Nat.fib (3^n-3^m):ℤ) := by
  have hpow : (3:ℕ)^m ≤ 3^n := Nat.pow_le_pow_right (by decide) hmn
  have hn : Odd ((3:ℕ)^n) := (by decide : Odd (3:ℕ)).pow
  have hm : Odd ((3:ℕ)^m) := (by decide : Odd (3:ℕ)).pow
  have he : Even ((3:ℕ)^n-3^m) := by
    obtain ⟨a,ha⟩ := hn
    obtain ⟨b,hb⟩ := hm
    exact ⟨a-b, by omega⟩
  calc
    _ = goldenLucas (3^n)^2-goldenLucas (3^m)^2 := by ring
    _ = _ := lucas_sq_sub_sq_of_even_difference _ _ hpow he

end D5.S3.Arith.Primes.GoldenCubicBlockFibonacciLagProduct
