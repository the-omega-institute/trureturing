/- GID: D5/S3/Arith/FibonacciTransportFivePowerArithmetic
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciTransportFivePowerArithmetic
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: The CRT period arithmetic for the 2 times 59 times 5-power family. -/

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace D5.S3.Arith.FibonacciTransportFivePowerArithmetic

private theorem coprime_five_power_twenty_nine (a : ℕ) :
    Nat.Coprime (5 ^ a) 29 := by
  exact (by decide : Nat.Coprime 5 29).pow_left a

private theorem coprime_six_five_power_twenty_nine (a : ℕ) :
    Nat.Coprime (6 * 5 ^ a) 29 := by
  rw [Nat.coprime_mul_iff_left]
  exact ⟨by decide, coprime_five_power_twenty_nine a⟩

private theorem lcm_three_four_five_power (a : ℕ) :
    Nat.lcm 3 (4 * 5 ^ a) = 12 * 5 ^ a := by
  have hpow : Nat.Coprime 3 (5 ^ a) :=
    (by decide : Nat.Coprime 3 5).pow_right a
  have hprod : Nat.Coprime 3 (4 * 5 ^ a) := by
    rw [Nat.coprime_mul_iff_right]
    exact ⟨by decide, hpow⟩
  rw [hprod.lcm_eq_mul]
  ring

/-- The common CRT period in the `2 * 59 * 5^a` family is
`lcm (3) (lcm (4 * 5^a) 58) = 348 * 5^a`.

This is the arithmetic CRT component used by the coherent-transport
five-power orbit calculation. -/
theorem fibonacci_transport_five_power_crt_lcm (a : ℕ) :
    Nat.lcm (Nat.lcm 3 (4 * 5 ^ a)) 58 = 348 * 5 ^ a := by
  rw [lcm_three_four_five_power]
  have hfactor : Nat.lcm (12 * 5 ^ a) 58 =
      Nat.lcm (2 * (6 * 5 ^ a)) (2 * 29) := by
    congr 1 <;> ring
  rw [hfactor]
  rw [← lcm_eq_nat_lcm, lcm_mul_left]
  simp only [normalize_eq, lcm_eq_nat_lcm]
  rw [coprime_six_five_power_twenty_nine a |>.lcm_eq_mul]
  ring

end D5.S3.Arith.FibonacciTransportFivePowerArithmetic
