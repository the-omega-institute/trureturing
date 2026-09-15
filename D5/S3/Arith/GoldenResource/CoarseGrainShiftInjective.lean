/- GID: D5/S3/Arith/GoldenResource/CoarseGrainShiftInjective
   generality: I
   mirror-B: D5/B/S3/Arith/GoldenResource/CoarseGrainShiftInjective
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Agreement at every forward shift makes the frozen golden exponent observation injective. -/

import D5.S3.Arith.GoldenResource.GoldenDivisorLanguage
import D5.S3.Arith.GoldenResource.GoldenFixedPoint
import Mathlib

open Nat
open D5.S3.Arith.GoldenResource.GoldenDivisorLanguage
open D5.S3.Arith.GoldenResource.GoldenFixedPoint

namespace D5.S3.Arith.GoldenResource.CoarseGrainShiftInjective

/-- Forward-shift agreement of the golden exponent observation `b` determines the index.
The proof reuses the frozen `b` (definition), `b_le` (the observation never increases an
exponent) and `b_fixed_iff` (a value is fixed iff it is a Fibonacci-window endpoint); it adds
only the cofinal-endpoint construction that forces equality. -/
theorem b_shift_injective {a c : ℕ}
    (h : ∀ t : ℕ, b (a + t) = b (c + t)) : a = c := by
  have aux : ∀ x y : ℕ, x < y →
      (∀ t : ℕ, b (x + t) = b (y + t)) → False := by
    intro x y hxy hxy'
    have hfibm1 : 1 ≤ Nat.fib (y + 5) := Nat.fib_pos.mpr (by omega)
    have hfibm : y + 1 ≤ Nat.fib (y + 5) := by
      have := Nat.le_fib_self (show 5 ≤ y + 5 by omega); omega
    set cc := Nat.fib (y + 5) - 1 with hc
    have hcy : y ≤ cc := by omega
    set t := cc - y with ht
    have hyt : y + t = cc := by omega
    have hxt : x + t < cc := by omega
    -- cc = fib(y+5) − 1 is a window endpoint, hence a fixed point of the observation
    have hyval : b (y + t) = cc := by
      rw [hyt]
      exact (b_fixed_iff cc).mpr ⟨y + 5, by omega, by omega⟩
    -- the frozen bound gives the strict drop below the endpoint
    have hxval : b (x + t) < cc := lt_of_le_of_lt (b_le (x + t)) hxt
    have hcontra := hxy' t
    omega
  rcases lt_trichotomy a c with hlt | heq | hgt
  · exact (aux a c hlt h).elim
  · exact heq
  · exact (aux c a hgt (fun t => (h t).symm)).elim

end D5.S3.Arith.GoldenResource.CoarseGrainShiftInjective
