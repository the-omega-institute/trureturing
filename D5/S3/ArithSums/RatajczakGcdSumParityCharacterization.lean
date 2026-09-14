/- GID: D5/S3/ArithSums/RatajczakGcdSumParityCharacterization
   generality: I
   mirror-B: D5/B/S3/ArithSums/RatajczakGcdSumParityCharacterization
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Ring.Nat, mathlib/module/Mathlib.Data.Finset.Interval, mathlib/module/Mathlib.Data.Nat.GCD.Basic, mathlib/module/Mathlib.Data.Nat.Prime.Defs, mathlib/module/Mathlib.Data.ZMod.Basic]
   utility: none
   digest: Both Ratajczak gcd-filtered sums are even exactly at positive multiples of eight. -/

import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Basic

open scoped BigOperators

namespace D5.S3.ArithSums.RatajczakGcdSumParityCharacterization

set_option autoImplicit false
set_option relaxedAutoImplicit false

def gcd2 (k m : ℕ) : ℕ :=
  Nat.gcd k m / Nat.minFac (Nat.gcd k m)

def lcd2 (k m : ℕ) : ℕ :=
  Nat.minFac (Nat.gcd k m)

def G (m : ℕ) : ℕ :=
  ∑ k ∈ (Finset.Icc 1 m).filter (fun k => Nat.gcd k m ≠ 1), gcd2 k m

def L (m : ℕ) : ℕ :=
  ∑ k ∈ (Finset.Icc 1 m).filter (fun k => Nat.gcd k m ≠ 1), lcd2 k m

#eval (G 8, L 8)
#eval (G 16, L 16)
#eval (G 24, L 24)

end D5.S3.ArithSums.RatajczakGcdSumParityCharacterization
