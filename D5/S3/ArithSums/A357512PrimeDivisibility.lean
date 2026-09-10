/- GID: D5/S3/ArithSums/A357512PrimeDivisibility
   generality: G
   mirror-B: D5/B/S3/ArithSums/A357512PrimeDivisibility
   mirror-E: none(waiver:universal-divisibility-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Data.Nat.Choose.Basic]
   utility: none
   digest: The fifth-weighted Apéry binomial sum at p-1 is divisible by p^4 for every prime p at least 5. -/

import D5.S1.Phase.Interference.DedekindReciprocityFiniteSums
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Tactic

open Finset

namespace D5.S3.ArithSums.A357512PrimeDivisibility

/-- OEIS A357512, with offset zero. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ range (n + 1), k ^ 5 * (n.choose k) ^ 2 * ((n + k).choose k) ^ 2

private def b (p k : ℕ) : ℕ := (p - 1).choose k * (p + k - 1).choose k

private lemma b_step (p k : ℕ) (hp : 0 < p) :
    (k + 1) ^ 2 * b p (k + 1) = (p - 1 - k) * (p + k) * b p k := by
  have h₁ := Nat.choose_succ_right_eq (p - 1) k
  have h₂ := Nat.add_one_mul_choose_eq (p + k - 1) k
  rw [show p + k - 1 + 1 = p + k by omega] at h₂
  dsimp [b]
  calc
    _ = ((p - 1).choose (k + 1) * (k + 1)) *
        ((p + k).choose (k + 1) * (k + 1)) := by ring
    _ = _ := by rw [h₁, ← h₂]; ring

private lemma transport {R : Type*} [CommRing R] (t x : R) (ht : t ^ 4 = 0) :
    ((t - x - 1) * (t + x)) ^ 2 * (t ^ 2 * x ^ 2 - 2 * t ^ 3 * x) =
      x ^ 4 * (t ^ 2 * (x + 1) ^ 2 - 2 * t ^ 3 * (x + 1)) := by
  linear_combination
    (-2*t^3*x + t^2*x^2 + 4*t^2*x + 4*t*x^3 + 2*t*x^2 - 2*t*x -
      2*x^4 - 6*x^3 - 3*x^2) * ht

end D5.S3.ArithSums.A357512PrimeDivisibility
