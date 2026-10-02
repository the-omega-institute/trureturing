/- GID: D5/S3/Arith/Robin/EulerValuationMomentComparison
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/EulerValuationMomentComparison
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: The complete valuation Euler moment and the prime-support moment have an explicit logarithmic comparison. -/

import D5.S3.Arith.GoldenResource.PrefixDeficitKernel
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.SumPrimeReciprocals

set_option autoImplicit false
noncomputable section

namespace D5.S3.Arith.Robin.EulerValuationMomentComparison

open Finset Real
open D5.S3.Arith.GoldenResource.PrefixDeficitKernel

/-- The full geometric-valuation local moment. -/
def localU (p : Nat.Primes) (s : ℝ) : ℝ :=
  (1 - (p : ℝ)⁻¹) * ∑' a : ℕ, S a (p : ℝ)⁻¹ ^ s * ((p : ℝ)⁻¹) ^ a

/-- The local moment recording the prime support. -/
def localW (p : Nat.Primes) (s : ℝ) : ℝ :=
  1 - (p : ℝ)⁻¹ + (p : ℝ)⁻¹ * (1 - (p : ℝ)⁻¹) ^ (-s)

/-- The Euler product of full valuation moments. -/
def U (s : ℝ) : ℝ := ∏' p : Nat.Primes, localU p s

/-- The Euler product of prime-support moments. -/
def W (s : ℝ) : ℝ := ∏' p : Nat.Primes, localW p s

/-- Local convergence, positive Euler products, and their explicit logarithmic gap. -/
theorem result (s : ℝ) (hs : 4 ≤ s) :
    (∀ p : Nat.Primes,
      Summable (fun a : ℕ => S a (p : ℝ)⁻¹ ^ s * ((p : ℝ)⁻¹) ^ a) ∧
      1 ≤ localU p s ∧ localU p s ≤ localW p s) ∧
    Multipliable (fun p : Nat.Primes => localU p s) ∧
    Multipliable (fun p : Nat.Primes => localW p s) ∧
    0 < U s ∧ 0 < W s ∧
    0 ≤ Real.log (W s) - Real.log (U s) ∧
    Real.log (W s) - Real.log (U s) ≤ Real.sqrt s * (Real.log s + 5) := by
  sorry

end D5.S3.Arith.Robin.EulerValuationMomentComparison
