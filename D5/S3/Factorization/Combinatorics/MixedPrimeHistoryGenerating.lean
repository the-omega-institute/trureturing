/- GID: D5/S3/Factorization/Combinatorics/MixedPrimeHistoryGenerating
   generality: G
   mirror-B: D5/B/S3/Factorization/Combinatorics/MixedPrimeHistoryGenerating
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A truncated mixed prime polynomial operator counts histories by length, and every nonempty history ends at least twice its length. -/

import D5.S3.Factorization.Combinatorics.MixedPrimeHistoryCount
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Data.Real.Basic

set_option autoImplicit false

namespace D5.S3.Factorization.Combinatorics.MixedPrimeHistoryGenerating

open D5.S3.Factorization.Combinatorics.MixedPrimeHistoryCount
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
open Polynomial

/-- Retain precisely the coefficients in degrees one through J. -/
noncomputable def clipPositive (J : ℕ) (f : Polynomial ℕ) : Polynomial ℕ :=
  ∑ n ∈ Finset.Icc 1 J, monomial n (f.coeff n)

/-- Iterate prime addition and multiplication on exponents, retaining degrees one through J. -/
noncomputable def mixedPolynomial (J : ℕ) : ℕ → Polynomial ℕ
  | 0 => X
  | k+1 => clipPositive J (∑ q ∈ Nat.primesLE J,
      (X ^ q * mixedPolynomial J k + (mixedPolynomial J k).comp (X ^ q)))

/-- Sum the length weights of all histories with a positive endpoint, and set the value at zero to zero. -/
noncomputable def weightedCount (r : ℝ) (n : ℕ) : ℝ :=
  if hn : 0 < n then ∑ w ∈ (reachable_finite n hn).2.toFinset, r ^ w.length else 0

/-- Sum the first J mixed history polynomials with a real weight for each step. -/
noncomputable def weightedPolynomial (J : ℕ) (t : ℝ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range J, C (t ^ k) * (mixedPolynomial J k).map (Nat.castRingHom ℝ)

/-- The total length weight of histories ending at primes at most X. -/
noncomputable def partition (X : ℕ) (r : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE X, weightedCount r p

set_option maxHeartbeats 800000 in
/-- In every retained degree, the kth iterate counts histories of length k. -/
theorem mixed_coefficient (J k n : ℕ) (hn : 1 ≤ n) (hnJ : n ≤ J) :
    (mixedPolynomial J k).coeff n = lengthCount k n := by
  sorry

/-- Every nonempty prime history ends at least twice its length. -/
theorem sharp_length_bound (w : List PrimeLetter) (hw : w ≠ []) :
    2 * w.length ≤ endpoint w := by
  sorry

end D5.S3.Factorization.Combinatorics.MixedPrimeHistoryGenerating
