/- GID: D5/S3/Weil/Mertens/CoprimeSquarefreeDensity
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/CoprimeSquarefreeDensity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Count squarefree integers coprime to a fixed squarefree modulus with an explicit square-root error. -/

import D5.S3.Weil.Mertens.CoprimeMobiusCertificateError
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Algebra.InfiniteSum.Basic

set_option autoImplicit false

open scoped BigOperators
open Finset
open D5.S3.Weil.Mertens.CoprimeMobiusCertificateError

namespace D5.S3.Weil.Mertens.CoprimeSquarefreeDensity

/-- The number of positive squarefree integers at most X and coprime to Q. -/
noncomputable def S (Q : ℕ) (X : ℝ) : ℝ := by
  classical
  exact ((((Finset.Icc 1 ⌊X⌋₊).filter (fun d => d.Coprime Q ∧ Squarefree d)).card : ℕ) : ℝ)

/-- The reciprocal square series density with one coprimality factor for each prime divisor. -/
noncomputable def rho (Q : ℕ) : ℝ :=
  (∑' n : ℕ, (((n : ℝ) + 1) ^ 2)⁻¹)⁻¹ *
    ∏ p ∈ Q.primeFactors, (p : ℝ) / ((p : ℝ) + 1)

set_option maxHeartbeats 800000 in
/-- The squarefree coprime count differs from its density times X by an explicit square-root bound. -/
theorem squarefree_coprime_count_error (Q : ℕ) (X : ℝ) (hQ : Squarefree Q) (hX : 0 ≤ X) :
    |S Q X - rho Q * X| ≤ ((2 : ℝ) ^ Q.primeFactors.card + 2) * Real.sqrt X := by
  classical
  sorry

end D5.S3.Weil.Mertens.CoprimeSquarefreeDensity
