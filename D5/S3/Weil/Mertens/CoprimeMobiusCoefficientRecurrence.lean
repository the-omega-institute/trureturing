/- GID: D5/S3/Weil/Mertens/CoprimeMobiusCoefficientRecurrence
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/CoprimeMobiusCoefficientRecurrence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Adjoining a new prime strictly decreases the coprime Mobius coefficient. -/

import D5.S3.Weil.Mertens.CoprimeMobiusCertificateError
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false

open scoped BigOperators Topology
open Finset MeasureTheory Set Filter
open D5.S3.Weil.Mertens.CoprimeMobiusCertificateError
open private divisorList from D5.S3.Arith.Congruence.DivisorDifferenceGcdHeinz

noncomputable section
namespace D5.S3.Weil.Mertens.CoprimeMobiusCoefficientRecurrence

/-- The same-sign overlap of a truncated Mobius kernel and its dilation. -/
def H (R p : ℕ) (u : ℝ) : ℝ :=
  if 0 < B R u * B R (u / p) then
    min |(B R u : ℝ)| |(B R (u / p) : ℝ)| else 0

/-- The inverse-square integral of the same-sign overlap over real numbers greater than one. -/
def J (R p : ℕ) : ℝ := ∫ u in Set.Ioi (1 : ℝ), H R p u / u ^ 2

/-- Adjoining a prime outside a squarefree modulus gives an exact coefficient recurrence
and strictly decreases the coefficient. -/
set_option maxHeartbeats 800000 in
theorem coefficient_recurrence (R p : ℕ) (hR : Squarefree R) (hR1 : 1 < R)
    (hp : p.Prime) (hpR : ¬ p ∣ R) :
    c (R * p) = (1 - ((p : ℝ)⁻¹) ^ 2) * c R -
      2 * e R * (1 - (p : ℝ)⁻¹) * J R p ∧ c (R * p) < c R := by
  sorry

/-- A positive same-sign overlap at one point forces its inverse-square integral to be positive. -/
set_option maxHeartbeats 800000 in
theorem overlap_integral_pos (R p : ℕ) (hR : Squarefree R) (hR1 : 1 < R)
    (hp : p.Prime) {u₀ : ℝ} (hu₀ : 1 ≤ u₀)
    (hsign : 0 < B R u₀ * B R (u₀ / p)) : 0 < J R p := by
  sorry

end D5.S3.Weil.Mertens.CoprimeMobiusCoefficientRecurrence
