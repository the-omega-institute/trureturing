/- GID: D5/S3/Weil/CayleyLaguerre/ChebyshevSlackPositivity
   generality: G
   mirror-B: D5/B/S3/Weil/CayleyLaguerre/ChebyshevSlackPositivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Nonnegative inputs give compactified Chebyshev slack bounds. -/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Tactic

/-!
# Chebyshev slack positivity

For a positive compactification scale, the rational coordinate
`(x - a) / (x + a)` sends every nonnegative real input into the closed unit
interval.  The first-kind Chebyshev bound on that interval then places the
associated slack `1 - T_N^2` between zero and one.

Library-search audit trail (2026-08-30):

* Exact-name and body-shape searches on the current tree and `origin/dev` for
  the rational coordinate, the Chebyshev slack, and their interval bounds found
  no existing D5 owner.
* `D5.S3.Weil.CayleyLaguerre.CayleyMomentTransport` uses first-kind Chebyshev
  polynomials in a circle-moment identity, but does not define this real
  coordinate or state its slack bounds.
* Pinned Mathlib's `Polynomial.Chebyshev.eval_T_real_mem_Icc` supplies the
  exact Chebyshev interval estimate used below; no Mathlib theorem combines it
  with this rational compactification.
-/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.CayleyLaguerre.ChebyshevSlackPositivity

/-- A scale above one quarter and a nonnegative real input construct a compact
coordinate in `[-1, 1]`; the corresponding first-kind Chebyshev slack also
lies in `[0, 1]`. -/
theorem chebyshev_slack_bounds
    (N : Nat) (a x : Real) (ha : (1 : Real) / 4 < a) (hx : 0 <= x) :
    let compactCoordinate := (x - a) / (x + a)
    let slack := 1 -
      (Polynomial.Chebyshev.T Real (N : Int)).eval compactCoordinate ^ 2
    compactCoordinate ∈ Set.Icc (-1) 1 /\ slack ∈ Set.Icc 0 1 := by
  dsimp only
  have haPositive : 0 < a := by linarith
  have hDenominator : 0 < x + a := by linarith
  have hCoordinate : (x - a) / (x + a) ∈ Set.Icc (-1 : Real) 1 := by
    constructor
    · rw [le_div_iff₀ hDenominator]
      linarith
    · rw [div_le_iff₀ hDenominator]
      linarith
  have hChebyshev :=
    Polynomial.Chebyshev.eval_T_real_mem_Icc (N : Int) hCoordinate
  rcases hChebyshev with ⟨hChebyshevLower, hChebyshevUpper⟩
  refine ⟨hCoordinate, ?_⟩
  constructor
  · nlinarith
  · nlinarith [sq_nonneg
      ((Polynomial.Chebyshev.T Real (N : Int)).eval ((x - a) / (x + a)))]

#print axioms chebyshev_slack_bounds

end D5.S3.Weil.CayleyLaguerre.ChebyshevSlackPositivity
