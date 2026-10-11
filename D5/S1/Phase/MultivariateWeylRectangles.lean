/- GID: D5/S1/Phase/MultivariateWeylRectangles
   generality: G
   mirror-B: D5/B/S1/Phase/MultivariateWeylRectangles
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Polynomial phase averages over independently growing rectangular boxes. -/

import D5.S1.Phase.CharacterAverage
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Homogeneous

noncomputable section

namespace D5.S1.Phase.MultivariateWeylRectangles

open Filter Finset
open scoped Topology BigOperators

/-- The phase of an integer polynomial evaluated at one natural-number tuple. -/
def polynomialPhase {d : ℕ} (α : ℝ) (Q : MvPolynomial (Fin d) ℤ)
    (n : Fin d → ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * α *
    (MvPolynomial.eval (fun i => (n i : ℤ)) Q : ℂ))

/-- Cancellation over every sufficiently large rectangle, with a common side threshold. -/
def RectangularCancellation {d : ℕ} (f : (Fin d → ℕ) → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R : ℕ, 1 ≤ R ∧ ∀ N : Fin d → ℕ,
    (∀ i, R ≤ N i) → ‖𝔼 n ∈ Fintype.piFinset (fun i => range (N i)), f n‖ < ε

end D5.S1.Phase.MultivariateWeylRectangles
