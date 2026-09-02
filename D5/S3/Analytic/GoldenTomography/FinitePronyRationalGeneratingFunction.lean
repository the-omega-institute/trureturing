/- GID: D5/S3/Analytic/GoldenTomography/FinitePronyRationalGeneratingFunction
   generality: G
   mirror-B: D5/B/S3/Analytic/GoldenTomography/FinitePronyRationalGeneratingFunction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite exponential moment sequence has the expected finite rational generating function on its common disk of convergence. -/

import Mathlib.Analysis.SpecificLimits.Normed

/-!
This module isolates the exact analytic bridge used by finite Prony theory.
A finite sum of exponential modes has a generating series equal to the finite
sum of its geometric resolvents. The theorem is pointwise on a common disk of
convergence. It makes no claim about unknown-node recovery, noisy stability,
confluent repeated nodes, or infinite Hankel operators.
-/

/- Library-search audit trail (2026-09-02):
   * Current-tree searches for `Prony`, `finite exponential moment`,
     `rational generating function`, and the displayed sum of resolvents found
     the open OACTC atom and finite Vandermonde tomography, but no frozen Lean
     declaration of this generating-function identity.
   * Pinned Mathlib supplies `hasSum_geometric_of_norm_lt_one`,
     `HasSum.mul_left`, and `hasSum_sum`. These canonical finite-sum and
     geometric-series primitives are applied directly below.
   * The result is the exact finite layer. Conditioning, root perturbation,
     and confluent Prony theory remain separate obligations. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.GoldenTomography.FinitePronyRationalGeneratingFunction

open scoped BigOperators

/-- The `n`th moment of finitely many weighted exponential modes. -/
def finitePronyMoment {m : ℕ}
    (nodes weights : Fin m → ℂ) (n : ℕ) : ℂ :=
  ∑ j, weights j * nodes j ^ n

/-- The finite sum of geometric resolvents attached to the same modes. -/
def finitePronyRationalFunction {m : ℕ}
    (nodes weights : Fin m → ℂ) (z : ℂ) : ℂ :=
  ∑ j, weights j / (1 - nodes j * z)

private theorem finite_prony_rational_generating_function_hasSum
    {m : ℕ} (nodes weights : Fin m → ℂ) (z : ℂ)
    (hConverges : ∀ j, ‖nodes j * z‖ < 1) :
    HasSum
      (fun n : ℕ => finitePronyMoment nodes weights n * z ^ n)
      (finitePronyRationalFunction nodes weights z) := by
  classical
  have hMode :
      ∀ j : Fin m,
        HasSum
          (fun n : ℕ => weights j * (nodes j * z) ^ n)
          (weights j / (1 - nodes j * z)) := by
    intro j
    have hGeometric :
        HasSum
          (fun n : ℕ => (nodes j * z) ^ n)
          ((1 - nodes j * z)⁻¹) :=
      hasSum_geometric_of_norm_lt_one (hConverges j)
    simpa [div_eq_mul_inv] using hGeometric.mul_left (weights j)
  have hFiniteSum :
      HasSum
        (∑ j : Fin m, fun n : ℕ => weights j * (nodes j * z) ^ n)
        (∑ j : Fin m, weights j / (1 - nodes j * z)) := by
    apply hasSum_sum
    intro j _
    exact hMode j
  simpa [finitePronyMoment, finitePronyRationalFunction,
    Finset.sum_mul, mul_pow, mul_assoc] using hFiniteSum

/-- Formula (1295.1--1295.2): on every point where all modal geometric
series converge, the generating series of the finite Prony moments is exactly
the finite sum of the corresponding rational resolvents. -/
theorem finite_prony_rational_generating_function
    {m : ℕ} (nodes weights : Fin m → ℂ) (z : ℂ)
    (hConverges : ∀ j, ‖nodes j * z‖ < 1) :
    (∑' n : ℕ, finitePronyMoment nodes weights n * z ^ n) =
      finitePronyRationalFunction nodes weights z :=
  (finite_prony_rational_generating_function_hasSum
    nodes weights z hConverges).tsum_eq

-- A concrete one-mode witness shows that the convergence hypotheses are
-- inhabited and that the public equality specializes to a nonzero resolvent.
example :
    (∑' n : ℕ,
      finitePronyMoment
          (fun _ : Fin 1 => (0 : ℂ))
          (fun _ : Fin 1 => (1 : ℂ)) n * (1 : ℂ) ^ n) = 1 := by
  have h := finite_prony_rational_generating_function
    (fun _ : Fin 1 => (0 : ℂ))
    (fun _ : Fin 1 => (1 : ℂ))
    (1 : ℂ)
    (by intro j; simp)
  simpa [finitePronyRationalFunction] using h

#print axioms finite_prony_rational_generating_function

end D5.S3.Analytic.GoldenTomography.FinitePronyRationalGeneratingFunction
