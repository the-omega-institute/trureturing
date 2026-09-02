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
sum of its geometric resolvents. The proof is split into a one-mode geometric
series, a finite family combination, public summability, and final value
identification. The theorem is pointwise on a common disk of convergence. It
makes no claim about unknown-node recovery, noisy stability, confluent repeated
nodes, or infinite Hankel operators.
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

/-- The common pointwise convergence condition for every modal geometric
series. -/
def finitePronyConvergesAt {m : ℕ}
    (nodes : Fin m → ℂ) (z : ℂ) : Prop :=
  ∀ j, ‖nodes j * z‖ < 1

/-- The `n`th term of the finite Prony generating series at `z`. -/
def finitePronySeriesTerm {m : ℕ}
    (nodes weights : Fin m → ℂ) (z : ℂ) (n : ℕ) : ℂ :=
  finitePronyMoment nodes weights n * z ^ n

/-- The generating series of the finite Prony moment sequence. -/
def finitePronyGeneratingSeries {m : ℕ}
    (nodes weights : Fin m → ℂ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, finitePronySeriesTerm nodes weights z n

/-- The finite sum of geometric resolvents attached to the same modes. -/
def finitePronyRationalFunction {m : ℕ}
    (nodes weights : Fin m → ℂ) (z : ℂ) : ℂ :=
  ∑ j, weights j / (1 - nodes j * z)

private theorem finite_prony_mode_resolvent_hasSum
    {m : ℕ} (nodes weights : Fin m → ℂ) (z : ℂ) (j : Fin m)
    (hConverges : ‖nodes j * z‖ < 1) :
    HasSum
      (fun n : ℕ => weights j * (nodes j * z) ^ n)
      (weights j / (1 - nodes j * z)) := by
  have hGeometric :
      HasSum
        (fun n : ℕ => (nodes j * z) ^ n)
        ((1 - nodes j * z)⁻¹) :=
    hasSum_geometric_of_norm_lt_one hConverges
  simpa [div_eq_mul_inv] using hGeometric.mul_left (weights j)

private theorem finite_prony_finite_sum_hasSum
    {m : ℕ} (nodes weights : Fin m → ℂ) (z : ℂ)
    (hConverges : finitePronyConvergesAt nodes z) :
    HasSum
      (∑ j : Fin m, fun n : ℕ => weights j * (nodes j * z) ^ n)
      (∑ j : Fin m, weights j / (1 - nodes j * z)) := by
  classical
  apply hasSum_sum
  intro j _
  exact finite_prony_mode_resolvent_hasSum
    nodes weights z j (hConverges j)

private theorem finite_prony_series_hasSum
    {m : ℕ} (nodes weights : Fin m → ℂ) (z : ℂ)
    (hConverges : finitePronyConvergesAt nodes z) :
    HasSum
      (finitePronySeriesTerm nodes weights z)
      (finitePronyRationalFunction nodes weights z) := by
  simpa [finitePronySeriesTerm, finitePronyMoment,
    finitePronyRationalFunction, Finset.sum_mul, mul_pow, mul_assoc] using
    (finite_prony_finite_sum_hasSum nodes weights z hConverges)

/-- On the common geometric disk, the finite Prony generating series is
summable. This separates the convergence obligation from identification of its
sum. -/
theorem finite_prony_generating_series_summable
    {m : ℕ} (nodes weights : Fin m → ℂ) (z : ℂ)
    (hConverges : finitePronyConvergesAt nodes z) :
    Summable (finitePronySeriesTerm nodes weights z) :=
  (finite_prony_series_hasSum nodes weights z hConverges).summable

/-- Formula (1295.1--1295.2): on every point where all modal geometric
series converge, the generating series of the finite Prony moments is exactly
the finite sum of the corresponding rational resolvents. -/
theorem finite_prony_rational_generating_function
    {m : ℕ} (nodes weights : Fin m → ℂ) (z : ℂ)
    (hConverges : finitePronyConvergesAt nodes z) :
    finitePronyGeneratingSeries nodes weights z =
      finitePronyRationalFunction nodes weights z := by
  unfold finitePronyGeneratingSeries
  exact (finite_prony_series_hasSum nodes weights z hConverges).tsum_eq

-- A concrete one-mode witness shows that the convergence hypotheses are
-- inhabited, that the series is summable, and that the public equality
-- specializes to a nonzero resolvent.
example :
    Summable
        (finitePronySeriesTerm
          (fun _ : Fin 1 => (0 : ℂ))
          (fun _ : Fin 1 => (1 : ℂ))
          (1 : ℂ)) ∧
      finitePronyGeneratingSeries
          (fun _ : Fin 1 => (0 : ℂ))
          (fun _ : Fin 1 => (1 : ℂ))
          (1 : ℂ) = 1 := by
  have hConverges :
      finitePronyConvergesAt
        (fun _ : Fin 1 => (0 : ℂ)) (1 : ℂ) := by
    simp [finitePronyConvergesAt]
  constructor
  · exact finite_prony_generating_series_summable
      (fun _ : Fin 1 => (0 : ℂ))
      (fun _ : Fin 1 => (1 : ℂ))
      (1 : ℂ) hConverges
  · have h := finite_prony_rational_generating_function
      (fun _ : Fin 1 => (0 : ℂ))
      (fun _ : Fin 1 => (1 : ℂ))
      (1 : ℂ) hConverges
    simpa [finitePronyRationalFunction] using h

#print axioms finite_prony_generating_series_summable
#print axioms finite_prony_rational_generating_function

end D5.S3.Analytic.GoldenTomography.FinitePronyRationalGeneratingFunction
