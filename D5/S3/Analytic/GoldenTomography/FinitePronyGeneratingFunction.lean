/- GID: D5/S3/Analytic/GoldenTomography/FinitePronyGeneratingFunction
   generality: G
   mirror-B: D5/B/S3/Analytic/GoldenTomography/FinitePronyGeneratingFunction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite Prony moment sequence has the expected partial-fraction generating function throughout its common geometric convergence region. -/

import D5.S3.Analytic.GoldenTomography.FinitePronyHankelReconstruction
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Finite Prony generating function

A finite exponential moment sequence

`c n = sum j, weight j * node j ^ n`

has generating function

`sum n, c n * z ^ n = sum j, weight j / (1 - node j * z)`

whenever every geometric mode lies in its convergence disk. This is the exact
finite rational-transfer identity used by Prony reconstruction, matrix-pencil
methods, and finite Koopman resolvents. No meromorphic continuation or
infinite-mode interchange is asserted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators Topology

namespace D5.S3.Analytic.GoldenTomography.FinitePronyGeneratingFunction

open D5.S3.Analytic.GoldenTomography.FinitePronyHankelReconstruction

universe u

variable {K : Type u} [NormedField K] [CompleteSpace K]

/-- The ordinary generating function of a finite Prony moment sequence. -/
def pronyGeneratingFunction {m : ℕ}
    (nodes weights : Fin m → K) (z : K) : K :=
  ∑' n : ℕ, pronyMoment nodes weights n * z ^ n

/-- Each finite Prony generating series sums to the corresponding finite
partial-fraction expression inside the common geometric convergence region. -/
theorem prony_generating_function_hasSum {m : ℕ}
    (nodes weights : Fin m → K) (z : K)
    (hDisk : ∀ mode, ‖nodes mode * z‖ < 1) :
    HasSum
      (fun n : ℕ => pronyMoment nodes weights n * z ^ n)
      (∑ mode, weights mode * (1 - nodes mode * z)⁻¹) := by
  classical
  have hModes :
      ∀ mode ∈ (Finset.univ : Finset (Fin m)),
        HasSum
          (fun n : ℕ => weights mode * (nodes mode * z) ^ n)
          (weights mode * (1 - nodes mode * z)⁻¹) := by
    intro mode hmode
    exact (hasSum_geometric_of_norm_lt_one (hDisk mode)).mul_left (weights mode)
  simpa only [pronyMoment, Finset.sum_apply, Finset.sum_mul, mul_pow, mul_assoc] using
    hasSum_sum hModes

/-- The ordinary generating function is the finite partial-fraction sum in its
common disk of convergence. -/
theorem prony_generating_function_eq_partial_fractions {m : ℕ}
    (nodes weights : Fin m → K) (z : K)
    (hDisk : ∀ mode, ‖nodes mode * z‖ < 1) :
    pronyGeneratingFunction nodes weights z =
      ∑ mode, weights mode * (1 - nodes mode * z)⁻¹ :=
  (prony_generating_function_hasSum nodes weights z hDisk).tsum_eq

/-- The exact finite rational package also records summability of the original
moment power series. -/
theorem finite_prony_rational_generating_function {m : ℕ}
    (nodes weights : Fin m → K) (z : K)
    (hDisk : ∀ mode, ‖nodes mode * z‖ < 1) :
    Summable (fun n : ℕ => pronyMoment nodes weights n * z ^ n) ∧
    pronyGeneratingFunction nodes weights z =
      ∑ mode, weights mode * (1 - nodes mode * z)⁻¹ := by
  have hSum := prony_generating_function_hasSum nodes weights z hDisk
  exact ⟨hSum.summable, hSum.tsum_eq⟩

-- A nonvacuous one-mode witness for the common convergence hypothesis.
example :
    pronyGeneratingFunction (fun _ : Fin 1 => (1 / 2 : ℝ))
        (fun _ : Fin 1 => 3) (1 / 2) = 4 := by
  rw [prony_generating_function_eq_partial_fractions]
  · norm_num
  · intro mode
    fin_cases mode
    norm_num

#print axioms prony_generating_function_hasSum
#print axioms prony_generating_function_eq_partial_fractions
#print axioms finite_prony_rational_generating_function

end D5.S3.Analytic.GoldenTomography.FinitePronyGeneratingFunction
