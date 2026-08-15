/- GID: D5/S3/Analytic/Boundary/ConditionalNaturalBoundary
   generality: G
   mirror-B: D5/B/S3/Analytic/Boundary/ConditionalNaturalBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Accumulating poles force a conditional boundary and expose any analytic gate. -/

/- Library-search audit trail (2026-08-16):
   * The repository theorem `scaled_candidate_poles_tendsto` supplies the exact
     convergence of transported candidates to every point on the imaginary axis.
   * Pinned Mathlib supplies `AnalyticAt.eventually_analyticAt` and
     `AnalyticAt.meromorphicOrderAt_nonneg` for the boundary and gate deductions.
   * Repository search found no declaration joining the conditional boundary and
     its eventual two-channel gate conclusion.
-/

import D5.S3.Analytic.ScaledPoleAccumulation
import Mathlib.Analysis.Meromorphic.Order

namespace D5.S3.Analytic.Boundary.ConditionalNaturalBoundary

open Complex Filter Topology
open D5.S3.Analytic.ScaledPoleAccumulation

/-- The candidate obtained by transporting a height through a positive scale. -/
noncomputable def candidatePoint (scale height : ℕ -> ℝ) (n : ℕ) : ℂ :=
  (((2 * scale n)⁻¹ : ℝ) : ℂ) +
    ((height n / scale n : ℝ) : ℂ) * I

/-- If the scale tends to infinity and normalized candidate heights approach every
target, then negative-order candidate poles force a natural boundary on the
imaginary axis. Conversely, analyticity at an axis point makes nearby candidates
eventually analytic, so every such candidate must enter one of the two supplied
cancellation channels. -/
theorem conditional_natural_boundary_and_gate
    (f : ℂ -> ℂ) (scale : ℕ -> ℝ) (height : ℝ -> ℕ -> ℝ)
    (tailNonvanishing lineCondition alternateCondition : Prop)
    (scaledZeroPattern tailZeroCollision : ℝ -> ℕ -> Prop)
    (hscale : Tendsto scale atTop atTop)
    (hheight : ∀ target : ℝ,
      Tendsto (fun n => height target n / scale n) atTop (𝓝 target))
    (hpoles : tailNonvanishing ∧ (lineCondition ∨ alternateCondition) ->
      ∀ (target : ℝ) (n : ℕ),
        meromorphicOrderAt f (candidatePoint scale (height target) n) < 0)
    (hchannels : ∀ (target : ℝ) (n : ℕ),
      ¬ meromorphicOrderAt f (candidatePoint scale (height target) n) < 0 ->
        scaledZeroPattern target n ∨ tailZeroCollision target n) :
    (tailNonvanishing ∧ (lineCondition ∨ alternateCondition) ->
      ∀ target : ℝ, ¬ AnalyticAt ℂ f ((target : ℂ) * I)) ∧
      ∀ target : ℝ, AnalyticAt ℂ f ((target : ℂ) * I) ->
        ∀ᶠ n in atTop, scaledZeroPattern target n ∨ tailZeroCollision target n := by
  have hcandidates : ∀ target : ℝ,
      Tendsto (fun n => candidatePoint scale (height target) n) atTop
        (𝓝 ((target : ℂ) * I)) := by
    intro target
    simpa [candidatePoint] using
      scaled_candidate_poles_tendsto scale (height target) target hscale (hheight target)
  constructor
  · intro hconditions target htarget
    have heventually :
        ∀ᶠ n in atTop, AnalyticAt ℂ f (candidatePoint scale (height target) n) :=
      hcandidates target htarget.eventually_analyticAt
    obtain ⟨n, hn⟩ := heventually.exists
    exact (not_lt_of_ge hn.meromorphicOrderAt_nonneg) (hpoles hconditions target n)
  · intro target htarget
    have heventually :
        ∀ᶠ n in atTop, AnalyticAt ℂ f (candidatePoint scale (height target) n) :=
      hcandidates target htarget.eventually_analyticAt
    filter_upwards [heventually] with n hn
    exact hchannels target n (not_lt_of_ge hn.meromorphicOrderAt_nonneg)

#print axioms conditional_natural_boundary_and_gate

end D5.S3.Analytic.Boundary.ConditionalNaturalBoundary
