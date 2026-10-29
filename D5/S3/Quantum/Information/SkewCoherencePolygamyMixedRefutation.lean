/- GID: D5/S3/Quantum/Information/SkewCoherencePolygamyMixedRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/SkewCoherencePolygamyMixedRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/SkewCoherencePolygamyMixedRefutation.claim; result=D5/S3/Quantum/Information/SkewCoherencePolygamyMixedRefutation.result; claim=D5/S3/Quantum/Information/SkewCoherencePolygamyMixedRefutation.claim
   digest: A mixed state on two by three levels violates skew-coherence polygamy. -/

import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Information.SLDSpectralEnergy
import Mathlib.Analysis.Matrix.Order

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Quantum.Information.SkewCoherencePolygamyMixedRefutation

open Matrix
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Information.SLDSpectralEnergy
open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

/-- Yu's skew-information coherence in the given reference basis. -/
def skewCoherence {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : Matrix ι ι ℂ) : ℝ :=
  1 - ∑ k, (CFC.sqrt ρ k k).re ^ 2

/-- Mixed-state polygamy in every bipartite total dimension at least six. -/
def claim : Prop :=
  ∀ m n : ℕ, 6 ≤ m * n →
    ∀ ρ : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ,
      IsDensity ρ →
        1 - skewCoherence ρ ≤
          (1 - skewCoherence (partialTraceRight ρ)) *
          (1 - skewCoherence (partialTraceLeft ρ))

private def rho : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ :=
  fun p q =>
    if p.2 = 2 then
      if q.2 = 2 then (if p.1 = q.1 then 1 / 4 else 3 / 17) else 0
    else if q.2 = 2 then 0
    else if p = q then 1 / 8
    else if p.1 = q.1 ∨ p.2 = q.2 then 3 / 34 else 9 / 136

private def tau : Matrix (Fin 2) (Fin 2) ℂ :=
  fun a c => if a = c then 1 / 2 else 6 / 17

private def beta : Matrix (Fin 3) (Fin 3) ℂ :=
  fun b d =>
    if b = 2 then (if d = 2 then 1 / 2 else 0)
    else if d = 2 then 0 else if b = d then 1 / 4 else 3 / 17

private def rootRho : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ :=
  fun p q => (((if p.2 = 2 then
    if q.2 = 2 then
      Real.sqrt 29 + (if p.1 = q.1 then Real.sqrt 5 else -Real.sqrt 5)
    else 0
    else if q.2 = 2 then 0
    else if p = q then 5
    else if p.1 = q.1 ∨ p.2 = q.2 then 2 else 1) /
      (2 * Real.sqrt 68) : ℝ) : ℂ)

private def rootTau : Matrix (Fin 2) (Fin 2) ℂ :=
  fun a c => (((Real.sqrt 29 +
    (if a = c then Real.sqrt 5 else -Real.sqrt 5)) /
      (2 * Real.sqrt 34) : ℝ) : ℂ)

private def rootBeta : Matrix (Fin 3) (Fin 3) ℂ :=
  fun b d => ((if b = 2 then (if d = 2 then 1 / Real.sqrt 2 else 0)
    else if d = 2 then 0
    else (Real.sqrt 29 + (if b = d then Real.sqrt 5 else -Real.sqrt 5)) /
      (2 * Real.sqrt 68) : ℝ) : ℂ)

private lemma root_rho_positive : rootRho.PosSemidef := by
  sorry

private lemma root_rho_square : rootRho * rootRho = rho := by
  sorry

private lemma rho_density : IsDensity rho := by
  sorry

private lemma marginal_right : partialTraceRight rho = tau := by
  sorry

private lemma marginal_left : partialTraceLeft rho = beta := by
  sorry

private lemma root_tau_positive : rootTau.PosSemidef := by
  sorry

private lemma root_tau_square : rootTau * rootTau = tau := by
  sorry

private lemma root_beta_positive : rootBeta.PosSemidef := by
  sorry

private lemma root_beta_square : rootBeta * rootBeta = beta := by
  sorry

private lemma sqrt_rho : CFC.sqrt rho = rootRho := by
  sorry

private lemma sqrt_tau : CFC.sqrt tau = rootTau := by
  sorry

private lemma sqrt_beta : CFC.sqrt beta = rootBeta := by
  sorry

private lemma value_rho :
    1 - skewCoherence rho = (25 / 34 + (1 / 2 + Real.sqrt 145 / 34)) / 2 := by
  sorry

private lemma value_tau :
    1 - skewCoherence tau = 1 / 2 + Real.sqrt 145 / 34 := by
  sorry

private lemma value_beta :
    1 - skewCoherence beta = ((1 / 2 + Real.sqrt 145 / 34) + 1) / 2 := by
  sorry

private lemma strict_violation :
    (1 - skewCoherence tau) * (1 - skewCoherence beta) < 1 - skewCoherence rho := by
  sorry

/-- The registered two by three mixed state refutes the conjecture. -/
theorem result : ¬ claim := by
  intro h
  have hi := h 2 3 (by norm_num) rho rho_density
  rw [marginal_right, marginal_left] at hi
  exact (not_le_of_gt strict_violation) hi

end

end D5.S3.Quantum.Information.SkewCoherencePolygamyMixedRefutation
