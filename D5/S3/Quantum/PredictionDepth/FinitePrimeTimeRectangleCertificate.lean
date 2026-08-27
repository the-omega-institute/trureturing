/- GID: D5/S3/Quantum/PredictionDepth/FinitePrimeTimeRectangleCertificate
   generality: G
   mirror-B: D5/B/S3/Quantum/PredictionDepth/FinitePrimeTimeRectangleCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite quantum effect certificate extends to a finite rectangular window. -/

import D5.S3.Quantum.PredictionDepth.FinitePrimeTimeCertificate

/- Library-search audit trail (2026-08-27):
   * Exact family hit `finite_prime_time_certificate` supplies the selected
     natural index-time pairs, the dimension bound, their centered span, and
     density-state separation by those pairs.
   * Repository body-shape searches for first-coordinate images,
     second-coordinate suprema, and rectangular quantum windows found no theorem
     exposing the source's constructed `J` and `T` with rectangle completeness.
   * Exact pinned-Mathlib hits `Finset.mem_image` and `Finset.le_sup` show that
     every selected pair lies in the constructed finite rectangle. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.PredictionDepth.FinitePrimeTimeRectangleCertificate

open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Fibers.TraceZeroReadoutOrthogonalEquivalence
open D5.S3.Quantum.PredictionDepth.FinitePrimeTimeCertificate

/-- A complete natural index-time family has at most `d^2 - 1` selected
centered effects that already separate density states. The selected indices
and one plus the largest selected time construct a finite rectangular window
that is still information-complete. -/
theorem finite_prime_time_rectangle_certificate
    (d : Nat) [NeZero d]
    (effects : Nat × Nat -> HermitianTraceZero (d := Fin d))
    (hcomplete : Submodule.span ℝ (Set.range effects) = ⊤) :
    ∃ selected : Finset (Nat × Nat),
      selected.card ≤ d ^ 2 - 1 ∧
        Submodule.span ℝ
            (Set.range fun index : selected => effects index.1) = ⊤ ∧
        (∀ rho sigma : DensityState (Fin d),
          (∀ index : selected,
            (Matrix.trace
                (CStarMatrix.ofMatrix.symm rho.1 * (effects index.1).1)).re =
              (Matrix.trace
                (CStarMatrix.ofMatrix.symm sigma.1 * (effects index.1).1)).re) ->
          rho = sigma) ∧
        let primeIndices := selected.image fun index => index.1
        let horizon := selected.sup (fun index => index.2) + 1
        ∀ rho sigma : DensityState (Fin d),
          (∀ prime, prime ∈ primeIndices -> ∀ time, time < horizon ->
            (Matrix.trace
                (CStarMatrix.ofMatrix.symm rho.1 * (effects (prime, time)).1)).re =
              (Matrix.trace
                (CStarMatrix.ofMatrix.symm sigma.1 * (effects (prime, time)).1)).re) ->
          rho = sigma := by
  classical
  obtain ⟨selected, hcard, hspan, hselectedSeparates⟩ :=
    finite_prime_time_certificate d effects hcomplete
  refine ⟨selected, hcard, hspan, hselectedSeparates, ?_⟩
  dsimp
  intro rho sigma hrectangle
  apply hselectedSeparates
  intro index
  apply hrectangle index.1.1
  · exact Finset.mem_image.mpr ⟨index.1, index.2, rfl⟩
  · exact Nat.lt_succ_of_le (Finset.le_sup (f := fun pair => pair.2) index.2)

#print axioms finite_prime_time_rectangle_certificate

end D5.S3.Quantum.PredictionDepth.FinitePrimeTimeRectangleCertificate
