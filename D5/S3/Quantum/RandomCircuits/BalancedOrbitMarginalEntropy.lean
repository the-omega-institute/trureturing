/- GID: D5/S3/Quantum/RandomCircuits/BalancedOrbitMarginalEntropy
   generality: I
   mirror-B: D5/B/S3/Quantum/RandomCircuits/BalancedOrbitMarginalEntropy
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Balanced bipartite marginals have equal Haar-averaged von Neumann entropies. -/

import D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity

/-! Haar symmetry exchanges the marginals of a balanced bipartite state. -/

set_option autoImplicit false

noncomputable section

open Matrix MeasureTheory TopologicalSpace
open scoped Matrix.Norms.Elementwise

namespace D5.S3.Quantum.RandomCircuits.BalancedOrbitMarginalEntropy

open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition (DensityState)
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching (vonNeumannEntropy)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
  (partialTraceLeft partialTraceRight marginalLeft marginalRight)
open D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity (unitaryConjugateState)
open D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl (permutationUnitary)

/-- Equality of the two marginal entropy averages on every balanced global unitary orbit. -/
def claim : Prop :=
  ∀ n : ℕ, ∀ ρ : DensityState (Fin n × Fin n),
    (∫ u : Matrix.unitaryGroup (Fin n × Fin n) ℂ,
      vonNeumannEntropy (marginalRight (unitaryConjugateState
        (u : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) u.2 ρ))
      ∂(Measure.haarMeasure (⊤ : PositiveCompacts (Matrix.unitaryGroup (Fin n × Fin n) ℂ)))) =
    ∫ u : Matrix.unitaryGroup (Fin n × Fin n) ℂ,
      vonNeumannEntropy (marginalLeft (unitaryConjugateState
        (u : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) u.2 ρ))
      ∂(Measure.haarMeasure (⊤ : PositiveCompacts (Matrix.unitaryGroup (Fin n × Fin n) ℂ)))

private theorem swap_conjugate (n : ℕ)
    (x : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :
    (permutationUnitary (Equiv.prodComm (Fin n) (Fin n)) :
      Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) * x *
      star (permutationUnitary (Equiv.prodComm (Fin n) (Fin n)) :
        Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) =
      x.submatrix (Equiv.prodComm (Fin n) (Fin n)) (Equiv.prodComm (Fin n) (Fin n)) := by
  change Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin n) (Fin n)) * x *
    star (Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin n) (Fin n))) = _
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_permMatrix]
  change (Equiv.prodComm (Fin n) (Fin n)).toPEquiv.toMatrix * x *
    (Equiv.prodComm (Fin n) (Fin n)).symm.toPEquiv.toMatrix = _
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  rfl

private theorem partial_trace_swap (n : ℕ)
    (x : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :
    partialTraceRight
      ((permutationUnitary (Equiv.prodComm (Fin n) (Fin n)) :
        Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) * x *
        star (permutationUnitary (Equiv.prodComm (Fin n) (Fin n)) :
          Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)) = partialTraceLeft x := by
  rw [swap_conjugate]
  rfl

private theorem marginal_swap_mul (n : ℕ) (ρ : DensityState (Fin n × Fin n))
    (u : Matrix.unitaryGroup (Fin n × Fin n) ℂ) :
    marginalRight (unitaryConjugateState
      ((permutationUnitary (Equiv.prodComm (Fin n) (Fin n)) * u :
        Matrix.unitaryGroup (Fin n × Fin n) ℂ) :
        Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
      (permutationUnitary (Equiv.prodComm (Fin n) (Fin n)) * u).2 ρ) =
    marginalLeft (unitaryConjugateState
      (u : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) u.2 ρ) := by
  apply Subtype.ext
  apply congrArg CStarMatrix.ofMatrix
  change partialTraceRight
    (((permutationUnitary (Equiv.prodComm (Fin n) (Fin n)) :
      Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) *
      (u : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)) *
      CStarMatrix.ofMatrix.symm ρ.1 *
      star ((permutationUnitary (Equiv.prodComm (Fin n) (Fin n)) :
        Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) *
        (u : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ))) =
    partialTraceLeft
      ((u : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) * CStarMatrix.ofMatrix.symm ρ.1 *
        star (u : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ))
  rw [star_mul]
  simpa only [Matrix.mul_assoc] using partial_trace_swap n
    ((u : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) * CStarMatrix.ofMatrix.symm ρ.1 *
      star (u : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ))

/-- The Zhang–Xiang balanced marginal entropy identity. -/
theorem result : claim := by
  intro n ρ
  calc
    _ = ∫ u : Matrix.unitaryGroup (Fin n × Fin n) ℂ,
        vonNeumannEntropy (marginalRight (unitaryConjugateState
          ((permutationUnitary (Equiv.prodComm (Fin n) (Fin n)) * u :
            Matrix.unitaryGroup (Fin n × Fin n) ℂ) :
            Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
          (permutationUnitary (Equiv.prodComm (Fin n) (Fin n)) * u).2 ρ))
        ∂(Measure.haarMeasure (⊤ : PositiveCompacts
          (Matrix.unitaryGroup (Fin n × Fin n) ℂ))) :=
      (integral_mul_left_eq_self
        (μ := Measure.haarMeasure (⊤ : PositiveCompacts
          (Matrix.unitaryGroup (Fin n × Fin n) ℂ)))
        (fun u : Matrix.unitaryGroup (Fin n × Fin n) ℂ =>
          vonNeumannEntropy (marginalRight (unitaryConjugateState
            (u : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) u.2 ρ)))
        (permutationUnitary (Equiv.prodComm (Fin n) (Fin n)))).symm
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun u =>
      congrArg vonNeumannEntropy (marginal_swap_mul n ρ u))

end D5.S3.Quantum.RandomCircuits.BalancedOrbitMarginalEntropy
