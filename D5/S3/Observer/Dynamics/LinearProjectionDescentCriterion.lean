/- GID: D5/S3/Observer/Dynamics/LinearProjectionDescentCriterion
   generality: G
   mirror-B: D5/B/S3/Observer/Dynamics/LinearProjectionDescentCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: For a finite complex Hilbert-space orthogonal projection, the six deterministic interface criteria are equivalent to vanishing hidden-to-visible flow, and self-adjoint dynamics make this equivalent to commutation. -/

import D5.S3.ConceptDynamics.Dialectics.DeterministicInterfaceEquivalence
import D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity

/- Library-search audit trail (2026-08-25):
   * Exact repository hit
     `deterministic_interface_sixfold_equivalence` packages effective-image
     descent, interface congruence, empty carry, factorization, pullback
     invariance, and equality of the depth-zero and depth-one kernels. It is
     imported and applied directly below.
   * The Observer, ConceptDynamics, and Entropy families were searched before
     introducing declarations. The canonical `EffectiveDescent`,
     `InterfaceCongruence`, `PullbackInvariant`, and kernel primitives are
     reused; this module introduces no replacement family definition.
   * Exact family hit `commutator_eq_cross_blocks` supplies the commutator
     identity and is applied directly. The adjacent complementary-subspace
     criteria use an abstract chosen complement rather than the matrix
     orthogonal-projection carrier required here.
   * Pinned Mathlib hits `Matrix.toLin'_mul`,
     `Matrix.conjTranspose_mul`, `Matrix.conjTranspose_sub`,
     `Matrix.conjTranspose_one`, and `Matrix.IsHermitian.eq` supply the
     linear and adjoint calculations. No packaged theorem was found for the
     full seven-condition statement. The loogle and leansearch executables
     were absent from PATH. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix

namespace D5.S3.Observer.Dynamics.LinearProjectionDescentCriterion

open D5.S3.ConceptDynamics.Dialectics.DeterministicInterfaceEquivalence
open D5.S3.ConceptDynamics.Dialectics.MinimalDialecticalRepair

/-- Let `P` be an orthogonal projection on the finite complex Hilbert space
`n -> ℂ`, represented by an idempotent Hermitian matrix, and let `T` be a
linear dynamics. The six canonical deterministic-interface conditions for
`q = P` and `F = T` are equivalent to `P * T * (1 - P) = 0`. If `T` is
Hermitian, that directed block vanishes exactly when `P * T - T * P = 0`. -/
theorem linear_projection_descent_criterion
    {n : Type*} [Fintype n] [DecidableEq n]
    (P T : Matrix n n ℂ) (hPIdempotent : P * P = P)
    (hPHermitian : P.IsHermitian) :
    List.TFAE [
      EffectiveDescent (fun x => Matrix.toLin' P x) (fun x => Matrix.toLin' T x),
      InterfaceCongruence (fun x => Matrix.toLin' P x) (fun x => Matrix.toLin' T x),
      ∀ x y, ¬IsCarryWitness (fun x => Matrix.toLin' P x)
        (fun x => Matrix.toLin' T x) (fun x => Matrix.toLin' P x) x y,
      Function.FactorsThrough
        ((fun x => Matrix.toLin' P x) ∘ (fun x => Matrix.toLin' T x))
        (fun x => Matrix.toLin' P x),
      PullbackInvariant (fun x => Matrix.toLin' P x) (fun x => Matrix.toLin' T x),
      depthZeroKernel (fun x => Matrix.toLin' P x) =
        depthOneKernel (fun x => Matrix.toLin' P x) (fun x => Matrix.toLin' T x),
      P * T * (1 - P) = 0] ∧
    (T.IsHermitian →
      (P * T * (1 - P) = 0 ↔ P * T - T * P = 0)) := by
  have hPComplement : P * (1 - P) = 0 := by
    calc
      P * (1 - P) = P - P * P := by noncomm_ring
      _ = 0 := by rw [hPIdempotent]; exact sub_self P
  have hInterface :
      InterfaceCongruence (fun x => Matrix.toLin' P x)
          (fun x => Matrix.toLin' T x) ↔
        P * T * (1 - P) = 0 := by
    constructor
    · intro hCongruence
      apply Matrix.toLin'.injective
      apply LinearMap.ext
      intro x
      have hSameReadout :
          Matrix.toLin' P (Matrix.toLin' (1 - P) x) =
            Matrix.toLin' P (0 : n → ℂ) := by
        calc
          Matrix.toLin' P (Matrix.toLin' (1 - P) x) =
              Matrix.toLin' (P * (1 - P)) x := by
            rw [Matrix.toLin'_mul]
            rfl
          _ = Matrix.toLin' P (0 : n → ℂ) := by
            rw [hPComplement]
            simp
      have hFuture := hCongruence _ _ hSameReadout
      simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec] using hFuture
    · intro hBlock x y hSameReadout
      have hKernel : Matrix.toLin' P (x - y) = 0 := by
        rw [map_sub, sub_eq_zero]
        exact hSameReadout
      have hHidden : Matrix.toLin' (1 - P) (x - y) = x - y := by
        change (1 - P) *ᵥ (x - y) = x - y
        change P *ᵥ (x - y) = 0 at hKernel
        rw [sub_mulVec, one_mulVec, hKernel, sub_zero]
      have hBlockLin := congrArg Matrix.toLin' hBlock
      have hAtDifference := LinearMap.congr_fun hBlockLin (x - y)
      apply sub_eq_zero.mp
      calc
        Matrix.toLin' P (Matrix.toLin' T x) -
            Matrix.toLin' P (Matrix.toLin' T y) =
            Matrix.toLin' P (Matrix.toLin' T (x - y)) := by
          rw [map_sub, map_sub]
        _ = Matrix.toLin' P
              (Matrix.toLin' T (Matrix.toLin' (1 - P) (x - y))) := by rw [hHidden]
        _ = 0 := by
          simpa [Matrix.toLin'_mul, Module.End.mul_eq_comp,
            LinearMap.comp_apply, Matrix.toLin'_apply] using hAtDifference
  constructor
  · have hSix :=
      deterministic_interface_sixfold_equivalence
        (fun x => Matrix.toLin' P x) (fun x => Matrix.toLin' T x)
    tfae_have 1 ↔ 2 := hSix.out 0 1
    tfae_have 2 ↔ 3 := hSix.out 1 2
    tfae_have 3 ↔ 4 := hSix.out 2 3
    tfae_have 4 ↔ 5 := hSix.out 3 4
    tfae_have 5 ↔ 6 := hSix.out 4 5
    tfae_have 6 ↔ 7 := (hSix.out 5 1).trans hInterface
    tfae_finish
  · intro hTHermitian
    constructor
    · intro hVisible
      have hHidden : (1 - P) * T * P = 0 := by
        have hStar := congrArg Matrix.conjTranspose hVisible
        simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
          Matrix.conjTranspose_one, hPHermitian.eq, hTHermitian.eq,
          Matrix.conjTranspose_zero, Matrix.mul_assoc] using hStar
      have hIdentity :=
        D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator_eq_cross_blocks
          P (1 - P) T rfl
      rw [hIdentity, hVisible, hHidden, sub_zero]
    · intro hComm
      have hPT : P * T = T * P := sub_eq_zero.mp hComm
      calc
        P * T * (1 - P) = T * P * (1 - P) := by rw [hPT]
        _ = T * (P * (1 - P)) := by rw [mul_assoc]
        _ = 0 := by rw [hPComplement, mul_zero]

#print axioms linear_projection_descent_criterion

end D5.S3.Observer.Dynamics.LinearProjectionDescentCriterion
