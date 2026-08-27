/- GID: D5/S3/Observer/Conditioning/TargetVisibilityConditionCost
   generality: G
   mirror-B: D5/B/S3/Observer/Conditioning/TargetVisibilityConditionCost
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact target visibility carries a canonical minimum-norm condition cost. -/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/- Library-search audit trail (2026-08-28):
   * D5 searches found adjacent observer frame, conditioning, tomography, and
     observable-span results, but no theorem combining fiberwise target
     visibility with its canonical minimum-norm adjoint certificate and cost.
   * Pinned Mathlib has no Moore--Penrose construction. Exact component hits
     `LinearMap.orthogonal_ker`, `LinearMap.range_adjoint_comp_self`,
     `LinearMap.ker_adjoint_comp_self`, and orthogonal decomposition supply the
     canonical certificate without introducing a substitute pseudoinverse.
   * Body-shape searches found no D5 primitive with this certificate signature.
     This module introduces no `def` or `abbrev`; the state Gramian is the
     constructed composite of the public measurement map and its adjoint. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Conditioning.TargetVisibilityConditionCost

open InnerProductSpace

/-- A target is constant on measurement fibers exactly when it has a unique
orthogonal normal-equation certificate. The induced observation coefficient is
the minimum-norm unbiased coefficient, and its squared norm is the target's
quadratic condition cost. -/
theorem target_visibility_condition_cost
    {K State Observation : Type*}
    [RCLike K]
    [NormedAddCommGroup State] [InnerProductSpace K State]
    [FiniteDimensional K State]
    [NormedAddCommGroup Observation] [InnerProductSpace K Observation]
    [FiniteDimensional K Observation]
    (measurement : State →ₗ[K] Observation) (target : State) :
    (∀ x y : State, measurement x = measurement y →
      inner K target x = inner K target y) ↔
      ∃! certificate : State × Observation,
        certificate.1 ∈ measurement.kerᗮ ∧
        measurement.adjoint certificate.2 = target ∧
        certificate.2 = measurement certificate.1 ∧
        (∀ coefficient : Observation,
          measurement.adjoint coefficient = target →
            ‖certificate.2‖ ≤ ‖coefficient‖) ∧
        ((‖certificate.2‖ ^ 2 : ℝ) : K) =
          inner K target certificate.1 := by
  constructor
  · intro visible
    have targetOrthogonal : target ∈ measurement.kerᗮ := by
      rw [Submodule.mem_orthogonal']
      intro hidden hiddenKernel
      have hiddenReadout : measurement hidden = measurement 0 := by
        simpa using LinearMap.mem_ker.mp hiddenKernel
      simpa using visible hidden 0 hiddenReadout
    have targetInGramRange :
        target ∈ (measurement.adjoint ∘ₗ measurement).range := by
      rw [measurement.range_adjoint_comp_self]
      rw [← measurement.orthogonal_ker]
      exact targetOrthogonal
    rcases targetInGramRange with ⟨initialState, initialNormal⟩
    letI := FiniteDimensional.complete K State
    rcases measurement.ker.exists_add_mem_mem_orthogonal initialState with
      ⟨hiddenPart, hiddenPartKernel, stateCertificate,
        stateCertificateOrthogonal, initialDecomposition⟩
    have stateNormal :
        measurement.adjoint (measurement stateCertificate) = target := by
      rw [initialDecomposition] at initialNormal
      simpa [LinearMap.mem_ker.mp hiddenPartKernel] using initialNormal
    have coefficientMinimal : ∀ coefficient : Observation,
        measurement.adjoint coefficient = target →
          ‖measurement stateCertificate‖ ≤ ‖coefficient‖ := by
      intro coefficient coefficientNormal
      have residualKernel :
          coefficient - measurement stateCertificate ∈ measurement.adjoint.ker := by
        rw [LinearMap.mem_ker]
        simp [coefficientNormal, stateNormal]
      have residualOrthogonal :
          coefficient - measurement stateCertificate ∈ measurement.rangeᗮ := by
        rw [measurement.orthogonal_range]
        exact residualKernel
      have coefficientSplit :
          coefficient = measurement stateCertificate +
            (coefficient - measurement stateCertificate) := by abel
      have splitOrthogonal : inner K (measurement stateCertificate)
          (coefficient - measurement stateCertificate) = 0 :=
        (Submodule.mem_orthogonal measurement.range
          (coefficient - measurement stateCertificate)).mp residualOrthogonal
            (measurement stateCertificate) ⟨stateCertificate, rfl⟩
      have squareLe : ‖measurement stateCertificate‖ ^ 2 ≤ ‖coefficient‖ ^ 2 := by
        rw [coefficientSplit,
          show ‖measurement stateCertificate +
              (coefficient - measurement stateCertificate)‖ ^ 2 =
            ‖measurement stateCertificate‖ ^ 2 +
              ‖coefficient - measurement stateCertificate‖ ^ 2 by
            simpa [pow_two] using
              norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
                (measurement stateCertificate)
                (coefficient - measurement stateCertificate) splitOrthogonal]
        exact le_add_of_nonneg_right (sq_nonneg _)
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp squareLe
    have conditionCost : ((‖measurement stateCertificate‖ ^ 2 : ℝ) : K) =
        inner K target stateCertificate := by
      rw [← stateNormal, measurement.adjoint_inner_left]
      simp [inner_self_eq_norm_sq_to_K]
    refine ⟨(stateCertificate, measurement stateCertificate), ?_, ?_⟩
    · exact ⟨stateCertificateOrthogonal, stateNormal, rfl,
        coefficientMinimal, conditionCost⟩
    · intro other otherProperties
      rcases otherProperties with
        ⟨otherOrthogonal, otherNormal, otherCoefficient, _, _⟩
      have otherStateNormal :
          measurement.adjoint (measurement other.1) = target := by
        rw [← otherCoefficient]
        exact otherNormal
      have stateDifferenceKernel : other.1 - stateCertificate ∈ measurement.ker := by
        rw [← measurement.ker_adjoint_comp_self, LinearMap.mem_ker]
        simp [otherStateNormal, stateNormal]
      have stateDifferenceOrthogonal :
          other.1 - stateCertificate ∈ measurement.kerᗮ :=
        measurement.kerᗮ.sub_mem otherOrthogonal stateCertificateOrthogonal
      have stateDifferenceZero : other.1 - stateCertificate = 0 := by
        rw [← inner_self_eq_zero (𝕜 := K)]
        exact (Submodule.mem_orthogonal measurement.ker
          (other.1 - stateCertificate)).mp stateDifferenceOrthogonal
            (other.1 - stateCertificate) stateDifferenceKernel
      have stateEqual : other.1 = stateCertificate := sub_eq_zero.mp stateDifferenceZero
      apply Prod.ext
      · exact stateEqual
      · simp [otherCoefficient, stateEqual]
  · rintro ⟨certificate, certificateProperties, _⟩
    rcases certificateProperties with ⟨_, coefficientNormal, _, _, _⟩
    intro x y sameReadout
    calc
      inner K target x = inner K (measurement.adjoint certificate.2) x := by
        rw [coefficientNormal]
      _ = inner K certificate.2 (measurement x) :=
        measurement.adjoint_inner_left x certificate.2
      _ = inner K certificate.2 (measurement y) := by rw [sameReadout]
      _ = inner K (measurement.adjoint certificate.2) y :=
        (measurement.adjoint_inner_left y certificate.2).symm
      _ = inner K target y := by rw [coefficientNormal]

#print axioms target_visibility_condition_cost

end D5.S3.Observer.Conditioning.TargetVisibilityConditionCost
