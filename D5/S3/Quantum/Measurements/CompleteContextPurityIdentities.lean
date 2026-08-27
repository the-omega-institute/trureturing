/- GID: D5/S3/Quantum/Measurements/CompleteContextPurityIdentities
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurements/CompleteContextPurityIdentities
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Complete complementary contexts split purity exactly into probability coordinates. -/

import D5.S3.Quantum.Tomography.PurityPythagorasDecomposition
import D5.S3.Quantum.Tomography.CompleteContextTomography

/- Library-search audit trail (2026-08-27):
   * Exact repository hit `purity_pythagoras_decomposition` supplies the centered-probability
     identity with its canonical residual and is applied directly below.
   * Exact family primitives `RankOneContext`, `PairwiseOrthogonalMeasurements`, `visibleMatrix`,
     and `basisProbability` encode the source contexts without a sibling fork. Exact hit
     `complete_context_tomography` derives reconstruction from the complementary-overlap law.
   * Repository and pinned-Mathlib searches found no theorem stating both complete-context
     probability identities. `complementary_context_probability_pythagoras` retains a residual
     term and does not state the uncentered square identity. -/

open scoped BigOperators ComplexOrder InnerProductSpace Matrix

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Measurements.CompleteContextPurityIdentities

open D5.S3.Observer.Conditioning
open D5.S3.Quantum.Measurement.BasisMeasurementProjection
open D5.S3.Quantum.Tomography.CompleteContextTomography
open D5.S3.Quantum.Tomography.PurityPythagorasDecomposition
open D5.S3.Quantum.Tomography.RankOneContextCommutator

attribute [local instance]
  D5.S3.Quantum.Measurement.BasisMeasurementProjection.matrixNormedAddCommGroup
  D5.S3.Quantum.Measurement.BasisMeasurementProjection.matrixComplexInnerProductSpace
  D5.S3.Quantum.Measurement.BasisMeasurementProjection.matrixRealInnerProductSpace

set_option maxHeartbeats 1000000 in
-- Expanding the complementary-context reconstruction requires nested finite matrix sums.
/-- For a complete family of pairwise complementary rank-one measurements, the centered Born
probability energy equals purity excess, and the uncentered squared probabilities sum to one
plus purity. Projection completeness is derived from the public complementary-overlap law. -/
theorem complete_context_purity_identities
    {n : Nat}
    (context : Fin (n + 2) -> RankOneContext (n + 1))
    (hRecord : forall l, IsRecordMeasurement (context l).projector)
    (hOverlap : forall l k j r,
      Matrix.trace ((context l).projector j * (context k).projector r) =
        if l = k then (if j = r then 1 else 0) else ((n + 1 : Nat) : ℂ)⁻¹)
    (rho : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hrho : rho.PosSemidef ∧ Matrix.trace rho = 1) :
    (∑ l, ∑ j,
        (basisProbability rho (context l) j - ((n + 1 : Nat) : ℝ)⁻¹) ^ 2 =
      (Matrix.trace (rho * rho)).re - ((n + 1 : Nat) : ℝ)⁻¹) ∧
    (∑ l, ∑ j, basisProbability rho (context l) j ^ 2 =
      1 + (Matrix.trace (rho * rho)).re) := by
  classical
  have hMeasurementExpansion (l : Fin (n + 2))
      (state : traceZeroHermitian (n + 1)) :
      (traceZeroBasisMeasurement (context l) (hRecord l) state).1.1 =
        ∑ j, Matrix.trace ((context l).projector j * state.1.1) •
          (context l).projector j := by
    change unreadState (context l).projector state.1.1 = _
    rw [unreadState]
    apply Finset.sum_congr rfl
    intro j _
    exact ((context l).rankOne j).2.2.2 state.1.1
  have hTraceSum (l : Fin (n + 2)) (state : traceZeroHermitian (n + 1)) :
      ∑ j, Matrix.trace ((context l).projector j * state.1.1) = 0 := by
    calc
      ∑ j, Matrix.trace ((context l).projector j * state.1.1) =
          Matrix.trace ((∑ j, (context l).projector j) * state.1.1) := by
        rw [Finset.sum_mul, Matrix.trace_sum]
      _ = 0 := by rw [(context l).resolvesIdentity, Matrix.one_mul, state.2]
  have hMatrixInner
      (A C : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
      inner ℂ A C = Matrix.trace (Aᴴ * C) := by
    change Matrix.trace (C * 1 * Aᴴ) = Matrix.trace (Aᴴ * C)
    rw [Matrix.mul_one, Matrix.trace_mul_comm]
  have hProjectorInner (l k : Fin (n + 2)) (j r : Fin (n + 1)) :
      inner ℂ ((context l).projector j) ((context k).projector r) =
        Matrix.trace ((context l).projector j * (context k).projector r) := by
    rw [hMatrixInner, ((context l).rankOne j).1]
  have hComplementary : PairwiseOrthogonalMeasurements context hRecord := by
    intro l k hlk x y
    rw [hMeasurementExpansion l x, hMeasurementExpansion k y]
    change (inner ℂ
      (∑ j, Matrix.trace ((context l).projector j * x.1.1) •
        (context l).projector j)
      (∑ r, Matrix.trace ((context k).projector r * y.1.1) •
        (context k).projector r)).re = 0
    have hComplexZero : inner ℂ
        (∑ j, Matrix.trace ((context l).projector j * x.1.1) •
          (context l).projector j)
        (∑ r, Matrix.trace ((context k).projector r * y.1.1) •
          (context k).projector r) = 0 := by
      rw [sum_inner]
      apply Finset.sum_eq_zero
      intro j _
      rw [inner_sum]
      calc
        ∑ r, inner ℂ
            (Matrix.trace ((context l).projector j * x.1.1) •
              (context l).projector j)
            (Matrix.trace ((context k).projector r * y.1.1) •
              (context k).projector r) =
            ∑ r, (starRingEnd ℂ)
              (Matrix.trace ((context l).projector j * x.1.1)) *
              Matrix.trace ((context k).projector r * y.1.1) *
                (((n + 1 : Nat) : ℂ)⁻¹) := by
          apply Finset.sum_congr rfl
          intro r _
          rw [inner_smul_left, inner_smul_right,
            hProjectorInner, hOverlap, if_neg hlk]
          ac_rfl
        _ = (starRingEnd ℂ)
              (Matrix.trace ((context l).projector j * x.1.1)) *
              (∑ r, Matrix.trace ((context k).projector r * y.1.1)) *
                (((n + 1 : Nat) : ℂ)⁻¹) := by
          rw [Finset.mul_sum, Finset.sum_mul]
        _ = 0 := by rw [hTraceSum k y]; simp
    simpa using congrArg Complex.re hComplexZero
  have hComplete (state : traceZeroHermitian (n + 1)) :
      visibleMatrix context hRecord state = state.1.1 := by
    have hHermitian : state.1.1ᴴ = state.1.1 := by
      have hStar := state.1.2
      change star state.1.1 = state.1.1 at hStar
      simpa only [Matrix.star_eq_conjTranspose] using hStar
    obtain ⟨coefficient, hCoefficientProperties, _⟩ :=
      (complete_context_tomography context hOverlap).1 state.1.1 hHermitian state.2
    rcases hCoefficientProperties with ⟨hCentered, hReconstruct⟩
    have hCoefficient (k : Fin (n + 2)) (r : Fin (n + 1)) :
        Matrix.trace ((context k).projector r * state.1.1) =
          (coefficient k r : ℂ) := by
      rw [hReconstruct, Matrix.mul_sum, Matrix.trace_sum]
      simp_rw [Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_smul,
        Matrix.trace_smul, smul_eq_mul]
      have hContext (l : Fin (n + 2)) :
          ∑ j, (coefficient l j : ℂ) *
              Matrix.trace ((context k).projector r * (context l).projector j) =
            if l = k then coefficient k r else 0 := by
        by_cases hlk : l = k
        · subst l
          simp [hOverlap]
        · have hkl : k ≠ l := Ne.symm hlk
          simp only [hOverlap k l, hkl, hlk, if_false]
          rw [← Finset.sum_mul]
          have hCast : ∑ j, (coefficient l j : ℂ) = 0 := by
            exact_mod_cast hCentered l
          rw [hCast, zero_mul]
          norm_num
      calc
        ∑ l, ∑ j, (coefficient l j : ℂ) *
              Matrix.trace ((context k).projector r * (context l).projector j) =
            ∑ l, (((if l = k then coefficient k r else 0 : ℝ)) : ℂ) := by
          apply Finset.sum_congr rfl
          intro l _
          exact hContext l
        _ = (coefficient k r : ℂ) := by
          rw [← Complex.ofReal_sum]
          simp
    calc
      visibleMatrix context hRecord state =
          ∑ l, ∑ j, Matrix.trace ((context l).projector j * state.1.1) •
            (context l).projector j := by
        unfold visibleMatrix
        apply Finset.sum_congr rfl
        intro l _
        exact hMeasurementExpansion l state
      _ = ∑ l, ∑ j, (coefficient l j : ℂ) • (context l).projector j := by
        apply Finset.sum_congr rfl
        intro l _
        apply Finset.sum_congr rfl
        intro j _
        rw [hCoefficient]
      _ = state.1.1 := hReconstruct.symm
  have hResidual :
      purityResidual context hRecord (centeredDensity rho hrho) = 0 := by
    rw [purityResidual, residualVector, hComplete]
    simp
  have hCentered :=
    purity_pythagoras_decomposition context hRecord rho hrho hComplementary
  rw [hResidual, add_zero] at hCentered
  have hFirst :
      (∑ l, ∑ j,
          (basisProbability rho (context l) j - ((n + 1 : Nat) : ℝ)⁻¹) ^ 2) =
        (Matrix.trace (rho * rho)).re - ((n + 1 : Nat) : ℝ)⁻¹ :=
    hCentered.symm
  have hProbabilitySum (l : Fin (n + 2)) :
      ∑ j, basisProbability rho (context l) j = 1 := by
    unfold basisProbability
    rw [← Complex.re_sum]
    calc
      (∑ j, Matrix.trace (rho * (context l).projector j)).re =
          (Matrix.trace (rho * ∑ j, (context l).projector j)).re := by
        rw [Matrix.mul_sum, Matrix.trace_sum]
      _ = 1 := by rw [(context l).resolvesIdentity, Matrix.mul_one, hrho.2]; norm_num
  have hCenteredExpansion :
      (∑ l, ∑ j,
          (basisProbability rho (context l) j - ((n + 1 : Nat) : ℝ)⁻¹) ^ 2) =
        (∑ l, ∑ j, basisProbability rho (context l) j ^ 2) -
          ((n + 2 : Nat) : ℝ) * ((n + 1 : Nat) : ℝ)⁻¹ := by
    calc
      (∑ l, ∑ j,
          (basisProbability rho (context l) j - ((n + 1 : Nat) : ℝ)⁻¹) ^ 2) =
          ∑ l, ((∑ j, basisProbability rho (context l) j ^ 2) -
            2 * ((n + 1 : Nat) : ℝ)⁻¹ *
              (∑ j, basisProbability rho (context l) j) +
            ((n + 1 : Nat) : ℝ) * (((n + 1 : Nat) : ℝ)⁻¹) ^ 2) := by
        apply Finset.sum_congr rfl
        intro l _
        calc
          (∑ j, (basisProbability rho (context l) j -
              ((n + 1 : Nat) : ℝ)⁻¹) ^ 2) =
              ∑ j, (basisProbability rho (context l) j ^ 2 -
                2 * ((n + 1 : Nat) : ℝ)⁻¹ *
                  basisProbability rho (context l) j +
                (((n + 1 : Nat) : ℝ)⁻¹) ^ 2) := by
            apply Finset.sum_congr rfl
            intro j _
            ring
          _ = (∑ j, basisProbability rho (context l) j ^ 2) -
              2 * ((n + 1 : Nat) : ℝ)⁻¹ *
                (∑ j, basisProbability rho (context l) j) +
              ((n + 1 : Nat) : ℝ) * (((n + 1 : Nat) : ℝ)⁻¹) ^ 2 := by
            simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
              ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
              Fintype.card_fin, nsmul_eq_mul]
      _ = ∑ l, ((∑ j, basisProbability rho (context l) j ^ 2) -
            ((n + 1 : Nat) : ℝ)⁻¹) := by
        apply Finset.sum_congr rfl
        intro l _
        rw [hProbabilitySum]
        field_simp [show ((n + 1 : Nat) : ℝ) ≠ 0 by positivity]
        ring
      _ = (∑ l, ∑ j, basisProbability rho (context l) j ^ 2) -
          ((n + 2 : Nat) : ℝ) * ((n + 1 : Nat) : ℝ)⁻¹ := by
        rw [Finset.sum_sub_distrib]
        simp
  refine ⟨hFirst, ?_⟩
  rw [hCenteredExpansion] at hFirst
  have hd : ((n + 1 : Nat) : ℝ) * ((n + 1 : Nat) : ℝ)⁻¹ = 1 := by
    field_simp [show ((n + 1 : Nat) : ℝ) ≠ 0 by positivity]
  have hCard : ((n + 2 : Nat) : ℝ) * ((n + 1 : Nat) : ℝ)⁻¹ =
      1 + ((n + 1 : Nat) : ℝ)⁻¹ := by
    have hCastSucc : ((n + 2 : Nat) : ℝ) = ((n + 1 : Nat) : ℝ) + 1 := by
      push_cast
      ring
    rw [hCastSucc, add_mul, hd, one_mul]
  linarith

#print axioms complete_context_purity_identities

end D5.S3.Quantum.Measurements.CompleteContextPurityIdentities
