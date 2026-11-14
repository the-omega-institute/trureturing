/- GID: D5/S3/Quantum/Divergence/FaithfulConditionalGap
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/FaithfulConditionalGap
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Squared trace distance separates complete and conditional contraction coefficients. -/

import D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability
import D5.S3.Quantum.Information.ChenKatoBrandaoTraceNormCMIRefutation

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Quantum.Divergence.FaithfulConditionalGap

open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
open D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability

/-- A finite real-valued divergence, with heterogeneous quantum data processing. -/
structure FiniteDivergence where
  value : ∀ {n : Type} [Fintype n] [DecidableEq n], DensityState n → DensityState n → ℝ
  nonnegative : ∀ {n : Type} [Fintype n] [DecidableEq n] (ρ σ : DensityState n),
    0 ≤ value ρ σ
  faithful : ∀ {n : Type} [Fintype n] [DecidableEq n] (ρ σ : DensityState n),
    value ρ σ = 0 ↔ ρ = σ
  dataProcessing : ∀ {a b : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (N : QuantumChannel a b) (ρ σ : DensityState a),
    value (N.mapState ρ) (N.mapState σ) ≤ value ρ σ

private theorem positive_trace_contraction
    {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (f : Matrix a a ℂ →ₗ[ℂ] Matrix b b ℂ)
    (hpos : ∀ X, 0 ≤ X → 0 ≤ f X)
    (htr : ∀ X, Matrix.trace (f X) = Matrix.trace X)
    (X : Matrix a a ℂ) (hX : X.IsHermitian) : traceNorm (f X) ≤ traceNorm X := by
  have hn (Y : Matrix a a ℂ) (hY : 0 ≤ Y) :
      traceNorm (f Y) = (Matrix.trace Y).re := by
    have h := congrArg Complex.re
      (traceNorm_of_posSemidef (Matrix.nonneg_iff_posSemidef.mp (hpos Y hY)))
    simpa only [Complex.ofReal_re, htr] using h
  rw [← CFC.posPart_sub_negPart X hX, map_sub, sub_eq_add_neg]
  calc
    traceNorm (f (posPart X) + -f (negPart X)) ≤
        traceNorm (f (posPart X)) + traceNorm (-f (negPart X)) := traceNorm_add_le _ _
    _ = traceNorm X := by
      rw [traceNorm_neg, hn _ (CFC.posPart_nonneg X), hn _ (CFC.negPart_nonneg X)]
      exact (trace_norm_jordan_mass X hX).symm

private theorem traceNorm_zero {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) : traceNorm X = 0 ↔ X = 0 := by
  constructor
  · intro h
    have hp := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Xᴴ * X))
    have hi := (Complex.nonneg_iff.mp hp.trace_nonneg).2
    have hz : (CFC.sqrt (Xᴴ * X)).trace = 0 := Complex.ext h hi.symm
    exact CFC.abs_eq_zero_iff.mp (hp.trace_eq_zero_iff.mp hz)
  · rintro rfl
    simp [traceNorm]

private theorem state_hermitian {n : Type*} [Fintype n] [DecidableEq n]
    (ρ : DensityState n) : (CStarMatrix.ofMatrix.symm ρ.1).IsHermitian :=
  (Matrix.nonneg_iff_posSemidef.mp
    (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm ρ.2.1)).isHermitian

private theorem traceDistance_faithful {n : Type*} [Fintype n] [DecidableEq n]
    (ρ σ : DensityState n) : traceDistance ρ σ = 0 ↔ ρ = σ := by
  constructor
  · intro h
    have hz : traceNorm (CStarMatrix.ofMatrix.symm ρ.1 -
        CStarMatrix.ofMatrix.symm σ.1) = 0 := by
      unfold traceDistance at h
      linarith
    have he := sub_eq_zero.mp ((traceNorm_zero _).mp hz)
    apply Subtype.ext
    exact CStarMatrix.ofMatrix.symm.injective he
  · rintro rfl
    simp [traceDistance, traceNorm]

private theorem traceDistance_heterogeneous
    {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (N : QuantumChannel a b) (ρ σ : DensityState a) :
    traceDistance (N.mapState ρ) (N.mapState σ) ≤ traceDistance ρ σ := by
  let f : Matrix a a ℂ →ₗ[ℂ] Matrix b b ℂ :=
    CStarMatrix.ofMatrixₗ.symm.toLinearMap.comp
      (N.toCompletelyPositiveMap.toLinearMap.comp CStarMatrix.ofMatrixₗ.toLinearMap)
  have hp : ∀ X, 0 ≤ X → 0 ≤ f X := by
    intro X hX
    exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm
      (map_nonneg N.toCompletelyPositiveMap
        (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hX))
  have ht : ∀ X, Matrix.trace (f X) = Matrix.trace X :=
    fun X => N.trace_preserving (CStarMatrix.ofMatrix X)
  have hc := positive_trace_contraction f hp ht
    (CStarMatrix.ofMatrix.symm ρ.1 - CStarMatrix.ofMatrix.symm σ.1)
    ((state_hermitian ρ).sub (state_hermitian σ))
  have he : f (CStarMatrix.ofMatrix.symm ρ.1 - CStarMatrix.ofMatrix.symm σ.1) =
      CStarMatrix.ofMatrix.symm (N.mapState ρ).1 -
        CStarMatrix.ofMatrix.symm (N.mapState σ).1 := by
    rw [map_sub]
    rfl
  rw [he] at hc
  exact div_le_div_of_nonneg_right hc (by norm_num)

private def squareTrace : FiniteDivergence where
  value ρ σ := traceDistance ρ σ ^ 2
  nonnegative ρ σ := sq_nonneg _
  faithful ρ σ := by rw [sq_eq_zero_iff, traceDistance_faithful]
  dataProcessing N ρ σ := by
    exact pow_le_pow_left₀ (traceDistance_nonneg _ _)
      (traceDistance_heterogeneous N ρ σ) 2

/-- Complete ratios range over every finite quantum reference. -/
def completeRatios {a b : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (D : FiniteDivergence) (N : QuantumChannel a b) : Set ℝ :=
  {x | ∃ (r : Type) (fr : Fintype r) (dr : DecidableEq r),
    letI := fr
    letI := dr
    ∃ ρ σ : DensityState (r × a),
      marginalRight ρ = marginalRight σ ∧ 0 < D.value ρ σ ∧
      x = D.value (referenceState N ρ) (referenceState N σ) / D.value ρ σ}

/-- Squaring is performed before subtracting the marginal divergence. -/
def conditionalRatios {a b : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (D : FiniteDivergence) (N : QuantumChannel a b) : Set ℝ :=
  {x | ∃ (r : Type) (fr : Fintype r) (dr : DecidableEq r),
    letI := fr
    letI := dr
    ∃ ρ σ : DensityState (r × a),
      0 < D.value ρ σ - D.value (marginalRight ρ) (marginalRight σ) ∧
      x = (D.value (referenceState N ρ) (referenceState N σ) -
        D.value (marginalRight ρ) (marginalRight σ)) /
          (D.value ρ σ - D.value (marginalRight ρ) (marginalRight σ))}

def completeCoefficient {a b : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (D : FiniteDivergence) (N : QuantumChannel a b) : ℝ :=
  sSup (insert 0 (completeRatios D N))

def conditionalCoefficient {a b : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (D : FiniteDivergence) (N : QuantumChannel a b) : ℝ :=
  sSup (insert 0 (conditionalRatios D N))

end D5.S3.Quantum.Divergence.FaithfulConditionalGap
