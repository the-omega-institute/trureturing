/- GID: D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicCMI
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicCMI
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Matched faithful three-qubit states obstruct continuity of both forward geodesic CMIs. -/

import D5.S3.Quantum.Information.GeodesicCMI.CapelCostaRicoForwardGeodesicBoundary
import D5.S3.Quantum.Information.GeodesicCMI.CapelCostaRicoGeodesicContinuity
import D5.S3.Quantum.Information.GeodesicCMI.CapelCostaRicoReverseGeodesicCMI
import Mathlib.Analysis.SpecificLimits.Basic

/-! The two forward deficits of (357) in Capel and Costa Rico,
*Geodesic Quantum f-Divergences*, arXiv:2608.15833v1. For #32416 the perturbation is
invisible to every two-body partial trace, while the forward CMI gap tends to log 2. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Information.GeodesicCMI.CapelCostaRicoForwardGeodesicCMI

open Matrix Set Filter
open scoped BigOperators ComplexOrder Kronecker Matrix MatrixOrder Matrix.Norms.L2Operator Topology
open D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState)
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceDistance)
open PartialTraceMutualInformation
  (partialTraceLeft partialTraceRight partialTraceLeft_kronecker partialTraceRight_kronecker)
open CapelCostaRicoForwardGeodesicDensity
open CapelCostaRicoForwardGeodesicBoundary
  (SMatrix_eq_diagonal referenceDiagonal geodesicRelativeEntropy_RMatrix_zero)
open CapelCostaRicoReverseGeodesicCMI
  (toMatrix marginalB diagReal geodesicRelativeEntropy geodesicRelativeEntropy_diagonal
    continuousOn_geodesicRelativeEntropy)

noncomputable section

/-- The actual C marginal, obtained by tracing B out of the BC marginal. -/
def marginalC (ρ : Matrix Triple Triple ℂ) : Matrix Bit Bit ℂ :=
  partialTraceLeft (marginalBC ρ)

/-- The one-sided forward deficit of equation (357), with reference `τC`. -/
def oneSidedCMI (t : ℝ) (τC : Matrix Bit Bit ℂ) (ρ : Matrix Triple Triple ℂ) : ℝ :=
  geodesicRelativeEntropy t ρ (marginalAB ρ ⊗ₖ τC) -
    geodesicRelativeEntropy t (marginalBC ρ) (marginalB ρ ⊗ₖ τC)

/-- The two-sided forward deficit uses the C marginal of its own input. -/
def twoSidedCMI (t : ℝ) (ρ : Matrix Triple Triple ℂ) : ℝ :=
  oneSidedCMI t (marginalC ρ) ρ

private theorem mixedBit_kronecker : mixedBit ⊗ₖ mixedBit = mixedPair := by
  simp only [mixedBit, mixedPair, smul_kronecker, kronecker_smul, one_kronecker_one,
    smul_smul] <;> norm_num

private theorem mixedBit_trace : mixedBit.trace = 1 := by
  norm_num [mixedBit, Matrix.trace_smul, Matrix.trace_one, Bit,
    RCLike.real_smul_eq_coe_mul (K := ℂ)]

private theorem marginalB_eq_partialTraceRight_marginalBC (ρ : Matrix Triple Triple ℂ) :
    marginalB ρ = partialTraceRight (marginalBC ρ) := by
  ext b b'
  change (∑ a : Bit, ∑ c : Bit, ρ ((a, b), c) ((a, b'), c)) =
    ∑ c : Bit, ∑ a : Bit, ρ ((a, b), c) ((a, b'), c)
  exact Finset.sum_comm

private theorem familyMatrix_marginalB (u w : ℝ) : marginalB (familyMatrix u w) = mixedBit := by
  rw [marginalB_eq_partialTraceRight_marginalBC, familyMatrix_marginalBC,
    ← mixedBit_kronecker]
  change partialTraceRight (Matrix.kronecker mixedBit mixedBit) = mixedBit
  rw [partialTraceRight_kronecker, mixedBit_trace, one_smul]

private theorem familyMatrix_marginalC (u w : ℝ) : marginalC (familyMatrix u w) = mixedBit := by
  rw [marginalC, familyMatrix_marginalBC, ← mixedBit_kronecker]
  change partialTraceLeft (Matrix.kronecker mixedBit mixedBit) = mixedBit
  rw [partialTraceLeft_kronecker, mixedBit_trace, one_smul]

private theorem geodesicRelativeEntropy_mixedPair_self (t : ℝ) :
    geodesicRelativeEntropy t mixedPair mixedPair = 0 := by
  have h : mixedPair = diagReal (fun _ : Pair => (1 / 4 : ℝ)) := by
    ext i j
    by_cases hij : i = j <;>
      simp [mixedPair, diagReal, Matrix.one_apply, Matrix.diagonal_apply, Matrix.smul_apply, hij,
        RCLike.real_smul_eq_coe_mul (K := ℂ)]
  rw [h, geodesicRelativeEntropy_diagonal t _ _ (fun _ => by norm_num) (fun _ => by norm_num)]
  norm_num

private theorem geodesicRelativeEntropy_SMatrix_self (t u : ℝ) (hu : 0 < u) (hhalf : u < 1 / 2) :
    geodesicRelativeEntropy t (SMatrix u) (SMatrix u) = 0 := by
  have h (i : Triple) : 0 < referenceDiagonal u i := by
    unfold referenceDiagonal
    split_ifs <;> linarith
  have hS : SMatrix u = diagReal (referenceDiagonal u) := SMatrix_eq_diagonal u
  rw [hS, geodesicRelativeEntropy_diagonal t _ _ h h]
  exact Finset.sum_eq_zero fun i _ => by rw [div_self (h i).ne', Real.log_one, mul_zero]

private theorem oneSidedCMI_familyMatrix (t u w : ℝ) :
    oneSidedCMI t mixedBit (familyMatrix u w) =
      geodesicRelativeEntropy t (familyMatrix u w) (SMatrix u) := by
  rw [oneSidedCMI, familyMatrix_marginalAB, familyMatrix_marginalBC, familyMatrix_marginalB,
    ← SMatrix_eq_product, mixedBit_kronecker, geodesicRelativeEntropy_mixedPair_self, sub_zero]

private theorem twoSidedCMI_familyMatrix (t u w : ℝ) :
    twoSidedCMI t (familyMatrix u w) =
      geodesicRelativeEntropy t (familyMatrix u w) (SMatrix u) := by
  rw [twoSidedCMI, familyMatrix_marginalC, oneSidedCMI_familyMatrix]

theorem continuous_RMatrix (u : ℝ) : Continuous (RMatrix u) := by
  have h : Continuous (fun η : ℝ =>
      (1 - η) • familyMatrix u (Real.sqrt (u * (1 - u))) + η • SMatrix u) := by
    fun_prop
  exact h.congr (fun η => (RMatrix_eq_mix u η).symm)

theorem RMatrix_posSemidef_of_mem_Icc {u η : ℝ} (hu : 0 < u) (hhalf : u < 1 / 2)
    (hη : η ∈ Icc (0 : ℝ) 1) : (RMatrix u η).PosSemidef := by
  rw [RMatrix_eq_mix]
  exact ((familyMatrix_endpoint_posSemidef hu hhalf).smul (sub_nonneg.mpr hη.2)).add
    ((SMatrix_posDef hu hhalf).posSemidef.smul hη.1)

theorem eventually_regularization_valid : ∀ᶠ η in 𝓝[>] (0 : ℝ), η ∈ Ioo (0 : ℝ) 1 := by
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
    (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with η hη₀ hη₁
  exact ⟨hη₀, hη₁⟩

theorem regularization_tendsto (t u : ℝ) (ht₀ : 0 < t) (ht₁ : t ≤ 1)
    (hu : 0 < u) (hhalf : u < 1 / 2) :
    Tendsto (fun η => geodesicRelativeEntropy t (RMatrix u η) (SMatrix u))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.log 2)) := by
  have hpsd := RMatrix_posSemidef_of_mem_Icc (η := 0) hu hhalf (by norm_num)
  have hpath : Tendsto (RMatrix u) (𝓝[>] (0 : ℝ))
      (𝓝[{r | r.PosSemidef}] (RMatrix u 0)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨(continuous_RMatrix u).continuousAt.tendsto.mono_left nhdsWithin_le_nhds,
        eventually_regularization_valid.mono fun _ h =>
          RMatrix_posSemidef_of_mem_Icc hu hhalf ⟨h.1.le, h.2.le⟩⟩
  have h := ((continuousOn_geodesicRelativeEntropy t ht₀.le ht₁ (SMatrix u))
      (RMatrix u 0) hpsd).tendsto.comp hpath
  change Tendsto (fun η => geodesicRelativeEntropy t (RMatrix u η) (SMatrix u))
    (𝓝[>] (0 : ℝ)) (𝓝 (geodesicRelativeEntropy t (RMatrix u 0) (SMatrix u))) at h
  simpa only [geodesicRelativeEntropy_RMatrix_zero hu hhalf ht₀ ht₁] using h

/-- Faithful pairs sharing AB at each index and having the same fixed B, AC and BC
throughout. The right-hand limit also records eventual strict positivity of the distance. -/
structure MatchedFaithfulPairs where
  ρ : ℕ → DensityState Triple
  σ : ℕ → DensityState Triple
  faithful : ∀ n, (toMatrix (ρ n)).PosDef ∧ (toMatrix (σ n)).PosDef
  sameAB : ∀ n, marginalAB (toMatrix (ρ n)) = marginalAB (toMatrix (σ n))
  fixedMarginals : ∀ n,
    marginalB (toMatrix (ρ n)) = mixedBit ∧ marginalB (toMatrix (σ n)) = mixedBit ∧
    marginalAC (toMatrix (ρ n)) = mixedPair ∧ marginalAC (toMatrix (σ n)) = mixedPair ∧
    marginalBC (toMatrix (ρ n)) = mixedPair ∧ marginalBC (toMatrix (σ n)) = mixedPair
  distance : Tendsto (fun n => traceDistance (ρ n) (σ n)) atTop (𝓝[>] (0 : ℝ))

/-- The signed gaps for both deficits converge to `log 2`. -/
def ForwardGap (p : MatchedFaithfulPairs) (t : ℝ) : Prop :=
  Tendsto (fun n => oneSidedCMI t mixedBit (toMatrix (p.ρ n)) -
    oneSidedCMI t mixedBit (toMatrix (p.σ n))) atTop (𝓝 (Real.log 2)) ∧
  Tendsto (fun n => twoSidedCMI t (toMatrix (p.ρ n)) -
    twoSidedCMI t (toMatrix (p.σ n))) atTop (𝓝 (Real.log 2))

/-- The same decreasing parameter is used for the reference and for the accuracy. -/
def sequenceParameter (n : ℕ) : ℝ := ((n : ℝ) + 3)⁻¹

theorem sequenceParameter_pos (n : ℕ) : 0 < sequenceParameter n := by
  unfold sequenceParameter
  positivity

theorem sequenceParameter_lt_half (n : ℕ) : sequenceParameter n < 1 / 2 := by
  unfold sequenceParameter
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [inv_eq_one_div, div_lt_div_iff₀ (by linarith : 0 < (n : ℝ) + 3) (by norm_num : (0 : ℝ) < 2)]
  linarith

theorem tendsto_sequenceParameter : Tendsto sequenceParameter atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_right _ 3 tendsto_natCast_atTop_atTop)

private theorem amplitude_pos {u η : ℝ} (hu : 0 < u) (hhalf : u < 1 / 2) (hη : η < 1) :
    0 < amplitude u η :=
  mul_pos (sub_pos.mpr hη) (Real.sqrt_pos.mpr (mul_pos hu (by linarith)))

private theorem amplitude_le_sqrt {u η : ℝ} (hu : 0 < u) (hη₀ : 0 < η) :
    amplitude u η ≤ Real.sqrt u :=
  (mul_le_of_le_one_left (Real.sqrt_nonneg _) (by linarith : 1 - η ≤ 1)).trans
    (Real.sqrt_le_sqrt (mul_le_of_le_one_right hu.le (by linarith)))

/-- The choices of regularization may depend on the index. The trace distance
converges to zero from above for every such choice. -/
def witnessPairs (η : ℕ → ℝ) (hη₀ : ∀ n, 0 < η n) (hη₁ : ∀ n, η n < 1) :
    MatchedFaithfulPairs where
  ρ n := R (sequenceParameter n) (η n) (sequenceParameter_pos n) (sequenceParameter_lt_half n)
    (hη₀ n) (hη₁ n)
  σ n := S (sequenceParameter n) (sequenceParameter_pos n) (sequenceParameter_lt_half n)
  faithful n :=
    ⟨RMatrix_posDef (sequenceParameter_pos n) (sequenceParameter_lt_half n) (hη₀ n) (hη₁ n),
      SMatrix_posDef (sequenceParameter_pos n) (sequenceParameter_lt_half n)⟩
  sameAB n := by
    change marginalAB (familyMatrix (sequenceParameter n) (amplitude (sequenceParameter n) (η n))) =
      marginalAB (familyMatrix (sequenceParameter n) 0)
    rw [familyMatrix_marginalAB, familyMatrix_marginalAB]
  fixedMarginals n :=
    ⟨familyMatrix_marginalB _ _, familyMatrix_marginalB _ _,
      familyMatrix_marginalAC _ _, familyMatrix_marginalAC _ _,
      familyMatrix_marginalBC _ _, familyMatrix_marginalBC _ _⟩
  distance := by
    have hpos n := amplitude_pos (sequenceParameter_pos n) (sequenceParameter_lt_half n) (hη₁ n)
    have hsqrt : Tendsto (fun n => Real.sqrt (sequenceParameter n)) atTop (𝓝 0) := by
      have h := Real.continuous_sqrt.continuousAt.tendsto.comp tendsto_sequenceParameter
      change Tendsto (fun n => Real.sqrt (sequenceParameter n)) atTop (𝓝 (Real.sqrt 0)) at h
      simpa only [Real.sqrt_zero] using h
    have hlim : Tendsto (fun n => amplitude (sequenceParameter n) (η n)) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨squeeze_zero (fun n => (hpos n).le)
            (fun n => amplitude_le_sqrt (sequenceParameter_pos n) (hη₀ n)) hsqrt,
          Eventually.of_forall hpos⟩
    refine hlim.congr (fun n => ?_)
    exact (traceDistance_R_S (sequenceParameter_pos n) (sequenceParameter_lt_half n)
      (hη₀ n) (hη₁ n)).symm

theorem witnessPairs_forwardGap (η : ℕ → ℝ) (hη₀ : ∀ n, 0 < η n) (hη₁ : ∀ n, η n < 1)
    (t : ℝ) (hlim : Tendsto
      (fun n => geodesicRelativeEntropy t (RMatrix (sequenceParameter n) (η n))
        (SMatrix (sequenceParameter n))) atTop (𝓝 (Real.log 2))) :
    ForwardGap (witnessPairs η hη₀ hη₁) t := by
  constructor <;> refine hlim.congr (fun n => ?_)
  · change _ = oneSidedCMI t mixedBit
        (familyMatrix (sequenceParameter n) (amplitude (sequenceParameter n) (η n))) -
      oneSidedCMI t mixedBit (familyMatrix (sequenceParameter n) 0)
    rw [oneSidedCMI_familyMatrix, oneSidedCMI_familyMatrix]
    change _ = geodesicRelativeEntropy t (RMatrix (sequenceParameter n) (η n))
      (SMatrix (sequenceParameter n)) -
        geodesicRelativeEntropy t (SMatrix (sequenceParameter n)) (SMatrix (sequenceParameter n))
    rw [geodesicRelativeEntropy_SMatrix_self t _ (sequenceParameter_pos n)
        (sequenceParameter_lt_half n), sub_zero]
  · change _ = twoSidedCMI t
        (familyMatrix (sequenceParameter n) (amplitude (sequenceParameter n) (η n))) -
      twoSidedCMI t (familyMatrix (sequenceParameter n) 0)
    rw [twoSidedCMI_familyMatrix, twoSidedCMI_familyMatrix]
    change _ = geodesicRelativeEntropy t (RMatrix (sequenceParameter n) (η n))
      (SMatrix (sequenceParameter n)) -
        geodesicRelativeEntropy t (SMatrix (sequenceParameter n)) (SMatrix (sequenceParameter n))
    rw [geodesicRelativeEntropy_SMatrix_self t _ (sequenceParameter_pos n)
        (sequenceParameter_lt_half n), sub_zero]

/-- For each fixed positive parameter, both native forward gaps stay bounded
away from zero on pairs of arbitrarily close faithful states with matched marginals. -/
theorem exists_pointwise (t : ℝ) (ht₀ : 0 < t) (ht₁ : t ≤ 1) :
    ∃ p : MatchedFaithfulPairs, ForwardGap p t := by
  have h (n : ℕ) : ∃ η : ℝ, 0 < η ∧ η < 1 ∧
      dist (geodesicRelativeEntropy t (RMatrix (sequenceParameter n) η)
        (SMatrix (sequenceParameter n))) (Real.log 2) < sequenceParameter n := by
    have hsmall := (Metric.tendsto_nhds.mp
      (regularization_tendsto t (sequenceParameter n) ht₀ ht₁
        (sequenceParameter_pos n) (sequenceParameter_lt_half n)))
      (sequenceParameter n) (sequenceParameter_pos n)
    obtain ⟨η, hη, hηsmall⟩ := (eventually_regularization_valid.and hsmall).exists
    exact ⟨η, hη.1, hη.2, hηsmall⟩
  choose η hη₀ hη₁ hη using h
  refine ⟨witnessPairs η hη₀ hη₁, witnessPairs_forwardGap η hη₀ hη₁ t ?_⟩
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [tendsto_sequenceParameter.eventually (Iio_mem_nhds hε)] with n hn
  exact (hη n).trans hn

end

end D5.S3.Quantum.Information.GeodesicCMI.CapelCostaRicoForwardGeodesicCMI
