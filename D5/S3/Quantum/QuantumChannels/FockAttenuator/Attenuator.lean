/- GID: D5/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/FockAttenuator/Attenuator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Attenuator on the full bosonic Hilbert space. -/
/-
coherent_output_covariance:
  proof_shape: content
  escape_witness: Conclusion witness: a summable double-index rank-one ensemble identity for arbitrary environment weights, connecting the reduced displaced input to conjugation of the vacuum output.
admission_basis: escape-witness
Direct frozen dependencies: none on the immutable origin/dev baseline.
Chain prerequisite (first freeze in Stage B): DisplacementCovariance.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S3.Quantum.QuantumChannels.FockAttenuator.DisplacementCovariance
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal NNReal ComplexOrder
open Filter Topology
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
namespace D5.S3.Quantum.QuantumChannels.FockAttenuator.Attenuator
open D5.S3.Quantum.QuantumChannels.FockAttenuator.DisplacementCovariance D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter

structure ProbabilityVector where
  weight : ℕ → ℝ
  nonneg : ∀ n, 0 ≤ weight n
  normalized : HasSum weight 1

structure DensityOperator where
  operator : (lp (fun _ : ℕ => ℂ) 2) →L[ℂ] (lp (fun _ : ℕ => ℂ) 2)
  positive : operator.IsPositive
  trace_one : HasSum (fun n : ℕ => (inner ℂ ((fun n : ℕ => lp.single (E := fun _ : ℕ => ℂ) 2 n (1 : ℂ)) n) (operator ((fun n : ℕ => lp.single (E := fun _ : ℕ => ℂ) 2 n (1 : ℂ)) n))).re) 1

def outputVector (η : ℝ) (hη : η ∈ Set.Icc (0 : ℝ) 1)
    (p : ProbabilityVector) (ρ : DensityOperator) (q : ℕ × ℕ × ℕ) : (lp (fun _ : ℕ => ℂ) 2) := by
  letI : Nontrivial (lp (fun _ : ℕ => ℂ) 2) := ⟨⟨lp.single 2 0 1, 0, by
    intro h
    have hc := congrArg (fun v : lp (fun _ : ℕ => ℂ) 2 => v 0) h
    simpa [lp.single_apply] using hc⟩⟩
  letI : IsometricContinuousFunctionalCalculus ℝ
      ((lp (fun _ : ℕ => ℂ) 2) →L[ℂ] (lp (fun _ : ℕ => ℂ) 2)) IsSelfAdjoint :=
    IsSelfAdjoint.instIsometricContinuousFunctionalCalculus
  letI : NonUnitalIsometricContinuousFunctionalCalculus ℝ
      ((lp (fun _ : ℕ => ℂ) 2) →L[ℂ] (lp (fun _ : ℕ => ℂ) 2)) IsSelfAdjoint :=
    IsSelfAdjoint.instNonUnitalIsometricContinuousFunctionalCalculus
  let h_FockAttTwoMode_fock (n : ℕ) : (lp (fun _ : ℕ => ℂ) 2) := lp.single 2 n 1
  exact (Real.sqrt (p.weight q.1) : ℂ) •
      (beamSplitter η hη (tensor (CFC.sqrt ρ.operator (h_FockAttTwoMode_fock q.2.1)) (h_FockAttTwoMode_fock q.1))) q.2.2

def attenuatorOperator (η : ℝ) (hη : η ∈ Set.Icc (0 : ℝ) 1)
    (p : ProbabilityVector) (ρ : DensityOperator) : (lp (fun _ : ℕ => ℂ) 2) →L[ℂ] (lp (fun _ : ℕ => ℂ) 2) := by
  exact mixture (outputVector η hη p ρ)

def attenuator (η : ℝ) (hη : η ∈ Set.Icc (0 : ℝ) 1)
    (p : ProbabilityVector) (ρ : DensityOperator) : DensityOperator := by
  letI : Nontrivial (lp (fun _ : ℕ => ℂ) 2) := ⟨⟨lp.single 2 0 1, 0, by
    intro h
    have hc := congrArg (fun v : lp (fun _ : ℕ => ℂ) 2 => v 0) h
    simpa [lp.single_apply] using hc⟩⟩
  letI : IsometricContinuousFunctionalCalculus ℝ
      ((lp (fun _ : ℕ => ℂ) 2) →L[ℂ] (lp (fun _ : ℕ => ℂ) 2)) IsSelfAdjoint :=
    IsSelfAdjoint.instIsometricContinuousFunctionalCalculus
  letI : NonUnitalIsometricContinuousFunctionalCalculus ℝ
      ((lp (fun _ : ℕ => ℂ) 2) →L[ℂ] (lp (fun _ : ℕ => ℂ) 2)) IsSelfAdjoint :=
    IsSelfAdjoint.instNonUnitalIsometricContinuousFunctionalCalculus
  have h_FockAttMixture_rankOne_summable {ι : Type} (v : ι → (lp (fun _ : ℕ => ℂ) 2)) (hv : Summable (fun i => ‖v i‖ ^ 2)) :
      Summable (fun i => InnerProductSpace.rankOne ℂ (v i) (v i)) := by
    apply Summable.of_norm
    simpa only [InnerProductSpace.norm_rankOne, ← sq] using hv
  let h_FockAttTwoMode_fock (n : ℕ) : (lp (fun _ : ℕ => ℂ) 2) := lp.single 2 n 1
  have h_FockAttMixture_fock_quadratic_rankOne (v : (lp (fun _ : ℕ => ℂ) 2)) (n : ℕ) :
      (inner ℂ (h_FockAttTwoMode_fock n) (InnerProductSpace.rankOne ℂ v v (h_FockAttTwoMode_fock n))).re = ‖v n‖ ^ 2 := by
    simp only [InnerProductSpace.rankOne_apply, inner_smul_right, h_FockAttTwoMode_fock,
      lp.inner_single_left, lp.inner_single_right]
    simp only [RCLike.inner_apply, map_one, one_mul, mul_one, RCLike.conj_mul]
    norm_cast
  have h_FockAttMixture_mixture_fock_quadratic {ι : Type} (v : ι → (lp (fun _ : ℕ => ℂ) 2))
      (hv : Summable (fun i => ‖v i‖ ^ 2)) (n : ℕ) :
      (inner ℂ (h_FockAttTwoMode_fock n) (mixture v (h_FockAttTwoMode_fock n))).re = ∑' i, ‖v i n‖ ^ 2 := by
    let φ : ((lp (fun _ : ℕ => ℂ) 2) →L[ℂ] (lp (fun _ : ℕ => ℂ) 2)) →L[ℝ] ℝ :=
      Complex.reCLM.comp (((innerSL ℂ (h_FockAttTwoMode_fock n)).comp
        (ContinuousLinearMap.apply ℂ (lp (fun _ : ℕ => ℂ) 2) (h_FockAttTwoMode_fock n))).restrictScalars ℝ)
    have hs := (h_FockAttMixture_rankOne_summable v hv).hasSum.mapL φ
    have heq : ∀ T : (lp (fun _ : ℕ => ℂ) 2) →L[ℂ] (lp (fun _ : ℕ => ℂ) 2), φ T =
        (inner ℂ (h_FockAttTwoMode_fock n) (T (h_FockAttTwoMode_fock n))).re := fun T => rfl
    simpa only [heq, h_FockAttMixture_fock_quadratic_rankOne, mixture] using hs.tsum_eq.symm
  have h_FockAttMixture_mixture_trace {ι : Type} (v : ι → (lp (fun _ : ℕ => ℂ) 2)) (hv : Summable (fun i => ‖v i‖ ^ 2)) :
      HasSum (fun n : ℕ => (inner ℂ (h_FockAttTwoMode_fock n) (mixture v (h_FockAttTwoMode_fock n))).re)
        (∑' i, ‖v i‖ ^ 2) := by
    have hi (i : ι) : HasSum (fun n => ‖v i n‖ ^ 2) (‖v i‖ ^ 2) := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) (v i)
    have hjoint : Summable (fun q : ι × ℕ => ‖v q.1 q.2‖ ^ 2) := by
      rw [summable_prod_of_nonneg (fun q => sq_nonneg _)]
      exact ⟨fun i => (hi i).summable, by simpa only [(hi _).tsum_eq] using hv⟩
    have hs := hjoint.tsum_comm' (fun i => (hi i).summable)
      (fun n => ((summable_prod_of_nonneg (fun q : ℕ × ι => sq_nonneg (‖v q.2 q.1‖))).mp
        hjoint.prod_symm).1 n)
    have hout : Summable (fun n : ℕ => ∑' i, ‖v i n‖ ^ 2) :=
      (summable_prod_of_nonneg (fun q : ℕ × ι => sq_nonneg (‖v q.2 q.1‖))).mp
        hjoint.prod_symm |>.2
    have heq : (∑' n : ℕ, ∑' i, ‖v i n‖ ^ 2) = ∑' i, ‖v i‖ ^ 2 := by
      rw [hs]
      exact tsum_congr (fun i => (hi i).tsum_eq)
    simpa only [h_FockAttMixture_mixture_fock_quadratic v hv, heq] using hout.hasSum
  have h_FockAttMixture_mixture_positive {ι : Type} (v : ι → (lp (fun _ : ℕ => ℂ) 2)) (hv : Summable (fun i => ‖v i‖ ^ 2)) :
      (mixture v).IsPositive := by
    apply (ContinuousLinearMap.nonneg_iff_isPositive (f := _)).mp
    apply tsum_nonneg
    intro i
    exact (ContinuousLinearMap.nonneg_iff_isPositive (f := _)).mpr
      (InnerProductSpace.isPositive_rankOne_self (v i))
  have h_FockAttTwoMode_tensor_apply (v w : (lp (fun _ : ℕ => ℂ) 2)) (n : ℕ) : tensor v w n = w n • v := rfl
  have h_FockAttTwoMode_tensor_norm_sq (v w : (lp (fun _ : ℕ => ℂ) 2)) : ‖tensor v w‖ ^ 2 = ‖v‖ ^ 2 * ‖w‖ ^ 2 := by
    have ht := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) (tensor v w)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at ht
    have hw := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) w
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hw
    rw [ht]
    simp only [h_FockAttTwoMode_tensor_apply, norm_smul, mul_pow]
    rw [hw.summable.tsum_mul_right, hw.tsum_eq, mul_comm]
  have h_FockAttChannel_outputVector_slice_hasSum (η : ℝ) (hη : η ∈ Set.Icc (0 : ℝ) 1)
      (p : ProbabilityVector) (ρ : DensityOperator) (n m : ℕ) :
      HasSum (fun l => ‖outputVector η hη p ρ (n,m,l)‖ ^ 2)
        (p.weight n * ‖CFC.sqrt ρ.operator (h_FockAttTwoMode_fock m)‖ ^ 2) := by
    let w := beamSplitter η hη (tensor (CFC.sqrt ρ.operator (h_FockAttTwoMode_fock m)) (h_FockAttTwoMode_fock n))
    have hs := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) w
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hs
    have hn : ‖w‖ ^ 2 = ‖CFC.sqrt ρ.operator (h_FockAttTwoMode_fock m)‖ ^ 2 := by
      change ‖beamSplitter η hη (tensor (CFC.sqrt ρ.operator (h_FockAttTwoMode_fock m)) (h_FockAttTwoMode_fock n))‖ ^ 2 = _
      rw [LinearIsometryEquiv.norm_map, h_FockAttTwoMode_tensor_norm_sq]
      simp [h_FockAttTwoMode_fock, lp.norm_single]
    rw [hn] at hs
    have hsqrt : ‖(Real.sqrt (p.weight n) : ℂ)‖ ^ 2 = p.weight n := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt (p.nonneg n)]
    apply HasSum.congr_fun (hs.mul_left (p.weight n))
    intro l
    simp only [outputVector, norm_smul, mul_pow, hsqrt]
    rfl
  have h_FockAttChannel_densitySqrt_squared (ρ : DensityOperator) : CFC.sqrt ρ.operator * CFC.sqrt ρ.operator = ρ.operator := CFC.sqrt_mul_sqrt_self ρ.operator
      ((ContinuousLinearMap.nonneg_iff_isPositive (f := _)).mpr ρ.positive)
  have h_FockAttChannel_densitySqrt_selfAdjoint (ρ : DensityOperator) : IsSelfAdjoint (CFC.sqrt ρ.operator) := (CFC.sqrt_nonneg ρ.operator).isSelfAdjoint
  have h_FockAttChannel_densitySqrt_norm_sq (ρ : DensityOperator) (v : (lp (fun _ : ℕ => ℂ) 2)) :
      ‖CFC.sqrt ρ.operator v‖ ^ 2 = (inner ℂ v (ρ.operator v)).re := by
    have hs := (h_FockAttChannel_densitySqrt_selfAdjoint ρ).isSymmetric v (CFC.sqrt ρ.operator v)
    have hprod : CFC.sqrt ρ.operator (CFC.sqrt ρ.operator v) = ρ.operator v := by
      exact congrArg (fun T : (lp (fun _ : ℕ => ℂ) 2) →L[ℂ] (lp (fun _ : ℕ => ℂ) 2) => T v) (h_FockAttChannel_densitySqrt_squared ρ)
    change inner ℂ (CFC.sqrt ρ.operator v) (CFC.sqrt ρ.operator v) =
      inner ℂ v (CFC.sqrt ρ.operator (CFC.sqrt ρ.operator v)) at hs
    rw [hprod, inner_self_eq_norm_sq_to_K] at hs
    have hr := congrArg Complex.re hs
    norm_cast at hr
  have h_FockAttChannel_densitySqrt_hasSum (ρ : DensityOperator) :
      HasSum (fun m : ℕ => ‖CFC.sqrt ρ.operator (h_FockAttTwoMode_fock m)‖ ^ 2) 1 := HasSum.congr_fun ρ.trace_one (fun m => h_FockAttChannel_densitySqrt_norm_sq ρ (h_FockAttTwoMode_fock m))
  have h_FockAttChannel_outputVector_hasSum (η : ℝ) (hη : η ∈ Set.Icc (0 : ℝ) 1)
      (p : ProbabilityVector) (ρ : DensityOperator) :
      HasSum (fun q : ℕ × ℕ × ℕ => ‖outputVector η hη p ρ q‖ ^ 2) 1 := by
    have hs := h_FockAttChannel_outputVector_slice_hasSum η hη p ρ
    have hn (n : ℕ) : Summable (fun q : ℕ × ℕ => ‖outputVector η hη p ρ (n,q)‖ ^ 2) := by
      rw [summable_prod_of_nonneg (fun q => sq_nonneg _)]
      refine ⟨fun m => (hs n m).summable, ?_⟩
      simp_rw [(hs n _).tsum_eq]
      exact (h_FockAttChannel_densitySqrt_hasSum ρ).summable.mul_left (p.weight n)
    have hnt (n : ℕ) : (∑' q : ℕ × ℕ, ‖outputVector η hη p ρ (n,q)‖ ^ 2) = p.weight n := by
      rw [(hn n).tsum_prod]
      simp_rw [(hs n _).tsum_eq]
      rw [(h_FockAttChannel_densitySqrt_hasSum ρ).summable.tsum_mul_left, (h_FockAttChannel_densitySqrt_hasSum ρ).tsum_eq,
        mul_one]
    have hall : Summable (fun q : ℕ × ℕ × ℕ => ‖outputVector η hη p ρ q‖ ^ 2) := by
      rw [summable_prod_of_nonneg (fun q => sq_nonneg _)]
      refine ⟨hn, ?_⟩
      simpa only [hnt] using p.normalized.summable
    have ht : (∑' q : ℕ × ℕ × ℕ, ‖outputVector η hη p ρ q‖ ^ 2) = 1 := by
      rw [hall.tsum_prod]
      simp_rw [hnt]
      exact p.normalized.tsum_eq
    exact ht ▸ hall.hasSum
  exact {
    operator := attenuatorOperator η hη p ρ
    positive := h_FockAttMixture_mixture_positive _ (h_FockAttChannel_outputVector_hasSum η hη p ρ).summable
    trace_one := by
      have hs := h_FockAttChannel_outputVector_hasSum η hη p ρ
      simpa only [hs.tsum_eq, h_FockAttTwoMode_fock, h_FockAttTwoMode_fock, attenuatorOperator] using
        h_FockAttMixture_mixture_trace _ hs.summable
  }

def pureDensity (v : (lp (fun _ : ℕ => ℂ) 2)) (hv : ‖v‖ = 1) : DensityOperator := by
  let h_FockAttTwoMode_fock (n : ℕ) : (lp (fun _ : ℕ => ℂ) 2) := lp.single 2 n 1
  have h_FockAttMixture_fock_quadratic_rankOne (v : (lp (fun _ : ℕ => ℂ) 2)) (n : ℕ) :
      (inner ℂ (h_FockAttTwoMode_fock n) (InnerProductSpace.rankOne ℂ v v (h_FockAttTwoMode_fock n))).re = ‖v n‖ ^ 2 := by
    simp only [InnerProductSpace.rankOne_apply, inner_smul_right, h_FockAttTwoMode_fock,
      lp.inner_single_left, lp.inner_single_right]
    simp only [RCLike.inner_apply, map_one, one_mul, mul_one, RCLike.conj_mul]
    norm_cast
  exact {
    operator := InnerProductSpace.rankOne ℂ v v
    positive := InnerProductSpace.isPositive_rankOne_self v
    trace_one := by
      have hs := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) v
      simp only [ENNReal.toReal_ofNat, Real.rpow_two, hv, one_pow] at hs
      exact HasSum.congr_fun hs (fun n => by
        simpa only [h_FockAttTwoMode_fock, h_FockAttTwoMode_fock] using h_FockAttMixture_fock_quadratic_rankOne v n)
  }

def pureOutputVector (η : ℝ) (hη : η ∈ Set.Icc (0 : ℝ) 1)
    (p : ProbabilityVector) (v : (lp (fun _ : ℕ => ℂ) 2)) (q : ℕ × ℕ) : (lp (fun _ : ℕ => ℂ) 2) := by
  let h_FockAttTwoMode_fock (n : ℕ) : (lp (fun _ : ℕ => ℂ) 2) := lp.single 2 n 1
  exact (Real.sqrt (p.weight q.1) : ℂ) •
      (beamSplitter η hη (tensor v (h_FockAttTwoMode_fock q.1))) q.2

def pureAttenuatorOperator (η : ℝ) (hη : η ∈ Set.Icc (0 : ℝ) 1)
    (p : ProbabilityVector) (v : (lp (fun _ : ℕ => ℂ) 2)) : (lp (fun _ : ℕ => ℂ) 2) →L[ℂ] (lp (fun _ : ℕ => ℂ) 2) := by
  exact mixture (pureOutputVector η hη p v)

theorem coherent_output_covariance (η : ℝ) (hη : η ∈ Set.Icc (0 : ℝ) 1)
    (p : ProbabilityVector) (α : ℂ) :
    pureAttenuatorOperator η hη p (displacement α ((fun n : ℕ => lp.single (E := fun _ : ℕ => ℂ) 2 n (1 : ℂ)) 0)) =
      LinearIsometryEquiv.conjStarAlgEquiv (displacement ((Real.sqrt η : ℂ) * α))
        (pureAttenuatorOperator η hη p ((fun n : ℕ => lp.single (E := fun _ : ℕ => ℂ) 2 n (1 : ℂ)) 0)) := by
  have exponential_vectors_total (v : (lp (fun _ : ℕ => ℂ) 2))
      (hv : ∀ α : ℂ, inner ℂ v (exponentialVector α) = 0) : v = 0 := by
    let h_FockAttCoherentBridge_scalarSeries (v : (lp (fun _ : ℕ => ℂ) 2)) : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ (fun n =>
        (starRingEnd ℂ) (v n) / (Real.sqrt (n.factorial : ℝ) : ℂ))
    have h_FockAttCoherentBridge_scalarSeries_expansion (v : (lp (fun _ : ℕ => ℂ) 2)) :
        HasFPowerSeriesAt (fun z : ℂ => inner ℂ v (exponentialVector z)) (h_FockAttCoherentBridge_scalarSeries v) 0 := by
      apply hasFPowerSeriesAt_iff.mpr
      filter_upwards [] with z
      simp only [zero_add]
      apply HasSum.congr_fun (lp.hasSum_inner v (exponentialVector z))
      intro n
      simp only [h_FockAttCoherentBridge_scalarSeries, FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul,
        exponentialVector, exponentialCoeff, RCLike.inner_apply]
      ring
    have hfun : (fun z : ℂ => inner ℂ v (exponentialVector z)) = 0 := funext hv
    have hs := h_FockAttCoherentBridge_scalarSeries_expansion v
    rw [hfun] at hs
    have hzero := hs.eq_zero
    apply lp.ext
    funext n
    have hc := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) hzero
    simp only [h_FockAttCoherentBridge_scalarSeries, FormalMultilinearSeries.coeff_ofScalars] at hc
    change (starRingEnd ℂ) (v n) / (Real.sqrt (n.factorial : ℝ) : ℂ) = 0 at hc
    have hsqrt : (Real.sqrt (n.factorial : ℝ) : ℂ) ≠ 0 := by
      norm_cast
      exact (Real.sqrt_pos.mpr (by positivity : 0 < (n.factorial : ℝ))).ne'
    have hvn : (starRingEnd ℂ) (v n) = 0 := (div_eq_zero_iff.mp hc).resolve_right hsqrt
    simpa using hvn
  have exponentialPair_total (v : (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2))
      (hv : ∀ z : ℂ × ℂ, inner ℂ v (exponentialPair z) = 0) : v = 0 := by
    let h_FockAttTwoMode_pairScalarSeries (v : (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2)) (α : ℂ) : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ (fun n =>
        inner ℂ (v n) (exponentialVector α) / (Real.sqrt (n.factorial : ℝ) : ℂ))
    have h_FockAttTwoMode_tensor_apply (v w : (lp (fun _ : ℕ => ℂ) 2)) (n : ℕ) : tensor v w n = w n • v := rfl
    have h_FockAttTwoMode_pairScalarSeries_expansion (v : (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2)) (α : ℂ) :
        HasFPowerSeriesAt (fun z : ℂ => inner ℂ v (exponentialPair (α,z)))
          (h_FockAttTwoMode_pairScalarSeries v α) 0 := by
      apply hasFPowerSeriesAt_iff.mpr
      filter_upwards [] with z
      simp only [zero_add]
      apply HasSum.congr_fun (lp.hasSum_inner v (exponentialPair (α,z)))
      intro n
      simp only [h_FockAttTwoMode_pairScalarSeries, FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul,
        exponentialPair, h_FockAttTwoMode_tensor_apply, exponentialVector, exponentialCoeff, inner_smul_right]
      ring
    apply lp.ext
    funext n
    apply exponential_vectors_total
    intro α
    have hfun : (fun z : ℂ => inner ℂ v (exponentialPair (α,z))) = 0 :=
      funext (fun z => hv (α,z))
    have hs := h_FockAttTwoMode_pairScalarSeries_expansion v α
    rw [hfun] at hs
    have hc := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) hs.eq_zero
    simp only [h_FockAttTwoMode_pairScalarSeries, FormalMultilinearSeries.coeff_ofScalars] at hc
    change inner ℂ (v n) (exponentialVector α) / (Real.sqrt (n.factorial : ℝ) : ℂ) = 0 at hc
    have hsqrt : (Real.sqrt (n.factorial : ℝ) : ℂ) ≠ 0 := by
      norm_cast
      exact (Real.sqrt_pos.mpr (by positivity : 0 < (n.factorial : ℝ))).ne'
    exact (div_eq_zero_iff.mp hc).resolve_right hsqrt

  let h_FockAttChannelCovariance_conjugateL (U : (lp (fun _ : ℕ => ℂ) 2) ≃ₗᵢ[ℂ] (lp (fun _ : ℕ => ℂ) 2)) :
      ((lp (fun _ : ℕ => ℂ) 2) →L[ℂ] (lp (fun _ : ℕ => ℂ) 2)) →L[ℂ] ((lp (fun _ : ℕ => ℂ) 2) →L[ℂ] (lp (fun _ : ℕ => ℂ) 2)) := (ContinuousLinearMap.compL ℂ (lp (fun _ : ℕ => ℂ) 2) (lp (fun _ : ℕ => ℂ) 2) (lp (fun _ : ℕ => ℂ) 2)
        U.toContinuousLinearEquiv.toContinuousLinearMap).comp
      ((ContinuousLinearMap.compL ℂ (lp (fun _ : ℕ => ℂ) 2) (lp (fun _ : ℕ => ℂ) 2) (lp (fun _ : ℕ => ℂ) 2)).flip
        U.symm.toContinuousLinearEquiv.toContinuousLinearMap)
  have h_FockAttMixture_rankOne_summable {ι : Type} (v : ι → (lp (fun _ : ℕ => ℂ) 2)) (hv : Summable (fun i => ‖v i‖ ^ 2)) :
      Summable (fun i => InnerProductSpace.rankOne ℂ (v i) (v i)) := by
    apply Summable.of_norm
    simpa only [InnerProductSpace.norm_rankOne, ← sq] using hv
  have h_FockAttTwoMode_tensor_apply (v w : (lp (fun _ : ℕ => ℂ) 2)) (n : ℕ) : tensor v w n = w n • v := rfl
  have h_FockAttTwoMode_tensor_norm_sq (v w : (lp (fun _ : ℕ => ℂ) 2)) : ‖tensor v w‖ ^ 2 = ‖v‖ ^ 2 * ‖w‖ ^ 2 := by
    have ht := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) (tensor v w)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at ht
    have hw := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) w
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hw
    rw [ht]
    simp only [h_FockAttTwoMode_tensor_apply, norm_smul, mul_pow]
    rw [hw.summable.tsum_mul_right, hw.tsum_eq, mul_comm]
  let h_FockAttTwoMode_fock (n : ℕ) : (lp (fun _ : ℕ => ℂ) 2) := lp.single 2 n 1
  have h_FockAttChannel_pureOutputVector_hasSum (η : ℝ) (hη : η ∈ Set.Icc (0 : ℝ) 1)
      (p : ProbabilityVector) (v : (lp (fun _ : ℕ => ℂ) 2)) (hv : ‖v‖ = 1) :
      HasSum (fun q : ℕ × ℕ => ‖pureOutputVector η hη p v q‖ ^ 2) 1 := by
    have hrow (n : ℕ) : HasSum (fun l => ‖pureOutputVector η hη p v (n,l)‖ ^ 2)
        (p.weight n) := by
      let w := beamSplitter η hη (tensor v (h_FockAttTwoMode_fock n))
      have hs := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) w
      simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hs
      have hn : ‖w‖ ^ 2 = 1 := by
        change ‖beamSplitter η hη (tensor v (h_FockAttTwoMode_fock n))‖ ^ 2 = _
        rw [LinearIsometryEquiv.norm_map, h_FockAttTwoMode_tensor_norm_sq, hv]
        simp [h_FockAttTwoMode_fock, lp.norm_single]
      rw [hn] at hs
      have hsqrt : ‖(Real.sqrt (p.weight n) : ℂ)‖ ^ 2 = p.weight n := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
          Real.sq_sqrt (p.nonneg n)]
      have hs' := HasSum.congr_fun (hs.mul_left (p.weight n)) (fun l => by
        change ‖pureOutputVector η hη p v (n,l)‖ ^ 2 = p.weight n * ‖w l‖ ^ 2
        simp only [pureOutputVector, norm_smul, mul_pow, hsqrt]
        rfl)
      simpa only [mul_one] using hs'
    have hall : Summable (fun q : ℕ × ℕ => ‖pureOutputVector η hη p v q‖ ^ 2) := by
      rw [summable_prod_of_nonneg (fun q => sq_nonneg _)]
      refine ⟨fun n => (hrow n).summable, ?_⟩
      simpa only [(hrow _).tsum_eq] using p.normalized.summable
    have ht : (∑' q : ℕ × ℕ, ‖pureOutputVector η hη p v q‖ ^ 2) = 1 := by
      rw [hall.tsum_prod]
      simpa only [(hrow _).tsum_eq] using p.normalized.tsum_eq
    exact ht ▸ hall.hasSum
  have h_FockAttChannel_rankOne_smul_self (c : ℂ) (v : (lp (fun _ : ℕ => ℂ) 2)) :
      InnerProductSpace.rankOne ℂ (c • v) (c • v) =
        (‖c‖ ^ 2 : ℝ) • InnerProductSpace.rankOne ℂ v v := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [InnerProductSpace.rankOne_apply, inner_smul_left, smul_smul, smul_apply]
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rw [smul_smul]
    change ((starRingEnd ℂ) c * inner ℂ v x * c) • v =
      (((‖c‖ ^ 2 : ℝ) : ℂ) * inner ℂ v x) • v
    congr 1
    calc
      _ = ((starRingEnd ℂ) c * c) * inner ℂ v x := by ring
      _ = _ := by rw [RCLike.conj_mul]; norm_cast
  have h_FockAttChannel_pureAttenuator_environment (η : ℝ) (hη : η ∈ Set.Icc (0 : ℝ) 1)
      (p : ProbabilityVector) (v : (lp (fun _ : ℕ => ℂ) 2)) (hv : ‖v‖ = 1) :
      pureAttenuatorOperator η hη p v =
        ∑' n, p.weight n • purePartialTrace (beamSplitter η hη (tensor v (h_FockAttTwoMode_fock n))) := by
    have hall := h_FockAttMixture_rankOne_summable _ (h_FockAttChannel_pureOutputVector_hasSum η hη p v hv).summable
    unfold pureAttenuatorOperator mixture
    rw [hall.tsum_prod]
    apply tsum_congr
    intro n
    let w := beamSplitter η hη (tensor v (h_FockAttTwoMode_fock n))
    have hw := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) w
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hw
    have hrank := h_FockAttMixture_rankOne_summable (fun l => w l) hw.summable
    have hsqrt : ‖(Real.sqrt (p.weight n) : ℂ)‖ ^ 2 = p.weight n := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt (p.nonneg n)]
    change (∑' l, InnerProductSpace.rankOne ℂ
      ((Real.sqrt (p.weight n) : ℂ) • w l) ((Real.sqrt (p.weight n) : ℂ) • w l)) =
      p.weight n • mixture (fun l => w l)
    simp_rw [h_FockAttChannel_rankOne_smul_self, hsqrt]
    exact hrank.tsum_const_smul (p.weight n)
  have h_FockAttChannelCovariance_purePartialTrace_norm_le (w : (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2)) : ‖purePartialTrace w‖ ≤ ‖w‖ ^ 2 := by
    have hw := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) w
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hw
    have hn : Summable (fun n => ‖InnerProductSpace.rankOne ℂ (w n) (w n)‖) := by
      simpa only [InnerProductSpace.norm_rankOne, ← sq] using hw.summable
    unfold purePartialTrace mixture
    calc
      _ ≤ ∑' n, ‖InnerProductSpace.rankOne ℂ (w n) (w n)‖ := norm_tsum_le_tsum_norm hn
      _ = ‖w‖ ^ 2 := by
        simpa only [InnerProductSpace.norm_rankOne, ← sq] using hw.tsum_eq
  have h_FockAttChannelCovariance_environment_operators_summable (η : ℝ) (hη : η ∈ Set.Icc (0 : ℝ) 1)
      (p : ProbabilityVector) (v : (lp (fun _ : ℕ => ℂ) 2)) (hv : ‖v‖ = 1) :
      Summable (fun n => p.weight n • purePartialTrace (beamSplitter η hη (tensor v (h_FockAttTwoMode_fock n)))) := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _ p.normalized.summable
    intro n
    have ht := h_FockAttChannelCovariance_purePartialTrace_norm_le (beamSplitter η hη (tensor v (h_FockAttTwoMode_fock n)))
    have hn : ‖beamSplitter η hη (tensor v (h_FockAttTwoMode_fock n))‖ ^ 2 = 1 := by
      rw [LinearIsometryEquiv.norm_map, h_FockAttTwoMode_tensor_norm_sq, hv]
      simp [h_FockAttTwoMode_fock, lp.norm_single]
    rw [hn] at ht
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (p.nonneg n)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left ht (p.nonneg n)
  let h_FockAttPartialTrace_sliceVector (x : (lp (fun _ : ℕ => ℂ) 2)) (w : (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2)) : (lp (fun _ : ℕ => ℂ) 2) := ⟨fun n => inner ℂ x (w n), by
      apply memℓp_gen
      simp only [ENNReal.toReal_ofNat, Real.rpow_two]
      have hw := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) w
      simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hw
      apply Summable.of_nonneg_of_le (fun n => sq_nonneg _) _ (hw.summable.mul_left (‖x‖ ^ 2))
      intro n
      have h := norm_inner_le_norm (𝕜 := ℂ) x (w n)
      nlinarith [norm_nonneg (inner ℂ x (w n)), norm_nonneg x, norm_nonneg (w n)]⟩
  have h_FockAttPartialTrace_sliceVector_apply (x : (lp (fun _ : ℕ => ℂ) 2)) (w : (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2)) (n : ℕ) :
      h_FockAttPartialTrace_sliceVector x w n = inner ℂ x (w n) := rfl
  have h_FockAttPartialTrace_sliceVector_norm (x : (lp (fun _ : ℕ => ℂ) 2)) (w : (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2)) :
      ‖h_FockAttPartialTrace_sliceVector x w‖ ≤ ‖x‖ * ‖w‖ := by
    have hs := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) (h_FockAttPartialTrace_sliceVector x w)
    have hw := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) w
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hs hw
    have hle : ‖h_FockAttPartialTrace_sliceVector x w‖ ^ 2 ≤ ‖x‖ ^ 2 * ‖w‖ ^ 2 := by
      rw [hs, ← hw.tsum_eq, ← hw.summable.tsum_mul_left]
      apply Summable.tsum_le_tsum _
        (by simpa only [h_FockAttPartialTrace_sliceVector_apply, ENNReal.toReal_ofNat, Real.rpow_two] using
          (lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) (h_FockAttPartialTrace_sliceVector x w)).summable)
        (hw.summable.mul_left (‖x‖ ^ 2))
      intro n
      simp only [h_FockAttPartialTrace_sliceVector_apply]
      have h := norm_inner_le_norm (𝕜 := ℂ) x (w n)
      nlinarith [norm_nonneg (inner ℂ x (w n)), norm_nonneg x, norm_nonneg (w n)]
    nlinarith [norm_nonneg (h_FockAttPartialTrace_sliceVector x w), norm_nonneg x, norm_nonneg w,
      mul_nonneg (norm_nonneg x) (norm_nonneg w)]
  let h_FockAttPartialTrace_sliceMap (x : (lp (fun _ : ℕ => ℂ) 2)) : (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2) →L[ℂ] (lp (fun _ : ℕ => ℂ) 2) := LinearMap.mkContinuous
      { toFun := h_FockAttPartialTrace_sliceVector x
        map_add' := by intro w v; apply lp.ext; funext n; exact inner_add_right _ _ _
        map_smul' := by intro c w; apply lp.ext; funext n; exact inner_smul_right _ _ _ }
      ‖x‖ (fun w => by change ‖h_FockAttPartialTrace_sliceVector x w‖ ≤ _; exact h_FockAttPartialTrace_sliceVector_norm x w)
  have h_FockAttCovariance_twoMode_ext_slices (v w : (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2))
      (h : ∀ x : (lp (fun _ : ℕ => ℂ) 2), h_FockAttPartialTrace_sliceMap x v = h_FockAttPartialTrace_sliceMap x w) :
      v = w := by
    apply lp.ext
    funext n
    apply ext_inner_left ℂ
    intro x
    exact congrArg (fun z : (lp (fun _ : ℕ => ℂ) 2) => z n) (h x)
  have h_FockAttTwoMode_exponentialPair_dense :
      DenseRange (Finsupp.linearCombination ℂ exponentialPair) := by
    have hspan : (Submodule.span ℂ (Set.range exponentialPair)).topologicalClosure = ⊤ := by
      apply Submodule.topologicalClosure_eq_top_iff.mpr
      apply le_antisymm
      · intro v hv
        have hzero : v = 0 := exponentialPair_total v (fun α => by
          have hmem : exponentialPair α ∈ Submodule.span ℂ (Set.range exponentialPair) :=
            Submodule.subset_span ⟨α, rfl⟩
          exact Submodule.inner_left_of_mem_orthogonal hmem hv)
        simp [hzero]
      · exact bot_le
    rw [← Finsupp.range_linearCombination] at hspan
    change Dense (Set.range (Finsupp.linearCombination ℂ exponentialPair))
    rw [dense_iff_closure_eq]
    simpa only [Submodule.topologicalClosure_coe, Submodule.top_coe, LinearMap.coe_range] using
      congrArg (fun K : Submodule ℂ (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2) => (K : Set (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2))) hspan
  have h_FockAttTwoMode_tensor_norm (v w : (lp (fun _ : ℕ => ℂ) 2)) : ‖tensor v w‖ = ‖v‖ * ‖w‖ := by
    have hs := h_FockAttTwoMode_tensor_norm_sq v w
    nlinarith [norm_nonneg (tensor v w), norm_nonneg v, norm_nonneg w,
      mul_nonneg (norm_nonneg v) (norm_nonneg w)]
  let h_FockAttTwoMode_tensorLeft (w : (lp (fun _ : ℕ => ℂ) 2)) : (lp (fun _ : ℕ => ℂ) 2) →L[ℂ] (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2) := LinearMap.mkContinuous
      { toFun := fun v => tensor v w
        map_add' := by intro v v'; apply lp.ext; funext n; exact smul_add (w n) v v'
        map_smul' := by
          intro c v; apply lp.ext; funext n
          exact smul_comm (w n) c v }
      ‖w‖ (fun v => by change ‖tensor v w‖ ≤ _; rw [h_FockAttTwoMode_tensor_norm, mul_comm])
  have h_FockAttTwoMode_tensor_smul_left (c : ℂ) (v w : (lp (fun _ : ℕ => ℂ) 2)) : tensor (c • v) w = c • tensor v w := (h_FockAttTwoMode_tensorLeft w).map_smul c v
  let h_FockAttTwoMode_tensorRight (v : (lp (fun _ : ℕ => ℂ) 2)) : (lp (fun _ : ℕ => ℂ) 2) →L[ℂ] (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2) := LinearMap.mkContinuous
      { toFun := fun w => tensor v w
        map_add' := by intro w w'; apply lp.ext; funext n; exact add_smul (w n) (w' n) v
        map_smul' := by
          intro c w; apply lp.ext; funext n
          exact mul_smul c (w n) v }
      ‖v‖ (fun w => by change ‖tensor v w‖ ≤ _; rw [h_FockAttTwoMode_tensor_norm])
  have h_FockAttTwoMode_tensor_smul_right (c : ℂ) (v w : (lp (fun _ : ℕ => ℂ) 2)) : tensor v (c • w) = c • tensor v w := (h_FockAttTwoMode_tensorRight v).map_smul c w
  have h_FockAttCovariance_pairWeyl_dense (a : ℂ × ℂ) :
      DenseRange (Finsupp.linearCombination ℂ (pairWeyl a)) := by
    have hspan : (Submodule.span ℂ (Set.range (pairWeyl a))).topologicalClosure = ⊤ := by
      apply Submodule.topologicalClosure_eq_top_iff.mpr
      apply le_antisymm
      · intro v hv
        have hzero : v = 0 := exponentialPair_total v (fun z => by
          have hmem : pairWeyl a (z.1-a.1,z.2-a.2) ∈ Submodule.span ℂ (Set.range (pairWeyl a)) :=
            Submodule.subset_span ⟨(z.1-a.1,z.2-a.2), rfl⟩
          have hi := Submodule.inner_left_of_mem_orthogonal hmem hv
          have h1 : a.1 + (z.1-a.1) = z.1 := by ring
          have h2 : a.2 + (z.2-a.2) = z.2 := by ring
          simp only [pairWeyl, weylVector, h_FockAttTwoMode_tensor_smul_left, h_FockAttTwoMode_tensor_smul_right,
            inner_smul_right, h1, h2] at hi
          exact (mul_eq_zero.mp ((mul_eq_zero.mp hi).resolve_left (Complex.exp_ne_zero _))).resolve_left
            (Complex.exp_ne_zero _))
        simp [hzero]
      · exact bot_le
    rw [← Finsupp.range_linearCombination] at hspan
    change Dense (Set.range (Finsupp.linearCombination ℂ (pairWeyl a)))
    rw [dense_iff_closure_eq]
    simpa only [Submodule.topologicalClosure_coe, Submodule.top_coe, LinearMap.coe_range] using
      congrArg (fun K : Submodule ℂ (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2) => (K : Set (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2))) hspan
  let h_FockAttFrameExtension_gramUnitary {ι H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (v w : ι → H)
      (hgram : ∀ i j, inner ℂ (w i) (w j) = inner ℂ (v i) (v j))
      (hv : DenseRange (Finsupp.linearCombination ℂ v))
      (hw : DenseRange (Finsupp.linearCombination ℂ w)) : H ≃ₗᵢ[ℂ] H := (LinearEquiv.refl ℂ (ι →₀ ℂ)).extendOfIsometry
      (Finsupp.linearCombination ℂ v) (Finsupp.linearCombination ℂ w) hv hw (by
        intro c
        change ‖Finsupp.linearCombination ℂ w c‖ = ‖Finsupp.linearCombination ℂ v c‖
        have hs : inner ℂ (Finsupp.linearCombination ℂ w c) (Finsupp.linearCombination ℂ w c) =
            inner ℂ (Finsupp.linearCombination ℂ v c) (Finsupp.linearCombination ℂ v c) := by
          classical
          simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
            inner_smul_left, inner_smul_right, hgram]
        rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hs
        have hsq : ‖Finsupp.linearCombination ℂ w c‖ ^ 2 =
            ‖Finsupp.linearCombination ℂ v c‖ ^ 2 := by exact_mod_cast hs
        nlinarith [norm_nonneg (Finsupp.linearCombination ℂ w c),
          norm_nonneg (Finsupp.linearCombination ℂ v c)])
  have h_FockAttFrameExtension_gramUnitary_apply {ι H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (v w : ι → H)
      (hgram : ∀ i j, inner ℂ (w i) (w j) = inner ℂ (v i) (v j))
      (hv : DenseRange (Finsupp.linearCombination ℂ v))
      (hw : DenseRange (Finsupp.linearCombination ℂ w)) (i : ι) :
      h_FockAttFrameExtension_gramUnitary v w hgram hv hw (v i) = w i := by
    have hh := LinearEquiv.extendOfIsometry_eq (LinearEquiv.refl ℂ (ι →₀ ℂ))
      (Finsupp.linearCombination ℂ v) (Finsupp.linearCombination ℂ w) hv hw
      (by
        intro c
        change ‖Finsupp.linearCombination ℂ w c‖ = ‖Finsupp.linearCombination ℂ v c‖
        have hs : inner ℂ (Finsupp.linearCombination ℂ w c) (Finsupp.linearCombination ℂ w c) =
            inner ℂ (Finsupp.linearCombination ℂ v c) (Finsupp.linearCombination ℂ v c) := by
          classical
          simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
            inner_smul_left, inner_smul_right, hgram]
        rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hs
        have hsq : ‖Finsupp.linearCombination ℂ w c‖ ^ 2 =
            ‖Finsupp.linearCombination ℂ v c‖ ^ 2 := by exact_mod_cast hs
        nlinarith [norm_nonneg (Finsupp.linearCombination ℂ w c),
          norm_nonneg (Finsupp.linearCombination ℂ v c)]) (Finsupp.single i (1 : ℂ))
    simpa only [LinearEquiv.refl_apply, Finsupp.linearCombination_single, one_smul, h_FockAttFrameExtension_gramUnitary] using hh
  have h_FockAttTwoMode_tensor_inner (v w v' w' : (lp (fun _ : ℕ => ℂ) 2)) :
      inner ℂ (tensor v w) (tensor v' w') = inner ℂ v v' * inner ℂ w w' := by
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum w w']
    simp only [h_FockAttTwoMode_tensor_apply, inner_smul_left, inner_smul_right, RCLike.inner_apply]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    ring
  have h_FockAttCoherentBridge_exponentialCoeff_inner (α β : ℂ) (n : ℕ) :
      inner ℂ (exponentialCoeff α n) (exponentialCoeff β n) =
        ((starRingEnd ℂ) α * β) ^ n / (n.factorial : ℂ) := by
    have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have hs : Real.sqrt (n.factorial : ℝ) ≠ 0 :=
      (Real.sqrt_pos.mpr (by positivity : 0 < (n.factorial : ℝ))).ne'
    have hsq : (Real.sqrt (n.factorial : ℝ) : ℂ) ^ 2 = (n.factorial : ℂ) := by
      norm_cast
      exact Real.sq_sqrt (Nat.cast_nonneg _)
    simp only [exponentialCoeff, RCLike.inner_apply, map_div₀, map_pow, Complex.conj_ofReal]
    rw [mul_pow]
    field_simp
    rw [hsq]
    ring
  have h_FockAttCoherentBridge_exponential_inner (α β : ℂ) :
      inner ℂ (exponentialVector α) (exponentialVector β) =
        Complex.exp ((starRingEnd ℂ) α * β) := by
    rw [lp.inner_eq_tsum]
    simp only [exponentialVector, h_FockAttCoherentBridge_exponentialCoeff_inner]
    simpa only [Complex.exp_eq_exp_ℂ] using
      (NormedSpace.expSeries_div_hasSum_exp ((starRingEnd ℂ) α * β)).tsum_eq
  have h_FockAttCoherentBridge_weyl_gram (α β γ : ℂ) :
      inner ℂ (weylVector α β) (weylVector α γ) =
        inner ℂ (exponentialVector β) (exponentialVector γ) := by
    have haa : (starRingEnd ℂ) α * α = ((‖α‖ ^ 2 : ℝ) : ℂ) := by
      rw [RCLike.conj_mul]; norm_cast
    simp only [weylVector, inner_smul_left, inner_smul_right, h_FockAttCoherentBridge_exponential_inner,
      ← Complex.exp_conj, map_sub, map_neg, map_mul, Complex.conj_conj, Complex.conj_ofReal]
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [map_add]
    push_cast
    push_cast at haa
    linear_combination haa
  have h_FockAttCoherentBridge_weyl_dense (α : ℂ) :
      DenseRange (Finsupp.linearCombination ℂ (weylVector α)) := by
    have hspan : (Submodule.span ℂ (Set.range (weylVector α))).topologicalClosure = ⊤ := by
      apply Submodule.topologicalClosure_eq_top_iff.mpr
      apply le_antisymm
      · intro v hv
        have hzero : v = 0 := exponential_vectors_total v (fun β => by
          have hmem : weylVector α (β - α) ∈ Submodule.span ℂ (Set.range (weylVector α)) :=
            Submodule.subset_span ⟨β - α, rfl⟩
          have hinner := Submodule.inner_left_of_mem_orthogonal hmem hv
          have heq : α + (β - α) = β := by ring
          simp only [weylVector, inner_smul_right, heq] at hinner
          exact (mul_eq_zero.mp hinner).resolve_left (Complex.exp_ne_zero _))
        simp [hzero]
      · exact bot_le
    rw [← Finsupp.range_linearCombination] at hspan
    change Dense (Set.range (Finsupp.linearCombination ℂ (weylVector α)))
    rw [dense_iff_closure_eq]
    simpa only [Submodule.topologicalClosure_coe, Submodule.top_coe, LinearMap.coe_range] using
      congrArg (fun K : Submodule ℂ (lp (fun _ : ℕ => ℂ) 2) => (K : Set (lp (fun _ : ℕ => ℂ) 2))) hspan
  have h_FockAttCoherentBridge_exponential_dense :
      DenseRange (Finsupp.linearCombination ℂ exponentialVector) := by
    have hspan : (Submodule.span ℂ (Set.range exponentialVector)).topologicalClosure = ⊤ := by
      apply Submodule.topologicalClosure_eq_top_iff.mpr
      apply le_antisymm
      · intro v hv
        have hzero : v = 0 := exponential_vectors_total v (fun α => by
          have hmem : exponentialVector α ∈ Submodule.span ℂ (Set.range exponentialVector) :=
            Submodule.subset_span ⟨α, rfl⟩
          exact Submodule.inner_left_of_mem_orthogonal hmem hv)
        simp [hzero]
      · exact bot_le
    rw [← Finsupp.range_linearCombination] at hspan
    change Dense (Set.range (Finsupp.linearCombination ℂ exponentialVector))
    rw [dense_iff_closure_eq]
    simpa only [Submodule.topologicalClosure_coe, Submodule.top_coe, LinearMap.coe_range] using
      congrArg (fun K : Submodule ℂ (lp (fun _ : ℕ => ℂ) 2) => (K : Set (lp (fun _ : ℕ => ℂ) 2))) hspan
  have h_FockAttCoherentBridge_displacement_exponential (α β : ℂ) :
      displacement α (exponentialVector β) = weylVector α β := by
    exact h_FockAttFrameExtension_gramUnitary_apply _ _ (h_FockAttCoherentBridge_weyl_gram α) h_FockAttCoherentBridge_exponential_dense (h_FockAttCoherentBridge_weyl_dense α) β
  have h_FockAttCovariance_pairWeyl_gram (a z w : ℂ × ℂ) :
      inner ℂ (pairWeyl a z) (pairWeyl a w) =
        inner ℂ (exponentialPair z) (exponentialPair w) := by
    rw [pairWeyl, pairWeyl, h_FockAttTwoMode_tensor_inner]
    have h1 := (displacement a.1).inner_map_map (exponentialVector z.1) (exponentialVector w.1)
    have h2 := (displacement a.2).inner_map_map (exponentialVector z.2) (exponentialVector w.2)
    simp only [h_FockAttCoherentBridge_displacement_exponential] at h1 h2
    rw [h1, h2, exponentialPair, exponentialPair, h_FockAttTwoMode_tensor_inner]
  have h_FockAttCovariance_pairDisplacement_exponential (a z : ℂ × ℂ) :
      pairDisplacement a (exponentialPair z) = pairWeyl a z := by
    exact h_FockAttFrameExtension_gramUnitary_apply _ _ (h_FockAttCovariance_pairWeyl_gram a) h_FockAttTwoMode_exponentialPair_dense (h_FockAttCovariance_pairWeyl_dense a) z
  have h_FockAttFamilyExt_totalFamily_ext {ι H K : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] [NormedAddCommGroup K] [NormedSpace ℂ K] (v : ι → H) (hv : DenseRange (Finsupp.linearCombination ℂ v))
      (f g : H →L[ℂ] K) (h : ∀ i, f (v i) = g (v i)) : f = g := by
    apply ContinuousLinearMap.ext
    intro x
    refine hv.induction (P := fun y => f y = g y) ?_ ?_ x
    · rintro y ⟨c, rfl⟩
      simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul, h]
    · exact isClosed_eq f.continuous g.continuous
  have h_FockAttPartialTrace_sliceMap_tensor (x v w : (lp (fun _ : ℕ => ℂ) 2)) :
      h_FockAttPartialTrace_sliceMap x (tensor v w) = inner ℂ x v • w := by
    apply lp.ext
    funext n
    change inner ℂ x (w n • v) = inner ℂ x v * w n
    rw [inner_smul_right]
    ring
  have h_FockAttCovariance_slice_pairDisplacement (a : ℂ × ℂ) (w : (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2)) (x : (lp (fun _ : ℕ => ℂ) 2)) :
      h_FockAttPartialTrace_sliceMap x (pairDisplacement a w) =
        displacement a.2 (h_FockAttPartialTrace_sliceMap ((displacement a.1).symm x) w) := by
    let f := (h_FockAttPartialTrace_sliceMap x).comp
      (pairDisplacement a).toContinuousLinearEquiv.toContinuousLinearMap
    let g := (displacement a.2).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (h_FockAttPartialTrace_sliceMap ((displacement a.1).symm x))
    have heq : f = g := h_FockAttFamilyExt_totalFamily_ext exponentialPair h_FockAttTwoMode_exponentialPair_dense f g
      (fun z => by
        change h_FockAttPartialTrace_sliceMap x (pairDisplacement a (exponentialPair z)) = _
        rw [h_FockAttCovariance_pairDisplacement_exponential, pairWeyl, h_FockAttPartialTrace_sliceMap_tensor]
        change _ = displacement a.2
          (h_FockAttPartialTrace_sliceMap ((displacement a.1).symm x) (exponentialPair z))
        rw [exponentialPair, h_FockAttPartialTrace_sliceMap_tensor, map_smul, h_FockAttCoherentBridge_displacement_exponential]
        congr 1
        rw [← h_FockAttCoherentBridge_displacement_exponential]
        simpa only [LinearIsometryEquiv.apply_symm_apply] using
          (displacement a.1).inner_map_map ((displacement a.1).symm x) (exponentialVector z.1))
    exact congrArg (fun T : (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2) →L[ℂ] (lp (fun _ : ℕ => ℂ) 2) => T w) heq
  have h_FockAttCovariance_pairDisplacement_tensor (a : ℂ × ℂ) (v w : (lp (fun _ : ℕ => ℂ) 2)) :
      pairDisplacement a (tensor v w) = tensor (displacement a.1 v) (displacement a.2 w) := by
    apply h_FockAttCovariance_twoMode_ext_slices
    intro x
    rw [h_FockAttCovariance_slice_pairDisplacement, h_FockAttPartialTrace_sliceMap_tensor,
      h_FockAttPartialTrace_sliceMap_tensor, map_smul]
    congr 1
    symm
    simpa only [LinearIsometryEquiv.apply_symm_apply] using
      (displacement a.1).inner_map_map ((displacement a.1).symm x) v
  have h_FockAttCovariance_displacement_zero (v : (lp (fun _ : ℕ => ℂ) 2)) : displacement 0 v = v := by
    have heq : (displacement 0).toContinuousLinearEquiv.toContinuousLinearMap =
        ContinuousLinearMap.id ℂ (lp (fun _ : ℕ => ℂ) 2) :=
      h_FockAttFamilyExt_totalFamily_ext exponentialVector h_FockAttCoherentBridge_exponential_dense _ _ (fun α => by
        change displacement 0 (exponentialVector α) = exponentialVector α
        rw [h_FockAttCoherentBridge_displacement_exponential]
        simp [weylVector])
    exact congrArg (fun T : (lp (fun _ : ℕ => ℂ) 2) →L[ℂ] (lp (fun _ : ℕ => ℂ) 2) => T v) heq
  have h_FockAttCovariance_coherent_purePartialTrace (t r : ℝ) (h : t ^ 2 + r ^ 2 = 1)
      (α : ℂ) (w : (lp (fun _ : ℕ => ℂ) 2)) :
      purePartialTrace (beamUnitary t r h (tensor (displacement α (h_FockAttTwoMode_fock 0)) w)) =
        LinearIsometryEquiv.conjStarAlgEquiv (displacement ((t : ℂ) * α))
          (purePartialTrace (beamUnitary t r h (tensor (h_FockAttTwoMode_fock 0) w))) := by
    have hp : tensor (displacement α (h_FockAttTwoMode_fock 0)) w =
        pairDisplacement (α,0) (tensor (h_FockAttTwoMode_fock 0) w) := by
      rw [h_FockAttCovariance_pairDisplacement_tensor]
      simp only [h_FockAttCovariance_displacement_zero]
    rw [hp, beam_displacement, partialTrace_pairDisplacement]
    simp only [rotate, mul_zero, sub_zero]
  have hv : ‖h_FockAttTwoMode_fock 0‖ = 1 := by simp [h_FockAttTwoMode_fock, lp.norm_single]
  have hc : ‖displacement α (h_FockAttTwoMode_fock 0)‖ = 1 := by rw [LinearIsometryEquiv.norm_map, hv]
  rw [h_FockAttChannel_pureAttenuator_environment η hη p _ hc, h_FockAttChannel_pureAttenuator_environment η hη p _ hv]
  let U := displacement ((Real.sqrt η : ℂ) * α)
  let L := (h_FockAttChannelCovariance_conjugateL U).restrictScalars ℝ
  change (∑' n, p.weight n • purePartialTrace
    (beamSplitter η hη (tensor (displacement α (h_FockAttTwoMode_fock 0)) (h_FockAttTwoMode_fock n)))) =
      L (∑' n, p.weight n • purePartialTrace (beamSplitter η hη (tensor (h_FockAttTwoMode_fock 0) (h_FockAttTwoMode_fock n))))
  rw [L.map_tsum (h_FockAttChannelCovariance_environment_operators_summable η hη p _ hv)]
  apply tsum_congr
  intro n
  rw [L.map_smul]
  congr 1
  exact h_FockAttCovariance_coherent_purePartialTrace (Real.sqrt η) (Real.sqrt (1-η))
    (by rw [Real.sq_sqrt hη.1, Real.sq_sqrt (by linarith [hη.2])]; ring) α (h_FockAttTwoMode_fock n)

def coherentDensity (α : ℂ) : DensityOperator := by
  have h_FockAttProbe_coherent_norm_sq (α : ℂ) (n : ℕ) :
      ‖coherentCoeff α n‖ ^ 2 =
        Real.exp (-‖α‖ ^ 2 / 2) ^ 2 * (‖α‖ ^ 2) ^ n / (n.factorial : ℝ) := by
    rw [coherentCoeff, norm_div, norm_mul, norm_pow]
    simp only [Complex.norm_real, Real.norm_eq_abs, Real.abs_exp,
      abs_of_nonneg (Real.sqrt_nonneg _), div_pow, mul_pow,
      Real.sq_sqrt (Nat.cast_nonneg n.factorial), pow_right_comm ‖α‖ n 2]
  have h_FockAttProbe_coherent_hasSum (α : ℂ) :
      HasSum (fun n : ℕ => ‖coherentCoeff α n‖ ^ 2) 1 := by
    have hseries : HasSum (fun n : ℕ => (‖α‖ ^ 2) ^ n / (n.factorial : ℝ))
        (Real.exp (‖α‖ ^ 2)) := by
      simpa only [Real.exp_eq_exp_ℝ] using
        (NormedSpace.expSeries_div_hasSum_exp (‖α‖ ^ 2))
    have hs := hseries.mul_left
      (Real.exp (-‖α‖ ^ 2 / 2) ^ 2)
    have he : Real.exp (-‖α‖ ^ 2 / 2) ^ 2 * Real.exp (‖α‖ ^ 2) = 1 := by
      rw [sq, ← Real.exp_add, ← Real.exp_add]
      ring_nf
      exact Real.exp_zero
    have hs' : HasSum (fun n : ℕ => ‖coherentCoeff α n‖ ^ 2)
        (Real.exp (-‖α‖ ^ 2 / 2) ^ 2 * Real.exp (‖α‖ ^ 2)) :=
      HasSum.congr_fun hs (fun n => by rw [h_FockAttProbe_coherent_norm_sq]; ring)
    rwa [he] at hs'
  have h_FockAttProbe_coherent_unit (α : ℂ) : ‖coherent α‖ = 1 := by
    have hn := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) (coherent α)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hn
    have hs : ‖coherent α‖ ^ 2 = 1 := hn.trans (h_FockAttProbe_coherent_hasSum α).tsum_eq
    nlinarith [norm_nonneg (coherent α)]
  exact pureDensity (coherent α) (h_FockAttProbe_coherent_unit α)

def fockDensity (n : ℕ) : DensityOperator := by
  let h_FockAttTwoMode_fock (n : ℕ) : (lp (fun _ : ℕ => ℂ) 2) := lp.single 2 n 1
  exact pureDensity (h_FockAttTwoMode_fock n) (by
    simp [h_FockAttTwoMode_fock, lp.norm_single])

end D5.S3.Quantum.QuantumChannels.FockAttenuator.Attenuator
