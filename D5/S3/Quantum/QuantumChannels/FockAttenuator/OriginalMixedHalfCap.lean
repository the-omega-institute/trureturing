/-
NONOPAQUE PRIVATE SOURCE SUPPLIER — UNCOMPILED.
Snapshot: 3f98ae45e29bd5fb6ef8dd7d1e5bf39c2723520e.
Lean: leanprover/lean4:v4.35.0.
Dependency SkewMarginal.lean: 12876 bytes,
SHA256 f9ac837b31edc04e540bb2a8342be015eff8e348f70297db341a71ca2a95cacf,
also UNCOMPILED. No elaboration, tactic, kernel, build, or CI was run.

This source derives the cap on the unchanged original attenuatorOperator.
The only state assumptions are the original DensityOperator fields.
The environment is the existing pointMassEnvironment 1.
The countable sums below are unconditional sums on the completed spaces.
-/
import D5.S3.Quantum.QuantumChannels.FockAttenuator.SkewMarginal
import D5.S3.Quantum.QuantumChannels.FockAttenuator.FiniteRankClassification
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal NNReal ComplexOrder

namespace D5.S3.Quantum.QuantumChannels.FockAttenuator.Bargmann.OriginalMixedHalfCap
open BeamSplitter DisplacementCovariance Attenuator

-- These are the same local CFC instances used in the original outputVector.
local instance : Nontrivial Fock := ⟨⟨lp.single 2 0 1, 0, by
  intro h
  have hc := congrArg (fun v : Fock => v 0) h
  simpa [lp.single_apply] using hc⟩⟩

local instance : IsometricContinuousFunctionalCalculus ℝ
    (Fock →L[ℂ] Fock) IsSelfAdjoint :=
  IsSelfAdjoint.instIsometricContinuousFunctionalCalculus

local instance : NonUnitalIsometricContinuousFunctionalCalculus ℝ
    (Fock →L[ℂ] Fock) IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalIsometricContinuousFunctionalCalculus

/-- Exactly the original positive-square-root occupation column. -/
def sqrtColumn (ρ : DensityOperator) (m : ℕ) : Fock :=
  CFC.sqrt ρ.operator (lp.single 2 m (1 : ℂ))

/-- The actual balanced completed output of an arbitrary system vector. -/
def onePhotonOutput (hHalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    (a : Fock) : TwoMode :=
  beamSplitter (1 / 2) hHalf (tensor a (lp.single 2 1 (1 : ℂ)))

/-- The sign follows from the owner's retained/discarded-port convention. -/
theorem one_photon_kernel (hHalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    (a : Fock) (z w : ℂ) :
    kernel (onePhotonOutput hHalf a) z w =
      transform a ((z + w) / (Real.sqrt 2 : ℂ)) *
        ((w - z) / (Real.sqrt 2 : ℂ)) := by
  have hreal : Real.sqrt (1 / 2 : ℝ) = 1 / Real.sqrt 2 := by
    rw [Real.sqrt_div (by norm_num), Real.sqrt_one]
  have ht : (Real.sqrt (1 / 2 : ℝ) : ℂ) = 1 / (Real.sqrt 2 : ℂ) := by
    exact_mod_cast hreal
  have hr : (Real.sqrt (1 - 1 / 2 : ℝ) : ℂ) = 1 / (Real.sqrt 2 : ℂ) := by
    norm_num only [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num]
    exact ht
  change kernel (beamSplitter (1 / 2) hHalf
    (tensor a (lp.single 2 1 (1 : ℂ)))) z w = _
  rw [beamSplitter, kernel_beam_unitary, kernel_tensor, transform_single]
  simp only [ht, hr, pow_one, Nat.factorial_one, Nat.cast_one,
    Real.sqrt_one, Complex.ofReal_one, div_one]
  have hsum : (1 / (Real.sqrt 2 : ℂ)) * z + (1 / (Real.sqrt 2 : ℂ)) * w =
      (z + w) / (Real.sqrt 2 : ℂ) := by ring
  have hdiff : -(1 / (Real.sqrt 2 : ℂ)) * z + (1 / (Real.sqrt 2 : ℂ)) * w =
      (w - z) / (Real.sqrt 2 : ℂ) := by ring
  rw [hsum, hdiff]

theorem one_photon_kernel_skew (hHalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    (a : Fock) (z w : ℂ) :
    kernel (onePhotonOutput hHalf a) z w =
      -kernel (onePhotonOutput hHalf a) w z := by
  rw [one_photon_kernel, one_photon_kernel]
  rw [show w + z = z + w by ring]
  ring

-- A basis contraction extracts a completed coordinate row. It is the
-- predecessor's existing bounded slice, so no new flip or tensor model is used.
private theorem transform_basis_slice (W : TwoMode) (i : ℕ) (w : ℂ) :
    transform (SkewMarginal.slice (lp.single 2 i (1 : ℂ)) W) w =
      discardedSection W w i := by
  have hs := (summable_contraction W w).hasSum.mapL
    (lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 i)
  change HasSum (fun j : ℕ => exponentialCoeff w j * W j i)
    (discardedSection W w i) at hs
  apply (has_sum (SkewMarginal.slice (lp.single 2 i (1 : ℂ)) W) w).unique
  convert hs using 1
  ext j
  simp only [SkewMarginal.slice_apply, lp.inner_single_left,
    RCLike.inner_apply, map_one, one_mul, exponentialCoeff]
  ring

/-- Every completed system vector has genuinely skew physical output.
There is no support, rank, normalization, energy, or entropy premise. -/
theorem one_photon_output_skew (hHalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    (a : Fock) : SkewMarginal.IsSkew (onePhotonOutput hHalf a) := by
  let W := onePhotonOutput hHalf a
  have hsec (w : ℂ) : discardedSection W w = -retainedSection W w := by
    apply injective
    funext z
    calc
      transform (discardedSection W w) z = kernel W z w :=
        (kernel_eq_transform_discarded_section W z w).symm
      _ = -kernel W w z := one_photon_kernel_skew hHalf a z w
      _ = transform (-retainedSection W w) z := by
        simp only [kernel, transform, inner_neg_right]
  have hrow (i : ℕ) : SkewMarginal.slice (lp.single 2 i (1 : ℂ)) W = -W i := by
    apply injective
    funext w
    rw [transform_basis_slice, hsec]
    simp only [retainedSection, lp.coeFn_neg, Pi.neg_apply, transform, inner_neg_right]
  intro i j
  have hc := congrArg (fun v : Fock => v j) (hrow i)
  simpa only [SkewMarginal.slice_apply, lp.inner_single_left,
    RCLike.inner_apply, map_one, one_mul, lp.coeFn_neg, Pi.neg_apply] using hc

/-- Export the original channel proof's square-root quadratic identity. -/
theorem density_sqrt_norm_sq (ρ : DensityOperator) (v : Fock) :
    ‖CFC.sqrt ρ.operator v‖ ^ 2 = (inner ℂ v (ρ.operator v)).re := by
  have hsquare : CFC.sqrt ρ.operator * CFC.sqrt ρ.operator = ρ.operator :=
    CFC.sqrt_mul_sqrt_self ρ.operator
      ((ContinuousLinearMap.nonneg_iff_isPositive (f := _)).mpr ρ.positive)
  have hself : IsSelfAdjoint (CFC.sqrt ρ.operator) :=
    (CFC.sqrt_nonneg ρ.operator).isSelfAdjoint
  have hs := hself.isSymmetric v (CFC.sqrt ρ.operator v)
  have hprod : CFC.sqrt ρ.operator (CFC.sqrt ρ.operator v) = ρ.operator v := by
    exact congrArg (fun T : Fock →L[ℂ] Fock => T v) hsquare
  change inner ℂ (CFC.sqrt ρ.operator v) (CFC.sqrt ρ.operator v) =
    inner ℂ v (CFC.sqrt ρ.operator (CFC.sqrt ρ.operator v)) at hs
  rw [hprod, inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow] at hs
  simpa only [Complex.ofReal_re] using congrArg Complex.re hs

/-- The unrestricted original input supplies all the ensemble mass. -/
theorem sqrt_columns_hasSum (ρ : DensityOperator) :
    HasSum (fun m : ℕ => ‖sqrtColumn ρ m‖ ^ 2) 1 := by
  exact HasSum.congr_fun ρ.trace_one
    (fun m => density_sqrt_norm_sq ρ (lp.single 2 m (1 : ℂ)))

private theorem tensor_norm_sq (a b : Fock) :
    ‖tensor a b‖ ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
  have ht := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) (tensor a b)
  have hb := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) b
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at ht hb
  rw [ht]
  change (∑' j : ℕ, ‖b j • a‖ ^ 2) = _
  simp only [norm_smul, mul_pow]
  rw [hb.summable.tsum_mul_right, hb.tsum_eq, mul_comm]

theorem one_photon_output_norm_sq (hHalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    (a : Fock) : ‖onePhotonOutput hHalf a‖ ^ 2 = ‖a‖ ^ 2 := by
  unfold onePhotonOutput
  rw [LinearIsometryEquiv.norm_map, tensor_norm_sq]
  simp [lp.norm_single]

theorem output_columns_hasSum (hHalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    (ρ : DensityOperator) :
    HasSum (fun m : ℕ => ‖onePhotonOutput hHalf (sqrtColumn ρ m)‖ ^ 2) 1 :=
  HasSum.congr_fun (sqrt_columns_hasSum ρ)
    (fun m => one_photon_output_norm_sq hHalf (sqrtColumn ρ m))

theorem physical_columns_hasSum (hHalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    (ρ : DensityOperator) :
    HasSum (fun q : ℕ × ℕ => ‖onePhotonOutput hHalf (sqrtColumn ρ q.1) q.2‖ ^ 2) 1 := by
  have hrow (m : ℕ) : HasSum
      (fun j : ℕ => ‖onePhotonOutput hHalf (sqrtColumn ρ m) j‖ ^ 2)
      (‖onePhotonOutput hHalf (sqrtColumn ρ m)‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num)
        (onePhotonOutput hHalf (sqrtColumn ρ m))
  have hall : Summable
      (fun q : ℕ × ℕ => ‖onePhotonOutput hHalf (sqrtColumn ρ q.1) q.2‖ ^ 2) := by
    rw [summable_prod_of_nonneg (fun q => sq_nonneg _)]
    exact ⟨fun m => (hrow m).summable,
      by simpa only [(hrow _).tsum_eq] using (output_columns_hasSum hHalf ρ).summable⟩
  have ht : (∑' q : ℕ × ℕ, ‖onePhotonOutput hHalf (sqrtColumn ρ q.1) q.2‖ ^ 2) = 1 := by
    rw [hall.tsum_prod]
    simp_rw [(hrow _).tsum_eq]
    exact (output_columns_hasSum hHalf ρ).tsum_eq
  exact ht ▸ hall.hasSum

/-- Exact original q=(n,(m,j)) reduction, including every zero bath row. -/
theorem original_outputVector (hHalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    (ρ : DensityOperator) (n m j : ℕ) :
    outputVector (1 / 2) hHalf (pointMassEnvironment 1) ρ (n, (m, j)) =
      if n = 1 then onePhotonOutput hHalf (sqrtColumn ρ m) j else 0 := by
  classical
  by_cases hn : n = 1
  · subst n
    simp [outputVector, pointMassEnvironment, onePhotonOutput, sqrtColumn]
  · simp only [outputVector, pointMassEnvironment, if_neg hn,
      Real.sqrt_zero, Complex.ofReal_zero, zero_smul]

/-- All original triple-index columns have square-norm mass one. -/
theorem original_outputVector_hasSum (hHalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    (ρ : DensityOperator) :
    HasSum (fun q : ℕ × ℕ × ℕ =>
      ‖outputVector (1 / 2) hHalf (pointMassEnvironment 1) ρ q‖ ^ 2) 1 := by
  classical
  let v := outputVector (1 / 2) hHalf (pointMassEnvironment 1) ρ
  have hn (n : ℕ) : Summable (fun q : ℕ × ℕ => ‖v (n, q)‖ ^ 2) := by
    by_cases h : n = 1
    · subst n
      simpa only [v, original_outputVector, if_pos rfl] using
        (physical_columns_hasSum hHalf ρ).summable
    · simpa only [v, original_outputVector, if_neg h, norm_zero,
        zero_pow (by decide : 2 ≠ 0)] using
        (summable_zero : Summable (fun _ : ℕ × ℕ => (0 : ℝ)))
  have hnt (n : ℕ) : (∑' q : ℕ × ℕ, ‖v (n, q)‖ ^ 2) =
      if n = 1 then 1 else 0 := by
    by_cases h : n = 1
    · subst n
      simpa only [v, original_outputVector, if_pos rfl] using
        (physical_columns_hasSum hHalf ρ).tsum_eq
    · simp only [v, original_outputVector, if_neg h, norm_zero,
        zero_pow (by decide : 2 ≠ 0), tsum_zero]
  have hall : Summable (fun q : ℕ × ℕ × ℕ => ‖v q‖ ^ 2) := by
    rw [summable_prod_of_nonneg (fun q => sq_nonneg _)]
    exact ⟨hn, by simpa only [hnt] using (hasSum_ite_eq 1 (1 : ℝ)).summable⟩
  have ht : (∑' q : ℕ × ℕ × ℕ, ‖v q‖ ^ 2) = 1 := by
    rw [hall.tsum_prod]
    simp only [hnt, tsum_ite_eq]
  exact ht ▸ hall.hasSum

/-- Absolute operator-norm summability precedes all operator regrouping. -/
theorem physical_rankOne_norm_summable
    (hHalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1) (ρ : DensityOperator) :
    Summable (fun q : ℕ × ℕ => ‖InnerProductSpace.rankOne ℂ
      (onePhotonOutput hHalf (sqrtColumn ρ q.1) q.2)
      (onePhotonOutput hHalf (sqrtColumn ρ q.1) q.2)‖) := by
  simpa only [InnerProductSpace.norm_rankOne, ← sq] using
    (physical_columns_hasSum hHalf ρ).summable

theorem physical_rankOne_summable
    (hHalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1) (ρ : DensityOperator) :
    Summable (fun q : ℕ × ℕ => InnerProductSpace.rankOne ℂ
      (onePhotonOutput hHalf (sqrtColumn ρ q.1) q.2)
      (onePhotonOutput hHalf (sqrtColumn ρ q.1) q.2)) :=
  Summable.of_norm (physical_rankOne_norm_summable hHalf ρ)

theorem physical_partial_traces_norm_summable
    (hHalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1) (ρ : DensityOperator) :
    Summable (fun m : ℕ => ‖purePartialTrace (onePhotonOutput hHalf (sqrtColumn ρ m))‖) := by
  have hn := physical_rankOne_norm_summable hHalf ρ
  apply Summable.of_nonneg_of_le (fun m => norm_nonneg _) _ hn.prod
  intro m
  change ‖∑' j : ℕ, InnerProductSpace.rankOne ℂ
    (onePhotonOutput hHalf (sqrtColumn ρ m) j)
    (onePhotonOutput hHalf (sqrtColumn ρ m) j)‖ ≤ _
  exact norm_tsum_le_tsum_norm (hn.prod_factor m)

theorem physical_partial_traces_summable
    (hHalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1) (ρ : DensityOperator) :
    Summable (fun m : ℕ => purePartialTrace (onePhotonOutput hHalf (sqrtColumn ρ m))) :=
  Summable.of_norm (physical_partial_traces_norm_summable hHalf ρ)

/-- Identity with the unchanged original mixed channel, not a replacement output. -/
theorem original_attenuator_eq_tsum_partialTrace
    (hHalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1) (ρ : DensityOperator) :
    attenuatorOperator (1 / 2) hHalf (pointMassEnvironment 1) ρ =
      ∑' m : ℕ, purePartialTrace (onePhotonOutput hHalf (sqrtColumn ρ m)) := by
  classical
  let v := outputVector (1 / 2) hHalf (pointMassEnvironment 1) ρ
  have hfull : Summable (fun q : ℕ × ℕ × ℕ =>
      InnerProductSpace.rankOne ℂ (v q) (v q)) := by
    apply Summable.of_norm
    simpa only [InnerProductSpace.norm_rankOne, ← sq] using
      (original_outputVector_hasSum hHalf ρ).summable
  change (∑' q : ℕ × ℕ × ℕ, InnerProductSpace.rankOne ℂ (v q) (v q)) = _
  rw [hfull.tsum_prod]
  have hrow (n : ℕ) :
      (∑' q : ℕ × ℕ, InnerProductSpace.rankOne ℂ (v (n, q)) (v (n, q))) =
        if n = 1 then ∑' q : ℕ × ℕ, InnerProductSpace.rankOne ℂ
          (onePhotonOutput hHalf (sqrtColumn ρ q.1) q.2)
          (onePhotonOutput hHalf (sqrtColumn ρ q.1) q.2) else 0 := by
    by_cases hn : n = 1 <;>
      simp only [v, original_outputVector, hn, if_true, if_false,
        map_zero, ContinuousLinearMap.zero_apply, tsum_zero]
  simp only [hrow, tsum_ite_eq]
  exact (physical_rankOne_summable hHalf ρ).tsum_prod

theorem original_attenuator_hasSum_partialTrace
    (hHalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1) (ρ : DensityOperator) :
    HasSum (fun m : ℕ => purePartialTrace (onePhotonOutput hHalf (sqrtColumn ρ m)))
      (attenuatorOperator (1 / 2) hHalf (pointMassEnvironment 1) ρ) := by
  have hs := (physical_partial_traces_summable hHalf ρ).hasSum
  rw [← original_attenuator_eq_tsum_partialTrace hHalf ρ] at hs
  exact hs

/-- Continuous quadratic evaluation of that very same countable operator sum. -/
theorem original_attenuator_quadratic_hasSum
    (hHalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1) (ρ : DensityOperator) (x : Fock) :
    HasSum (fun m : ℕ =>
      (inner ℂ x (purePartialTrace (onePhotonOutput hHalf (sqrtColumn ρ m)) x)).re)
      (inner ℂ x (attenuatorOperator (1 / 2) hHalf (pointMassEnvironment 1) ρ x)).re := by
  let φ : (Fock →L[ℂ] Fock) →L[ℝ] ℝ :=
    Complex.reCLM.comp (((innerSL ℂ x).comp
      (ContinuousLinearMap.apply ℂ Fock x)).restrictScalars ℝ)
  exact (original_attenuator_hasSum_partialTrace hHalf ρ).mapL φ

/-- Every original density input and every test vector; no cap premise. -/
theorem original_attenuator_half_quadratic
    (hHalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1) (ρ : DensityOperator) (x : Fock) :
    (inner ℂ x (attenuatorOperator (1 / 2) hHalf (pointMassEnvironment 1) ρ x)).re ≤
      ‖x‖ ^ 2 / 2 := by
  have hs := original_attenuator_quadratic_hasSum hHalf ρ x
  have hb : HasSum (fun m : ℕ =>
      ‖onePhotonOutput hHalf (sqrtColumn ρ m)‖ ^ 2 * (‖x‖ ^ 2 / 2)) (‖x‖ ^ 2 / 2) := by
    simpa only [one_mul] using (output_columns_hasSum hHalf ρ).mul_right (‖x‖ ^ 2 / 2)
  calc
    (inner ℂ x (attenuatorOperator (1 / 2) hHalf (pointMassEnvironment 1) ρ x)).re =
        ∑' m : ℕ, (inner ℂ x
          (purePartialTrace (onePhotonOutput hHalf (sqrtColumn ρ m)) x)).re := hs.tsum_eq.symm
    _ ≤ ∑' m : ℕ, ‖onePhotonOutput hHalf (sqrtColumn ρ m)‖ ^ 2 * (‖x‖ ^ 2 / 2) := by
      apply Summable.tsum_le_tsum _ hs.summable hb.summable
      intro m
      have hm := SkewMarginal.pure_partial_trace_half_bound
        (onePhotonOutput hHalf (sqrtColumn ρ m))
        (one_photon_output_skew hHalf (sqrtColumn ρ m)) x
      nlinarith only [hm]
    _ = ‖x‖ ^ 2 / 2 := hb.tsum_eq

/-- Half the actual identity bounds the original all-normal-input operator. -/
theorem original_attenuator_le_half
    (hHalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1) (ρ : DensityOperator) :
    attenuatorOperator (1 / 2) hHalf (pointMassEnvironment 1) ρ ≤
      ((1 / 2 : ℝ) : ℂ) • (1 : Fock →L[ℂ] Fock) := by
  let T := attenuatorOperator (1 / 2) hHalf (pointMassEnvironment 1) ρ
  have hpositive : T.IsPositive :=
    (attenuator (1 / 2) hHalf (pointMassEnvironment 1) ρ).positive
  apply ContinuousLinearMap.le_def.mpr
  apply (ContinuousLinearMap.isPositive_iff_complex _).mpr
  intro x
  have hp := (ContinuousLinearMap.isPositive_iff_complex T).mp hpositive x
  have hTreal : inner ℂ (T x) x = ((inner ℂ x (T x)).re : ℂ) := by
    calc
      inner ℂ (T x) x = ((inner ℂ (T x) x).re : ℂ) := hp.1.symm
      _ = ((inner ℂ x (T x)).re : ℂ) := by rw [inner_re_symm]
  have hleft : inner ℂ
      ((((1 / 2 : ℝ) : ℂ) • (1 : Fock →L[ℂ] Fock) - T) x) x =
        ((‖x‖ ^ 2 / 2 - (inner ℂ x (T x)).re : ℝ) : ℂ) := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, inner_sub_left, inner_smul_left,
      Complex.conj_ofReal, inner_self_eq_norm_sq_to_K, hTreal]
    push_cast
    ring
  change (((inner ℂ
      ((((1 / 2 : ℝ) : ℂ) • (1 : Fock →L[ℂ] Fock) - T) x) x).re : ℝ) : ℂ) =
      inner ℂ ((((1 / 2 : ℝ) : ℂ) • (1 : Fock →L[ℂ] Fock) - T) x) x ∧
    0 ≤ (inner ℂ ((((1 / 2 : ℝ) : ℂ) • (1 : Fock →L[ℂ] Fock) - T) x) x).re
  rw [hleft]
  constructor
  · rfl
  · change 0 ≤ ‖x‖ ^ 2 / 2 - (inner ℂ x (T x)).re
    exact sub_nonneg.mpr (original_attenuator_half_quadratic hHalf ρ x)

theorem original_attenuator_half_sandwich
    (hHalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1) (ρ : DensityOperator) :
    0 ≤ attenuatorOperator (1 / 2) hHalf (pointMassEnvironment 1) ρ ∧
      attenuatorOperator (1 / 2) hHalf (pointMassEnvironment 1) ρ ≤
        ((1 / 2 : ℝ) : ℂ) • (1 : Fock →L[ℂ] Fock) := by
  exact ⟨(ContinuousLinearMap.nonneg_iff_isPositive (f := _)).mpr
    (attenuator (1 / 2) hHalf (pointMassEnvironment 1) ρ).positive,
    original_attenuator_le_half hHalf ρ⟩

/-- Definitional join to the original packaged DensityOperator output. -/
theorem attenuator_density_operator_le_half
    (hHalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1) (ρ : DensityOperator) :
    (attenuator (1 / 2) hHalf (pointMassEnvironment 1) ρ).operator ≤
      ((1 / 2 : ℝ) : ℂ) • (1 : Fock →L[ℂ] Fock) :=
  original_attenuator_le_half hHalf ρ

end D5.S3.Quantum.QuantumChannels.FockAttenuator.Bargmann.OriginalMixedHalfCap
