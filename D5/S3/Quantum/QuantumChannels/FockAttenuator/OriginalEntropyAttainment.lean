/-
NONOPAQUE PRIVATE SOURCE SUPPLIER — UNCOMPILED.
Pinned repository: 3f98ae45e29bd5fb6ef8dd7d1e5bf39c2723520e.
Toolchain: leanprover/lean4:v4.35.0.
Pinned mathlib: 56a005855ea17e0b0958f73ec801ae140b0a1679.

Provisional dependencies, also UNCOMPILED:
  SkewMarginal.lean, 12876 bytes,
    f9ac837b31edc04e540bb2a8342be015eff8e348f70297db341a71ca2a95cacf;
  OriginalMixedHalfCap.lean, 19079 bytes,
    1c6b6fc6c95356cb480d343330c3f109f7912b72dddc0e02d3b252699350d0fb.

No Lean/Lake, elaboration, tactic, compiler, kernel, build, or test was run.
Every tactic below is inert source text awaiting selected actual Mac adoption.
The channel, DensityOperator, input states, and entropy are the original ones.
No finite-support, rank, energy, coherence, or input-entropy premise is added.
-/
import D5.S3.Quantum.QuantumChannels.FockAttenuator.OriginalMixedHalfCap
import D5.S3.Quantum.QuantumChannels.FockAttenuator.Entropy
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal NNReal ComplexOrder

namespace D5.S3.Quantum.QuantumChannels.FockAttenuator.Bargmann.OriginalEntropyAttainment
open BeamSplitter DisplacementCovariance Attenuator Entropy OriginalMixedHalfCap

-- The original outputVector's CFC instances, with the same completed Fock.
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

/-- Parseval for any of the complete bases in the original entropy infimum. -/
private theorem basis_parseval (b : HilbertBasis ℕ ℂ Fock) (v : Fock) :
    HasSum (fun n : ℕ => ‖inner ℂ (b n) v‖ ^ 2) (‖v‖ ^ 2) := by
  have hs := b.hasSum_inner_mul_inner v v
  have hp (n : ℕ) : inner ℂ v (b n) * inner ℂ (b n) v =
      ((‖inner ℂ (b n) v‖ ^ 2 : ℝ) : ℂ) := by
    calc
      _ = (starRingEnd ℂ) (inner ℂ (b n) v) * inner ℂ (b n) v := by
        rw [inner_conj_symm]
      _ = ((‖inner ℂ (b n) v‖ : ℝ) : ℂ) ^ 2 := RCLike.conj_mul _
      _ = _ := by norm_cast
  have hs' : HasSum
      (fun n : ℕ => ((‖inner ℂ (b n) v‖ ^ 2 : ℝ) : ℂ))
      ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    have hval : inner ℂ v v = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]
      norm_cast
    rw [← hval]
    exact HasSum.congr_fun hs (fun n => (hp n).symm)
  exact Complex.hasSum_ofReal.mp hs'

private theorem rankOne_quadratic (v x : Fock) :
    (inner ℂ x (InnerProductSpace.rankOne ℂ v v x)).re =
      ‖inner ℂ x v‖ ^ 2 := by
  have he : inner ℂ x (InnerProductSpace.rankOne ℂ v v x) =
      ((‖inner ℂ x v‖ ^ 2 : ℝ) : ℂ) := by
    rw [InnerProductSpace.rankOne_apply, inner_smul_right]
    calc
      _ = (starRingEnd ℂ) (inner ℂ x v) * inner ℂ x v := by
        rw [inner_conj_symm]
      _ = ((‖inner ℂ x v‖ : ℝ) : ℂ) ^ 2 := RCLike.conj_mul _
      _ = _ := by norm_cast
  simpa only [Complex.ofReal_re] using congrArg Complex.re he

/-- Evaluate the very same original triple-index operator sum in any vector. -/
theorem original_diagonal_eq_tsum
    (hHalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    (ρ : DensityOperator) (x : Fock) :
    (inner ℂ x (attenuatorOperator (1 / 2) hHalf (pointMassEnvironment 1) ρ x)).re =
      ∑' q : ℕ × ℕ × ℕ,
        ‖inner ℂ x (outputVector (1 / 2) hHalf (pointMassEnvironment 1) ρ q)‖ ^ 2 := by
  let v := outputVector (1 / 2) hHalf (pointMassEnvironment 1) ρ
  have hn : Summable (fun q : ℕ × ℕ × ℕ =>
      ‖InnerProductSpace.rankOne ℂ (v q) (v q)‖) := by
    simpa only [InnerProductSpace.norm_rankOne, ← sq] using
      (original_outputVector_hasSum hHalf ρ).summable
  let φ : (Fock →L[ℂ] Fock) →L[ℝ] ℝ :=
    Complex.reCLM.comp (((innerSL ℂ x).comp
      (ContinuousLinearMap.apply ℂ Fock x)).restrictScalars ℝ)
  have hs := (Summable.of_norm hn).hasSum.mapL φ
  have he (T : Fock →L[ℂ] Fock) : φ T = (inner ℂ x (T x)).re := rfl
  simpa only [he, rankOne_quadratic, v, attenuatorOperator, mixture] using hs.tsum_eq.symm

/-- Every complete-basis diagonal of the original physical output has mass one.
The two sums are genuinely summable nonnegative real series. -/
theorem original_basis_diagonal_hasSum
    (hHalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    (ρ : DensityOperator) (b : HilbertBasis ℕ ℂ Fock) :
    HasSum (fun n : ℕ =>
      (inner ℂ (b n)
        (attenuatorOperator (1 / 2) hHalf (pointMassEnvironment 1) ρ (b n))).re) 1 := by
  let v := outputVector (1 / 2) hHalf (pointMassEnvironment 1) ρ
  have hcol (q : ℕ × ℕ × ℕ) :
      HasSum (fun n : ℕ => ‖inner ℂ (b n) (v q)‖ ^ 2) (‖v q‖ ^ 2) :=
    basis_parseval b (v q)
  have hjoint : Summable (fun qn : (ℕ × ℕ × ℕ) × ℕ =>
      ‖inner ℂ (b qn.2) (v qn.1)‖ ^ 2) := by
    rw [summable_prod_of_nonneg (fun _ => sq_nonneg _)]
    refine ⟨fun q => (hcol q).summable, ?_⟩
    simpa only [(hcol _).tsum_eq] using
      (original_outputVector_hasSum hHalf ρ).summable
  have hswap := hjoint.prod_symm
  have hrow (n : ℕ) : Summable (fun q : ℕ × ℕ × ℕ =>
      ‖inner ℂ (b n) (v q)‖ ^ 2) :=
    (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mp hswap |>.1 n
  have hout : Summable (fun n : ℕ => ∑' q : ℕ × ℕ × ℕ,
      ‖inner ℂ (b n) (v q)‖ ^ 2) :=
    (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mp hswap |>.2
  have he : (∑' n : ℕ, ∑' q : ℕ × ℕ × ℕ,
      ‖inner ℂ (b n) (v q)‖ ^ 2) = 1 := by
    rw [hjoint.tsum_comm' (fun q => (hcol q).summable) hrow]
    simp_rw [(hcol _).tsum_eq]
    exact (original_outputVector_hasSum hHalf ρ).tsum_eq
  have hs : HasSum (fun n : ℕ => ∑' q : ℕ × ℕ × ℕ,
      ‖inner ℂ (b n) (v q)‖ ^ 2) 1 := he ▸ hout.hasSum
  exact HasSum.congr_fun hs (fun n => original_diagonal_eq_tsum hHalf ρ (b n))

/-- The actual diagonal distribution, with no spectral or basis restriction. -/
theorem original_basis_distribution
    (hHalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    (ρ : DensityOperator) (b : HilbertBasis ℕ ℂ Fock) :
    (∀ n : ℕ, 0 ≤ (inner ℂ (b n)
      (attenuatorOperator (1 / 2) hHalf (pointMassEnvironment 1) ρ (b n))).re ∧
      (inner ℂ (b n)
        (attenuatorOperator (1 / 2) hHalf (pointMassEnvironment 1) ρ (b n))).re ≤ 1 / 2) ∧
    HasSum (fun n : ℕ => (inner ℂ (b n)
      (attenuatorOperator (1 / 2) hHalf (pointMassEnvironment 1) ρ (b n))).re) 1 := by
  refine ⟨?_, original_basis_diagonal_hasSum hHalf ρ b⟩
  intro n
  constructor
  · rw [original_diagonal_eq_tsum]
    exact tsum_nonneg (fun _ => sq_nonneg _)
  · simpa only [b.orthonormal.norm_eq_one n, one_pow] using
      original_attenuator_half_quadratic hHalf ρ (b n)

/-- Includes q=0; no division by a zero diagonal and no finite-entropy premise. -/
private theorem half_scalar_entropy (q : ℝ) (hq0 : 0 ≤ q) (hqhalf : q ≤ 1 / 2) :
    q * Real.log 2 ≤ Real.negMulLog q := by
  rcases eq_or_lt_of_le hq0 with hq | hq
  · subst q
    simp
  · have hl := Real.log_le_log hq hqhalf
    have hlog : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [Real.log_div one_ne_zero (by norm_num : (2 : ℝ) ≠ 0), Real.log_one]
      ring
    rw [hlog] at hl
    have hm := mul_le_mul_of_nonneg_left hl hq0
    change q * Real.log 2 ≤ -q * Real.log q
    nlinarith only [hm]

/-- Exact original basisEntropy lower bound, for EVERY complete basis. -/
theorem original_basisEntropy_ge_log_two
    (hHalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    (ρ : DensityOperator) (b : HilbertBasis ℕ ℂ Fock) :
    ENNReal.ofReal (Real.log 2) ≤
      basisEntropy (attenuatorOperator (1 / 2) hHalf (pointMassEnvironment 1) ρ) b := by
  let q : ℕ → ℝ := fun n => (inner ℂ (b n)
    (attenuatorOperator (1 / 2) hHalf (pointMassEnvironment 1) ρ (b n))).re
  obtain ⟨hq, hs⟩ := original_basis_distribution hHalf ρ b
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hw : HasSum (fun n : ℕ => q n * Real.log 2) (Real.log 2) := by
    simpa only [one_mul] using hs.mul_right (Real.log 2)
  calc
    ENNReal.ofReal (Real.log 2) =
        ∑' n : ℕ, ENNReal.ofReal (q n * Real.log 2) := by
      rw [← ENNReal.ofReal_tsum_of_nonneg
        (fun n => mul_nonneg (hq n).1 hlog) hw.summable, hw.tsum_eq]
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (Real.negMulLog (q n)) := by
      exact ENNReal.tsum_le_tsum (fun n => ENNReal.ofReal_le_ofReal
        (half_scalar_entropy (q n) (hq n).1 (hq n).2))
    _ = basisEntropy
        (attenuatorOperator (1 / 2) hHalf (pointMassEnvironment 1) ρ) b := rfl

/-- The unchanged basis-infimum ENNReal entropy on every original density input. -/
theorem original_vonNeumannEntropy_ge_log_two
    (hHalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1) (ρ : DensityOperator) :
    ENNReal.ofReal (Real.log 2) ≤
      vonNeumannEntropy (attenuatorOperator (1 / 2) hHalf (pointMassEnvironment 1) ρ) :=
  le_iInf (original_basisEntropy_ge_log_two hHalf ρ)

theorem original_packaged_entropy_ge_log_two
    (hHalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1) (ρ : DensityOperator) :
    ENNReal.ofReal (Real.log 2) ≤ vonNeumannEntropy
      (attenuator (1 / 2) hHalf (pointMassEnvironment 1) ρ).operator :=
  original_vonNeumannEntropy_ge_log_two hHalf ρ

/- The remaining declarations join actual pureDensity inputs to that same channel. -/

/-- The positive square root of the original normalized pure-density operator. -/
theorem sqrt_pureDensity (v : Fock) (hv : ‖v‖ = 1) :
    CFC.sqrt (pureDensity v hv).operator = InnerProductSpace.rankOne ℂ v v := by
  apply CFC.sqrt_unique
  · ext x
    change InnerProductSpace.rankOne ℂ v v
      (InnerProductSpace.rankOne ℂ v v x) = InnerProductSpace.rankOne ℂ v v x
    simp only [InnerProductSpace.rankOne_apply, inner_smul_right,
      inner_self_eq_norm_sq_to_K, hv, one_pow, Complex.ofReal_one, mul_one]
  · exact (ContinuousLinearMap.nonneg_iff_isPositive (f := _)).mpr
      (InnerProductSpace.isPositive_rankOne_self v)

theorem sqrtColumn_pureDensity (v : Fock) (hv : ‖v‖ = 1) (m : ℕ) :
    sqrtColumn (pureDensity v hv) m =
      inner ℂ v (lp.single 2 m (1 : ℂ)) • v := by
  unfold sqrtColumn
  rw [sqrt_pureDensity]
  rfl

private theorem tensor_smul_left (c : ℂ) (a b : Fock) :
    tensor (c • a) b = c • tensor a b := by
  apply lp.ext
  funext j
  change b j • (c • a) = c • (b j • a)
  simp only [smul_smul]
  rw [mul_comm]

private theorem onePhotonOutput_smul
    (hHalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1) (c : ℂ) (v : Fock) :
    onePhotonOutput hHalf (c • v) = c • onePhotonOutput hHalf v := by
  unfold onePhotonOutput
  rw [tensor_smul_left, map_smul]

private theorem rankOne_smul_self (c : ℂ) (v : Fock) :
    InnerProductSpace.rankOne ℂ (c • v) (c • v) =
      ((‖c‖ ^ 2 : ℝ) : ℂ) • InnerProductSpace.rankOne ℂ v v := by
  ext x
  simp only [InnerProductSpace.rankOne_apply, ContinuousLinearMap.smul_apply,
    inner_smul_left, smul_smul]
  congr 1
  calc
    ((starRingEnd ℂ) c * inner ℂ v x) * c =
        ((starRingEnd ℂ) c * c) * inner ℂ v x := by ring
    _ = ((‖c‖ ^ 2 : ℝ) : ℂ) * inner ℂ v x := by
      rw [RCLike.conj_mul]
      norm_cast

private theorem purePartialTrace_smul (c : ℂ) (W : TwoMode) :
    purePartialTrace (c • W) =
      ((‖c‖ ^ 2 : ℝ) : ℂ) • purePartialTrace W := by
  unfold purePartialTrace mixture
  simp only [lp.coeFn_smul, Pi.smul_apply, rankOne_smul_self]
  exact tsum_const_smul'' _

/-- The scalar mass of every original rank-one square-root column is one. -/
private theorem pure_column_mass (v : Fock) (hv : ‖v‖ = 1) :
    HasSum (fun m : ℕ => ‖inner ℂ v (lp.single 2 m (1 : ℂ))‖ ^ 2) 1 := by
  have hs := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) v
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, hv, one_pow] at hs
  apply HasSum.congr_fun hs
  intro m
  simp only [lp.inner_single_right, RCLike.inner_apply, mul_one, RCLike.norm_conj]

/-- Original full density channel equals the actual pure marginal, including
infinite-support coherent v. No conclusion is stored in the input state. -/
theorem original_pureDensity_eq_partialTrace
    (hHalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    (v : Fock) (hv : ‖v‖ = 1) :
    attenuatorOperator (1 / 2) hHalf (pointMassEnvironment 1) (pureDensity v hv) =
      purePartialTrace (onePhotonOutput hHalf v) := by
  rw [original_attenuator_eq_tsum_partialTrace]
  simp_rw [sqrtColumn_pureDensity, onePhotonOutput_smul, purePartialTrace_smul]
  have hc : HasSum
      (fun m : ℕ => ((‖inner ℂ v (lp.single 2 m (1 : ℂ))‖ ^ 2 : ℝ) : ℂ)) 1 := by
    exact Complex.hasSum_ofReal.mpr (pure_column_mass v hv)
  simpa only [one_smul] using
    (hc.smul_const (purePartialTrace (onePhotonOutput hHalf v))).tsum_eq

/-- Join to the pinned pureAttenuatorOperator used by coherent covariance. -/
theorem original_pureDensity_eq_pureAttenuator
    (hHalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    (v : Fock) (hv : ‖v‖ = 1) :
    attenuatorOperator (1 / 2) hHalf (pointMassEnvironment 1) (pureDensity v hv) =
      pureAttenuatorOperator (1 / 2) hHalf (pointMassEnvironment 1) v := by
  rw [original_pureDensity_eq_partialTrace, point_mass_pure_attenuator]
  rfl

/-- Actual completed occupation action, with the pinned discarded-port sign. -/
theorem original_vacuum_output
    (hHalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1) :
    onePhotonOutput hHalf (lp.single 2 0 (1 : ℂ)) =
      (Real.sqrt (1 / 2 : ℝ) : ℂ) •
        tensor (lp.single 2 0 (1 : ℂ)) (lp.single 2 1 (1 : ℂ)) +
      (-(Real.sqrt (1 / 2 : ℝ) : ℂ)) •
        tensor (lp.single 2 1 (1 : ℂ)) (lp.single 2 0 (1 : ℂ)) := by
  have hr : Real.sqrt (1 - (1 / 2 : ℝ)) = Real.sqrt (1 / 2 : ℝ) := by
    congr 1
    ring
  have h := beamUnitary_fock (Real.sqrt (1 / 2 : ℝ))
    (Real.sqrt (1 - (1 / 2 : ℝ)))
    (by rw [Real.sq_sqrt hHalf.1, Real.sq_sqrt (by linarith [hHalf.2])]; ring) 0 1
  simpa [onePhotonOutput, beamSplitter, fockExpansion, fockPair,
    Fin.sum_univ_succ, hr] using h

/-- Both nonzero columns and every zero column of the actual vacuum output. -/
theorem original_vacuum_output_column
    (hHalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1) (j : ℕ) :
    onePhotonOutput hHalf (lp.single 2 0 (1 : ℂ)) j =
      if j = 0 then -(Real.sqrt (1 / 2 : ℝ) : ℂ) • lp.single 2 1 (1 : ℂ)
      else if j = 1 then (Real.sqrt (1 / 2 : ℝ) : ℂ) • lp.single 2 0 (1 : ℂ)
      else 0 := by
  classical
  rw [original_vacuum_output]
  by_cases h0 : j = 0
  · subst j
    simp [tensor, lp.single_apply]
  · by_cases h1 : j = 1
    · subst j
      simp [tensor, lp.single_apply]
    · simp [tensor, lp.single_apply, h0, h1, Ne.symm h0, Ne.symm h1]

/-- Literal fockDensity 0 under the original full channel is the pinned
finiteDiagonal with two half weights. -/
theorem original_vacuum_eq_finiteDiagonal
    (hHalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1) :
    attenuatorOperator (1 / 2) hHalf (pointMassEnvironment 1) (fockDensity 0) =
      finiteDiagonal (fun _ : Fin 2 => (1 / 2 : ℝ)) := by
  classical
  have hv0 : ‖lp.single (E := fun _ : ℕ => ℂ) 2 0 (1 : ℂ)‖ = 1 := by
    simp [lp.norm_single]
  change attenuatorOperator (1 / 2) hHalf (pointMassEnvironment 1)
    (pureDensity (lp.single 2 0 (1 : ℂ)) hv0) = _
  rw [original_pureDensity_eq_partialTrace]
  unfold purePartialTrace mixture
  rw [tsum_eq_sum (s := ({0, 1} : Finset ℕ)) (fun j hj => by
    have h0 : j ≠ 0 := by simpa using (Finset.not_mem_insert.mp hj).1
    have h1 : j ≠ 1 := by simpa using (Finset.not_mem_insert.mp hj).2
    simp only [original_vacuum_output_column, if_neg h0, if_neg h1]
    ext x
    simp [InnerProductSpace.rankOne_apply])]
  have hs : ‖(Real.sqrt (1 / 2 : ℝ) : ℂ)‖ ^ 2 = (1 / 2 : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (by norm_num)]
  simp only [Finset.sum_insert (by simp : (0 : ℕ) ∉ ({1} : Finset ℕ)),
    Finset.sum_singleton, original_vacuum_output_column, if_pos rfl,
    if_neg (by decide : (1 : ℕ) ≠ 0), rankOne_smul_self, norm_neg, hs]
  simp only [finiteDiagonal, Fin.sum_univ_two]
  exact add_comm _ _

/-- Exact finite scalar entropy calculation in nats. -/
private theorem half_half_entropy :
    vonNeumannEntropy (finiteDiagonal (fun _ : Fin 2 => (1 / 2 : ℝ))) =
      ENNReal.ofReal (Real.log 2) := by
  rw [finiteDiagonal_entropy (fun _ : Fin 2 => (1 / 2 : ℝ))
    (by intro _; norm_num) (by intro _; norm_num)]
  congr 1
  simp only [D5.S3.Entropy.MaxEntropy.shannonEntropy, Fin.sum_univ_two,
    Real.negMulLog_def, Real.log_div one_ne_zero (by norm_num : (2 : ℝ) ≠ 0),
    Real.log_one]
  ring

theorem original_vacuum_entropy
    (hHalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1) :
    vonNeumannEntropy
      (attenuatorOperator (1 / 2) hHalf (pointMassEnvironment 1) (fockDensity 0)) =
        ENNReal.ofReal (Real.log 2) := by
  rw [original_vacuum_eq_finiteDiagonal]
  exact half_half_entropy

/-- Extract the existing dense Gram-extension action; no new displacement. -/
theorem original_displacement_exponential (α β : ℂ) :
    displacement α (exponentialVector β) = weylVector α β := by
  have hs : Finsupp.linearCombination ℂ exponentialVector (Finsupp.single β (1 : ℂ)) =
      exponentialVector β := by simp
  rw [← hs]
  unfold displacement
  rw [LinearEquiv.extendOfIsometry_eq]
  simp only [LinearEquiv.refl_apply, Finsupp.linearCombination_single, one_smul]

/-- The literal existing coherent vector is displaced actual vacuum. -/
theorem original_coherent_eq_displaced_vacuum (α : ℂ) :
    coherent α = displacement α (lp.single 2 0 (1 : ℂ)) := by
  have hz : exponentialVector 0 = lp.single 2 0 (1 : ℂ) := by
    apply lp.ext
    funext n
    by_cases hn : n = 0
    · subst n
      simp [exponentialVector, exponentialCoeff, lp.single_apply]
    · simp [exponentialVector, exponentialCoeff, lp.single_apply, hn, Ne.symm hn]
  rw [← hz, original_displacement_exponential]
  apply lp.ext
  funext n
  simp only [coherent, coherentCoeff, weylVector, zero_mul, mul_zero, sub_zero, add_zero,
    lp.coeFn_smul, Pi.smul_apply, exponentialVector, exponentialCoeff, smul_eq_mul]
  rw [show -((‖α‖ ^ 2 / 2 : ℝ) : ℂ) = ((-‖α‖ ^ 2 / 2 : ℝ) : ℂ) by push_cast; ring]
  rw [← Complex.ofReal_exp]
  ring

/-- The original coherentDensity, with its physical input action and full/pure join. -/
theorem original_coherent_output_covariance
    (hHalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1) (α : ℂ) :
    attenuatorOperator (1 / 2) hHalf (pointMassEnvironment 1) (coherentDensity α) =
      LinearIsometryEquiv.conjStarAlgEquiv
        (displacement ((Real.sqrt (1 / 2 : ℝ) : ℂ) * α))
        (attenuatorOperator (1 / 2) hHalf (pointMassEnvironment 1) (fockDensity 0)) := by
  have hv : ‖coherent α‖ = 1 := by
    rw [original_coherent_eq_displaced_vacuum, LinearIsometryEquiv.norm_map]
    simp [lp.norm_single]
  have hρ : coherentDensity α = pureDensity (coherent α) hv := rfl
  rw [hρ, original_pureDensity_eq_pureAttenuator,
    original_coherent_eq_displaced_vacuum, coherent_output_covariance]
  congr 1
  have hv0 : ‖lp.single (E := fun _ : ℕ => ℂ) 2 0 (1 : ℂ)‖ = 1 := by
    simp [lp.norm_single]
  change pureAttenuatorOperator (1 / 2) hHalf (pointMassEnvironment 1)
    (lp.single 2 0 (1 : ℂ)) =
      attenuatorOperator (1 / 2) hHalf (pointMassEnvironment 1)
        (pureDensity (lp.single 2 0 (1 : ℂ)) hv0)
  exact (original_pureDensity_eq_pureAttenuator hHalf
    (lp.single 2 0 (1 : ℂ)) hv0).symm

/-- Direct invariance of the unchanged basis-infimum entropy. -/
private theorem entropy_conj_le (U : Fock ≃ₗᵢ[ℂ] Fock) (T : Fock →L[ℂ] Fock) :
    vonNeumannEntropy (U.conjStarAlgEquiv T) ≤ vonNeumannEntropy T := by
  apply le_iInf
  intro b
  let c : HilbertBasis ℕ ℂ Fock := HilbertBasis.ofRepr (U.symm.trans b.repr)
  have hc (n : ℕ) : c n = U (b n) := rfl
  calc
    vonNeumannEntropy (U.conjStarAlgEquiv T) ≤
        basisEntropy (U.conjStarAlgEquiv T) c := iInf_le _ c
    _ = basisEntropy T b := by
      unfold basisEntropy
      apply tsum_congr
      intro n
      rw [hc, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
        LinearIsometryEquiv.symm_apply_apply, U.inner_map_map]

theorem original_entropy_unitary_conj (U : Fock ≃ₗᵢ[ℂ] Fock)
    (T : Fock →L[ℂ] Fock) :
    vonNeumannEntropy (U.conjStarAlgEquiv T) = vonNeumannEntropy T := by
  apply le_antisymm (entropy_conj_le U T)
  have h := entropy_conj_le U.symm (U.conjStarAlgEquiv T)
  have he : U.symm.conjStarAlgEquiv (U.conjStarAlgEquiv T) = T := by
    ext x
    simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
      LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.symm_apply_apply]
  rwa [he] at h

/-- Every literal original coherentDensity attains the same all-input bound. -/
theorem original_coherent_entropy
    (hHalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1) (α : ℂ) :
    vonNeumannEntropy
      (attenuatorOperator (1 / 2) hHalf (pointMassEnvironment 1) (coherentDensity α)) =
        ENNReal.ofReal (Real.log 2) := by
  rw [original_coherent_output_covariance, original_entropy_unitary_conj,
    original_vacuum_entropy]

theorem original_packaged_vacuum_entropy
    (hHalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1) :
    vonNeumannEntropy
      (attenuator (1 / 2) hHalf (pointMassEnvironment 1) (fockDensity 0)).operator =
        ENNReal.ofReal (Real.log 2) := original_vacuum_entropy hHalf

theorem original_packaged_coherent_entropy
    (hHalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1) (α : ℂ) :
    vonNeumannEntropy
      (attenuator (1 / 2) hHalf (pointMassEnvironment 1) (coherentDensity α)).operator =
        ENNReal.ofReal (Real.log 2) := original_coherent_entropy hHalf α

/-- The infimum over the unchanged full DensityOperator type is attained. -/
theorem original_minimum_entropy
    (hHalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1) :
    (⨅ ρ : DensityOperator, vonNeumannEntropy
      (attenuatorOperator (1 / 2) hHalf (pointMassEnvironment 1) ρ)) =
        ENNReal.ofReal (Real.log 2) := by
  apply le_antisymm
  · calc
      (⨅ ρ : DensityOperator, vonNeumannEntropy
          (attenuatorOperator (1 / 2) hHalf (pointMassEnvironment 1) ρ)) ≤
          vonNeumannEntropy
            (attenuatorOperator (1 / 2) hHalf (pointMassEnvironment 1) (fockDensity 0)) :=
        iInf_le _ (fockDensity 0)
      _ = _ := original_vacuum_entropy hHalf
  · exact le_iInf (original_vonNeumannEntropy_ge_log_two hHalf)

end D5.S3.Quantum.QuantumChannels.FockAttenuator.Bargmann.OriginalEntropyAttainment
