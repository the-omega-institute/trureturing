/- GID: D5/S3/Quantum/Measurement/ConditioningTraceDistanceConstant
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/ConditioningTraceDistanceConstant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The sharp trace-distance constant of a positive conditioning filter. -/

import D5.S3.Quantum.Measurement.BranchConditionedTraceDistance
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
import Mathlib.Analysis.Matrix.PosDef

noncomputable section
namespace D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant

open BigOperators Matrix Filter Topology
open scoped ComplexOrder MatrixOrder InnerProductSpace
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteTraceDistance

set_option autoImplicit false
set_option relaxedAutoImplicit false

def rMax {d : ℕ} (hd : 0 < d) (R : Matrix (Fin d) (Fin d) ℂ)
    (hR : R.IsHermitian) : ℝ :=
  hR.eigenvalues₀ ⟨0, by simp [hd]⟩

def rMin {d : ℕ} (hd : 0 < d) (R : Matrix (Fin d) (Fin d) ℂ)
    (hR : R.IsHermitian) : ℝ :=
  hR.eigenvalues₀ ⟨Fintype.card (Fin d) - 1, by simp [hd]⟩

def conditionNumber {d : ℕ} (hd : 0 < d) (R : Matrix (Fin d) (Fin d) ℂ)
    (hR : R.IsHermitian) : ℝ :=
  rMax hd R hR / rMin hd R hR

def conditionedState {d : ℕ} (hd : 0 < d) (R : Matrix (Fin d) (Fin d) ℂ) (hR : R.PosDef)
    (ρ : DensityState (Fin d)) : DensityState (Fin d) := by
  let hH : R.IsHermitian := hR.isHermitian
  let kMin : Fin (Fintype.card (Fin d)) :=
    ⟨Fintype.card (Fin d) - 1, by simpa using hd⟩
  let rlo : ℝ := rMin hd R hH
  have hrlo : 0 < rlo := by
    have hp := hH.posDef_iff_eigenvalues_pos.mp hR
      ((RHLinalg.eigEquiv (n := Fin d)) kMin)
    rw [RHLinalg.eigenvalues_eigEquiv hH kMin] at hp
    simpa [rlo, rMin, kMin] using hp
  have hlower : ∀ x ∈ spectrum ℝ R, rlo ≤ x := by
    rw [hH.spectrum_real_eq_range_eigenvalues]
    rintro _ ⟨i, rfl⟩
    let k : Fin (Fintype.card (Fin d)) :=
      (RHLinalg.eigEquiv (n := Fin d)).symm i
    have hi : hH.eigenvalues i = hH.eigenvalues₀ k := by
      simpa [k] using RHLinalg.eigenvalues_eigEquiv hH k
    have hk : k.val ≤ Fintype.card (Fin d) - 1 := by omega
    have hle := hH.eigenvalues₀_antitone (show k ≤ kMin by exact hk)
    rw [hi]
    simpa [rlo, rMin, kMin, RHLinalg.eigenvalues_eigEquiv] using hle
  have hfloor : (rlo : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) ≤ R := by
    simpa [rlo, Algebra.algebraMap_eq_smul_one] using
      algebraMap_le_of_le_spectrum hlower hH
  let X : Matrix (Fin d) (Fin d) ℂ := CStarMatrix.ofMatrix.symm ρ.val
  have hXpsd : X.PosSemidef := by
    change (CStarMatrix.ofMatrixStarAlgEquiv.symm ρ.val).PosSemidef
    simpa [X, CStarMatrix.ofMatrix_eq_ofMatrixStarAlgEquiv] using
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm ρ.prop.1).posSemidef
  have hXtrace : X.trace = 1 := by
    change Matrix.trace (CStarMatrix.ofMatrix.symm ρ.val) = 1
    exact ρ.prop.2
  have htraceLower : rlo ≤ (X * R).trace.re := by
    have ht := RHLinalg.trace_mul_nonneg_of_posSemidef hXpsd
      (sub_nonneg.mpr hfloor)
    have ht' : 0 ≤ (X * R).trace.re - rlo := by
      simpa [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_sub,
        Matrix.trace_smul, hXtrace, Complex.sub_re, Complex.real_smul] using ht
    linarith
  have htrpos : 0 < (R * X).trace.re := by
    rw [Matrix.trace_mul_comm R X]
    exact lt_of_lt_of_le hrlo htraceLower
  have hbase : (CFC.sqrt R * X * CFC.sqrt R).PosSemidef := by
    have hGstar : (CFC.sqrt R)ᴴ = CFC.sqrt R := by
      simpa [star_eq_conjTranspose] using (CFC.sqrt_nonneg R).isSelfAdjoint.star_eq
    simpa [hGstar, hXpsd.1.eq, hH.eq, Matrix.mul_assoc] using
      ((hXpsd.conjTranspose_mul_mul_same (CFC.sqrt R)).conjTranspose)
  have hpsd : ((1 / (R * X).trace.re) : ℝ) •
      (CFC.sqrt R * X * CFC.sqrt R) |>.PosSemidef :=
    hbase.smul (one_div_nonneg.mpr htrpos.le)
  refine ⟨CStarMatrix.ofMatrix
      (((1 / (R * X).trace.re) : ℝ) • (CFC.sqrt R * X * CFC.sqrt R)), ?_, ?_⟩
  · exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hpsd.nonneg
  · change Matrix.trace (((1 / (R * X).trace.re) : ℝ) •
      (CFC.sqrt R * X * CFC.sqrt R)) = 1
    rw [Matrix.trace_smul]
    have htrace : (CFC.sqrt R * X * CFC.sqrt R).trace = (R * X).trace := by
      rw [Matrix.trace_mul_cycle]
      rw [CFC.sqrt_mul_sqrt_self R hR.posSemidef.nonneg]
    have hstar : star ((R * X).trace) = (R * X).trace := by
      rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hXpsd.isHermitian.eq,
        hH.eq, Matrix.trace_mul_comm]
    have htraceReal : (R * X).trace = ((R * X).trace.re : ℂ) := by
      apply Complex.ext
      · simp
      · have him := congrArg Complex.im hstar
        change ((starRingEnd ℂ) ((R * X).trace)).im = _ at him
        rw [Complex.conj_im] at him
        have him' : (R * X).trace.im = 0 := by linarith
        simpa [him']
    rw [htrace, htraceReal]
    simp only [Complex.real_smul, one_div, Complex.ofReal_re, Complex.ofReal_inv]
    field_simp [htrpos.ne']

theorem conditioning_trace_distance_constant
    {d : ℕ} (hd : 2 ≤ d) (R : Matrix (Fin d) (Fin d) ℂ) (hR : R.PosDef) :
    (∀ ρ σ : DensityState (Fin d),
      (conditionNumber (by omega) R hR.isHermitian)⁻¹ * traceDistance ρ σ ≤
        traceDistance (conditionedState (by omega) R hR ρ)
          (conditionedState (by omega) R hR σ) ∧
      traceDistance (conditionedState (by omega) R hR ρ)
          (conditionedState (by omega) R hR σ) ≤
        conditionNumber (by omega) R hR.isHermitian * traceDistance ρ σ) ∧
      (∀ ρ : DensityState (Fin d),
        rMin (by omega) R hR.isHermitian = rMax (by omega) R hR.isHermitian →
          conditionedState (by omega) R hR ρ = ρ) ∧
      IsLUB {x : ℝ | ∃ ρ σ : DensityState (Fin d),
        ρ ≠ σ ∧
          x = traceDistance (conditionedState (by omega) R hR ρ)
              (conditionedState (by omega) R hR σ) /
            traceDistance ρ σ} (conditionNumber (by omega) R hR.isHermitian) := by
  classical
  have hd0 : 0 < d := by omega
  letI : NeZero (Fintype.card (Fin d)) :=
    ⟨Nat.ne_of_gt (by simpa using hd0)⟩
  let hH : R.IsHermitian := hR.isHermitian
  let IsDensity (X : Matrix (Fin d) (Fin d) ℂ) : Prop :=
    X.PosSemidef ∧ X.trace = 1
  let traceDistance (X Y : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
    traceNorm (X - Y) / 2
  let conditionedState (R' X : Matrix (Fin d) (Fin d) ℂ) :
      Matrix (Fin d) (Fin d) ℂ :=
    (1 / (R' * X).trace.re) • (CFC.sqrt R' * X * CFC.sqrt R')
  have spectralSandwich : ∀ (R' : Matrix (Fin d) (Fin d) ℂ) (hR' : R'.PosDef),
      (rMin (by omega) R' hR'.isHermitian : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) ≤ R' ∧
        R' ≤ (rMax (by omega) R' hR'.isHermitian : ℂ) •
          (1 : Matrix (Fin d) (Fin d) ℂ) := by
    intro R' hR'
    let hH' : R'.IsHermitian := hR'.isHermitian
    have hupper : ∀ x ∈ spectrum ℝ R', x ≤ rMax (by omega) R' hH' := by
      rw [hH'.spectrum_real_eq_range_eigenvalues]
      rintro _ ⟨i, rfl⟩
      let k : Fin (Fintype.card (Fin d)) := (RHLinalg.eigEquiv (n := Fin d)).symm i
      let k0 : Fin (Fintype.card (Fin d)) := ⟨0, by simpa using hd0⟩
      have hi : hH'.eigenvalues i = hH'.eigenvalues₀ k := by
        simpa [k] using RHLinalg.eigenvalues_eigEquiv hH' k
      have hle := hH'.eigenvalues₀_antitone (show k0 ≤ k by exact Fin.zero_le k)
      rw [hi]
      simpa [rMax, k0, RHLinalg.eigenvalues_eigEquiv] using hle
    have hlower : ∀ x ∈ spectrum ℝ R', rMin (by omega) R' hH' ≤ x := by
      rw [hH'.spectrum_real_eq_range_eigenvalues]
      rintro _ ⟨i, rfl⟩
      let k : Fin (Fintype.card (Fin d)) := (RHLinalg.eigEquiv (n := Fin d)).symm i
      let kLast : Fin (Fintype.card (Fin d)) :=
        ⟨Fintype.card (Fin d) - 1, by simpa using hd0⟩
      have hi : hH'.eigenvalues i = hH'.eigenvalues₀ k := by
        simpa [k] using RHLinalg.eigenvalues_eigEquiv hH' k
      have hk : k.val ≤ Fintype.card (Fin d) - 1 := by omega
      have hle := hH'.eigenvalues₀_antitone (show k ≤ kLast by exact hk)
      rw [hi]
      simpa [rMin, kLast, RHLinalg.eigenvalues_eigEquiv] using hle
    constructor
    · simpa [rMin, Algebra.algebraMap_eq_smul_one] using
        algebraMap_le_of_le_spectrum hlower hH'
    · simpa [rMax, Algebra.algebraMap_eq_smul_one] using
        le_algebraMap_of_spectrum_le hupper hH'

  have hUpperBounds : ∀ (R' : Matrix (Fin d) (Fin d) ℂ) (hR' : R'.PosDef)
      (rlo rhi : ℝ), 0 < rlo → 0 < rhi →
      (rlo : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) ≤ R' →
      R' ≤ (rhi : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) →
      ∀ ρ σ : Matrix (Fin d) (Fin d) ℂ, IsDensity ρ → IsDensity σ →
        traceDistance (conditionedState R' ρ) (conditionedState R' σ) ≤
          (rhi / rlo) * traceDistance ρ σ := by
    intro R' hR' rlo rhi hrlo hrhi hfloor hceil ρ σ hρ hσ
    let G' : Matrix (Fin d) (Fin d) ℂ := CFC.sqrt R'
    let K : Unit → Matrix (Fin d) (Fin d) ℂ := fun _ => (Real.sqrt rhi)⁻¹ • G'
    let B : Matrix (Fin d) (Fin d) ℂ := ∑ i, (K i)ᴴ * K i
    have hGstar : G'ᴴ = G' := by
      simpa [G', star_eq_conjTranspose] using (CFC.sqrt_nonneg R').isSelfAdjoint.star_eq
    have hGsq : G' * G' = R' := by
      simpa [G'] using CFC.sqrt_mul_sqrt_self R' hR'.posSemidef.nonneg
    have hB_eq : B = (rhi⁻¹ : ℝ) • R' := by
      simp [B, K, hGstar, Matrix.conjTranspose_smul, hGsq]
      rw [smul_smul, ← _root_.mul_inv_rev, ← pow_two, Real.sq_sqrt hrhi.le]
    have hB : B ≤ (1 : Matrix (Fin d) (Fin d) ℂ) := by
      rw [hB_eq]
      have := smul_le_smul_of_nonneg_left hceil (le_of_lt (inv_pos.mpr hrhi))
      simpa [smul_smul, Algebra.algebraMap_eq_smul_one, hrhi.ne'] using this
    have hρpsd : ρ.PosSemidef := hρ.1
    have hσpsd : σ.PosSemidef := hσ.1
    have hρtrace : ρ.trace = 1 := hρ.2
    have hσtrace : σ.trace = 1 := hσ.2
    have htraceLower : ∀ X : Matrix (Fin d) (Fin d) ℂ, IsDensity X →
        rlo ≤ (X * R').trace.re := by
      intro X hX
      have hdiff : (R' - (rlo : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)).PosSemidef :=
        hfloor
      have ht := RHLinalg.trace_mul_nonneg_of_posSemidef hX.1 hdiff
      have ht' : 0 ≤ (X * R').trace.re - rlo := by
        simpa [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_sub,
          Matrix.trace_smul, hX.2, Complex.sub_re, Complex.real_smul] using ht
      linarith
    have hp : 0 < (ρ * B).trace.re := by
      have hlo := htraceLower ρ hρ
      have hp_eq : (ρ * B).trace.re = rhi⁻¹ * (ρ * R').trace.re := by
        rw [hB_eq, Matrix.mul_smul, Matrix.trace_smul]
        simp [Complex.real_smul]
      rw [hp_eq]
      exact mul_pos (inv_pos.mpr hrhi) (lt_of_lt_of_le hrlo hlo)
    have hq : 0 < (σ * B).trace.re := by
      have hlo := htraceLower σ hσ
      have hq_eq : (σ * B).trace.re = rhi⁻¹ * (σ * R').trace.re := by
        rw [hB_eq, Matrix.mul_smul, Matrix.trace_smul]
        simp [Complex.real_smul]
      rw [hq_eq]
      exact mul_pos (inv_pos.mpr hrhi) (lt_of_lt_of_le hrlo hlo)
    let pR : ℝ := (R' * ρ).trace.re
    let qR : ℝ := (R' * σ).trace.re
    have hpR : 0 < pR := by
      apply lt_of_lt_of_le hrlo
      have ht := htraceLower ρ hρ
      rw [Matrix.trace_mul_comm ρ R'] at ht
      simpa [pR] using ht
    have hqR : 0 < qR := by
      apply lt_of_lt_of_le hrlo
      have ht := htraceLower σ hσ
      rw [Matrix.trace_mul_comm σ R'] at ht
      simpa [qR] using ht
    have hpB : (ρ * B).trace.re = rhi⁻¹ * pR := by
      rw [hB_eq, Matrix.mul_smul, Matrix.trace_smul]
      rw [Matrix.trace_mul_comm ρ R']
      simp [pR, Complex.real_smul]
    have hqB : (σ * B).trace.re = rhi⁻¹ * qR := by
      rw [hB_eq, Matrix.mul_smul, Matrix.trace_smul]
      rw [Matrix.trace_mul_comm σ R']
      simp [qR, Complex.real_smul]
    have hPhi (X : Matrix (Fin d) (Fin d) ℂ) :
        (∑ i : Unit, K i * X * (K i)ᴴ) = (rhi⁻¹ : ℝ) • (G' * X * G') := by
      simp [K, hGstar, Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul,
        smul_smul, hGsq]
      rw [← _root_.mul_inv_rev, ← pow_two, Real.sq_sqrt hrhi.le]
    have hnormρ :
        (1 / (ρ * B).trace.re) • (∑ i : Unit, K i * ρ * (K i)ᴴ) =
          conditionedState R' ρ := by
      rw [hPhi, hpB]
      simp only [conditionedState, G', pR]
      rw [smul_smul]
      congr 1
      field_simp [hpR.ne', hrhi.ne']
    have hnormσ :
        (1 / (σ * B).trace.re) • (∑ i : Unit, K i * σ * (K i)ᴴ) =
          conditionedState R' σ := by
      rw [hPhi, hqB]
      simp only [conditionedState, G', qR]
      rw [smul_smul]
      congr 1
      field_simp [hqR.ne', hrhi.ne']
    have hbranch :=
      D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.branch_conditioned_trace_distance
        ρ σ K hρpsd hρtrace hσpsd hσtrace hB
    have hweighted := hbranch.2.1 ⟨hp, hq⟩
    have hweighted' :
        max ((ρ * B).trace.re) ((σ * B).trace.re) *
            traceDistance (conditionedState R' ρ) (conditionedState R' σ) ≤
          traceDistance ρ σ := by
      change max ((ρ * B).trace.re) ((σ * B).trace.re) *
          (traceNorm ((1 / (ρ * B).trace.re) • (∑ i : Unit, K i * ρ * (K i)ᴴ) -
            (1 / (σ * B).trace.re) • (∑ i : Unit, K i * σ * (K i)ᴴ)) / 2) ≤
        traceNorm (ρ - σ) / 2 at hweighted
      rw [hnormρ, hnormσ] at hweighted
      simpa [traceDistance] using hweighted
    have hfloorρ : rlo / rhi ≤ (ρ * B).trace.re := by
      rw [hpB]
      have hlo := htraceLower ρ hρ
      rw [Matrix.trace_mul_comm ρ R'] at hlo
      field_simp [hrhi.ne']
      nlinarith
    have hfloorσ : rlo / rhi ≤ (σ * B).trace.re := by
      rw [hqB]
      have hlo := htraceLower σ hσ
      rw [Matrix.trace_mul_comm σ R'] at hlo
      field_simp [hrhi.ne']
      nlinarith
    have hfloorMax : rlo / rhi ≤ max ((ρ * B).trace.re) ((σ * B).trace.re) := by
      rcases le_total ((ρ * B).trace.re) ((σ * B).trace.re) with hpq | hqp
      · rw [max_eq_right hpq]
        exact hfloorσ
      · rw [max_eq_left hqp]
        exact hfloorρ
    have hDcond : 0 ≤ traceDistance (conditionedState R' ρ) (conditionedState R' σ) := by
      exact div_nonneg (traceNorm_nonneg _) (by norm_num)
    have hfloorPos : 0 < rlo / rhi := div_pos hrlo hrhi
    have hscaled : (rlo / rhi) *
          traceDistance (conditionedState R' ρ) (conditionedState R' σ) ≤
        traceDistance ρ σ := by
      exact (mul_le_mul_of_nonneg_right hfloorMax hDcond).trans hweighted'
    have hresult : traceDistance (conditionedState R' ρ) (conditionedState R' σ) ≤
        traceDistance ρ σ / (rlo / rhi) := by
      exact (le_div_iff₀ hfloorPos).2 (by simpa [mul_comm] using hscaled)
    calc
      traceDistance (conditionedState R' ρ) (conditionedState R' σ) ≤
          traceDistance ρ σ / (rlo / rhi) := hresult
      _ = (rhi / rlo) * traceDistance ρ σ := by
        field_simp [hrlo.ne', hrhi.ne']
  have hUpper : ∀ (R' : Matrix (Fin d) (Fin d) ℂ) (hR' : R'.PosDef),
      ∀ ρ σ : Matrix (Fin d) (Fin d) ℂ, IsDensity ρ → IsDensity σ →
        traceDistance (conditionedState R' ρ) (conditionedState R' σ) ≤
          conditionNumber (by omega) R' hR'.isHermitian * traceDistance ρ σ := by
    intro R' hR' ρ σ hρ hσ
    let hH' : R'.IsHermitian := hR'.isHermitian
    let rlo : ℝ := rMin (by omega) R' hH'
    let rhi : ℝ := rMax (by omega) R' hH'
    have hrlo : 0 < rlo := by
      let k : Fin (Fintype.card (Fin d)) := ⟨Fintype.card (Fin d) - 1, by simpa using hd0⟩
      have hp := hH'.posDef_iff_eigenvalues_pos.mp hR'
        ((RHLinalg.eigEquiv (n := Fin d)) k)
      rw [RHLinalg.eigenvalues_eigEquiv hH' k] at hp
      simpa [rlo, rMin, k] using hp
    have hrhi : 0 < rhi := by
      let k : Fin (Fintype.card (Fin d)) := ⟨0, by simpa using hd0⟩
      have hp := hH'.posDef_iff_eigenvalues_pos.mp hR'
        ((RHLinalg.eigEquiv (n := Fin d)) k)
      rw [RHLinalg.eigenvalues_eigEquiv hH' k] at hp
      simpa [rhi, rMax, k] using hp
    have hs' := spectralSandwich R' hR'
    exact hUpperBounds R' hR' rlo rhi hrlo hrhi (by simpa [rlo] using hs'.1)
      (by simpa [rhi] using hs'.2) ρ σ hρ hσ

  have hTwoSided : ∀ ρ σ : Matrix (Fin d) (Fin d) ℂ, IsDensity ρ → IsDensity σ →
      (conditionNumber (by omega) R hH)⁻¹ * traceDistance ρ σ ≤
          traceDistance (conditionedState R ρ) (conditionedState R σ) ∧
        traceDistance (conditionedState R ρ) (conditionedState R σ) ≤
          conditionNumber (by omega) R hH * traceDistance ρ σ := by
    intro ρ σ hρ hσ
    have hupper := hUpper R hR ρ σ hρ hσ
    let rlo : ℝ := rMin (by omega) R hH
    let rhi : ℝ := rMax (by omega) R hH
    have hrlo : 0 < rlo := by
      let k : Fin (Fintype.card (Fin d)) := ⟨Fintype.card (Fin d) - 1, by simpa using hd0⟩
      have hp := hH.posDef_iff_eigenvalues_pos.mp hR
        ((RHLinalg.eigEquiv (n := Fin d)) k)
      rw [RHLinalg.eigenvalues_eigEquiv hH k] at hp
      simpa [rlo, rMin, k] using hp
    have hrhi : 0 < rhi := by
      let k : Fin (Fintype.card (Fin d)) := ⟨0, by simpa using hd0⟩
      have hp := hH.posDef_iff_eigenvalues_pos.mp hR
        ((RHLinalg.eigEquiv (n := Fin d)) k)
      rw [RHLinalg.eigenvalues_eigEquiv hH k] at hp
      simpa [rhi, rMax, k] using hp
    have hs := spectralSandwich R hR
    have hs' : (rlo : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) ≤ R ∧
        R ≤ (rhi : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
      simpa [rlo, rhi] using hs
    have hRinv : R⁻¹.PosDef := hR.inv
    let S : Matrix (Fin d) (Fin d) ℂ := CFC.sqrt R⁻¹
    have hSstar : Sᴴ = S := by
      simpa [S, star_eq_conjTranspose] using (CFC.sqrt_nonneg R⁻¹).isSelfAdjoint.star_eq
    have hSsq : S * S = R⁻¹ := by
      simpa [S] using CFC.sqrt_mul_sqrt_self R⁻¹ hRinv.posSemidef.nonneg
    have hScommInv : Commute S R⁻¹ := by
      have hc := cfcₙ_commute_cfcₙ (R := ℝ) Real.sqrt id R⁻¹
      have hroot : CFC.sqrt R⁻¹ = cfcₙ Real.sqrt R⁻¹ :=
        CFC.sqrt_eq_real_sqrt (a := R⁻¹) (ha := hRinv.posSemidef.nonneg)
      have hid : cfcₙ id R⁻¹ = R⁻¹ := cfcₙ_id ℝ R⁻¹ (ha := hRinv.isHermitian)
      change Commute (CFC.sqrt R⁻¹) R⁻¹
      rw [← hroot, hid] at hc
      exact hc
    letI := hR.isUnit.invertible
    have hScomm : Commute S R := by
      have hh := congrArg (fun T => R * T * R) hScommInv.eq
      have hh' : R * S = S * R := by
        simpa [Matrix.mul_assoc, Matrix.mul_inv_of_invertible, Matrix.inv_mul_of_invertible] using hh
      exact hh'.symm
    have hconjLower : (S * ((rhi : ℝ) • (1 : Matrix (Fin d) (Fin d) ℂ) - R) * S).PosSemidef := by
      simpa [hH.eq, hSstar, Matrix.mul_assoc] using (sub_nonneg.mpr hs'.2).conjTranspose_mul_mul_same S |>.conjTranspose
    have hconjUpper : (S * (R - (rlo : ℝ) • (1 : Matrix (Fin d) (Fin d) ℂ)) * S).PosSemidef := by
      simpa [hH.eq, hSstar, Matrix.mul_assoc] using (sub_nonneg.mpr hs'.1).conjTranspose_mul_mul_same S |>.conjTranspose
    have hinvLower : (rhi⁻¹ : ℝ) • (1 : Matrix (Fin d) (Fin d) ℂ) ≤ R⁻¹ := by
      have hpos : (R⁻¹ - (rhi⁻¹ : ℝ) • (1 : Matrix (Fin d) (Fin d) ℂ)).PosSemidef := by
        rw [show R⁻¹ - (rhi⁻¹ : ℝ) • (1 : Matrix (Fin d) (Fin d) ℂ) =
          (rhi⁻¹ : ℝ) • (S * ((rhi : ℝ) • (1 : Matrix (Fin d) (Fin d) ℂ) - R) * S) by
            calc
              R⁻¹ - (rhi⁻¹ : ℝ) • (1 : Matrix (Fin d) (Fin d) ℂ) =
                  (rhi⁻¹ : ℝ) • ((rhi : ℝ) • (S * S) - S * R * S) := by
                    have hSRprod : S * R * S = R * R⁻¹ := by
                      rw [hScomm.eq, Matrix.mul_assoc, hSsq]
                    rw [hSsq, hSRprod, Matrix.mul_inv_of_invertible]
                    ext i j
                    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
                    by_cases hij : i = j
                    · subst j
                      simp only [ite_true]
                      simp only [Complex.real_smul]
                      rw [Complex.ofReal_inv]
                      field_simp [hrhi.ne']
                    · simp only [hij, ite_false, Complex.real_smul, smul_zero, sub_zero,
                        zero_smul]
                      rw [Complex.ofReal_inv]
                      field_simp [hrhi.ne']
              _ = (rhi⁻¹ : ℝ) • (S * ((rhi : ℝ) • (1 : Matrix (Fin d) (Fin d) ℂ) - R) * S) := by
                    simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
                    noncomm_ring]
        exact hconjLower.smul (inv_pos.mpr hrhi).le
      exact sub_nonneg.mp (Matrix.PosSemidef.nonneg hpos)
    have hinvUpper : R⁻¹ ≤ (rlo⁻¹ : ℝ) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
      have hpos : ((rlo⁻¹ : ℝ) • (1 : Matrix (Fin d) (Fin d) ℂ) - R⁻¹).PosSemidef := by
        rw [show (rlo⁻¹ : ℝ) • (1 : Matrix (Fin d) (Fin d) ℂ) - R⁻¹ =
          (rlo⁻¹ : ℝ) • (S * (R - (rlo : ℝ) • (1 : Matrix (Fin d) (Fin d) ℂ)) * S) by
            calc
              (rlo⁻¹ : ℝ) • (1 : Matrix (Fin d) (Fin d) ℂ) - R⁻¹ =
                  (rlo⁻¹ : ℝ) • (S * R * S - (rlo : ℝ) • (S * S)) := by
                    have hSRprod : S * R * S = R * R⁻¹ := by
                      rw [hScomm.eq, Matrix.mul_assoc, hSsq]
                    rw [hSsq, hSRprod, Matrix.mul_inv_of_invertible]
                    ext i j
                    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
                    by_cases hij : i = j
                    · subst j
                      simp only [ite_true]
                      simp only [Complex.real_smul]
                      rw [Complex.ofReal_inv]
                      field_simp [hrlo.ne']
                    · simp only [hij, ite_false, Complex.real_smul, smul_zero, sub_zero,
                        zero_smul]
                      rw [Complex.ofReal_inv]
                      field_simp [hrlo.ne']
                      ring
              _ = (rlo⁻¹ : ℝ) • (S * (R - (rlo : ℝ) • (1 : Matrix (Fin d) (Fin d) ℂ)) * S) := by
                    simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
                    noncomm_ring]
        exact hconjUpper.smul (inv_pos.mpr hrlo).le
      exact sub_nonneg.mp (Matrix.PosSemidef.nonneg hpos)
    have hInvUpper := hUpperBounds R⁻¹ hRinv (rhi⁻¹) (rlo⁻¹)
      (inv_pos.mpr hrhi) (inv_pos.mpr hrlo) hinvLower hinvUpper
    have hGstarR : (CFC.sqrt R)ᴴ = CFC.sqrt R := by
      simpa [star_eq_conjTranspose] using (CFC.sqrt_nonneg R).isSelfAdjoint.star_eq
    have hGsqR : CFC.sqrt R * CFC.sqrt R = R := by
      simpa using CFC.sqrt_mul_sqrt_self R hR.posSemidef.nonneg
    have htraceLowerR : ∀ X : Matrix (Fin d) (Fin d) ℂ, IsDensity X →
        rlo ≤ (X * R).trace.re := by
      intro X hX
      have ht := RHLinalg.trace_mul_nonneg_of_posSemidef hX.1 (sub_nonneg.mpr hs'.1)
      have ht' : 0 ≤ (X * R).trace.re - rlo := by
        simpa [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_sub,
          Matrix.trace_smul, hX.2, Complex.sub_re, Complex.real_smul] using ht
      linarith
    have hCondDensity : ∀ X : Matrix (Fin d) (Fin d) ℂ, IsDensity X →
        IsDensity (conditionedState R X) := by
      intro X hX
      have htrpos : 0 < (R * X).trace.re := by
        rw [Matrix.trace_mul_comm R X]
        exact lt_of_lt_of_le hrlo (htraceLowerR X hX)
      have hbase : (CFC.sqrt R * X * CFC.sqrt R).PosSemidef := by
        simpa [hGstarR, hX.1.1.eq, Matrix.mul_assoc] using
          ((hX.1.conjTranspose_mul_mul_same (CFC.sqrt R)).conjTranspose)
      have hpsd : (conditionedState R X).PosSemidef := by
        simpa [conditionedState] using
          hbase.smul (one_div_nonneg.mpr (le_of_lt htrpos))
      refine ⟨hpsd, ?_⟩
      simp only [conditionedState]
      rw [Matrix.trace_smul]
      have htrace : (CFC.sqrt R * X * CFC.sqrt R).trace = (R * X).trace := by
        rw [Matrix.trace_mul_cycle, hGsqR]
      have hstar : star ((R * X).trace) = (R * X).trace := by
        rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hX.1.1.eq, hH.eq,
          Matrix.trace_mul_comm]
      have htraceReal : (R * X).trace = ((R * X).trace.re : ℂ) := by
        apply Complex.ext
        · simp
        · have him := congrArg Complex.im hstar
          change ((starRingEnd ℂ) ((R * X).trace)).im = _ at him
          rw [Complex.conj_im] at him
          have him' : (R * X).trace.im = 0 := by linarith
          simpa [him']
      rw [htrace, htraceReal]
      simp only [Complex.real_smul]
      simp only [one_div, Complex.ofReal_re, Complex.ofReal_inv]
      field_simp [htrpos.ne']
    have hτinv : ∀ X : Matrix (Fin d) (Fin d) ℂ, IsDensity X →
        conditionedState R⁻¹ (conditionedState R X) = X := by
      intro X hX
      have htr : (R * X).trace.re ≠ 0 := by
        rw [Matrix.trace_mul_comm R X]
        exact ne_of_gt (lt_of_lt_of_le hrlo (htraceLowerR X hX))
      have hGunit : IsUnit (CFC.sqrt R) :=
        CFC.isUnit_sqrt_iff_isStrictlyPositive.mpr hR.isStrictlyPositive
      letI := hGunit.invertible
      simp only [conditionedState]
      have hG : CFC.sqrt R⁻¹ * (CFC.sqrt R * X * CFC.sqrt R) * CFC.sqrt R⁻¹ = X := by
        rw [← PosSemidef.inv_sqrt hR.posSemidef]
        simp [Matrix.mul_assoc, Matrix.inv_mul_of_invertible, Matrix.mul_inv_of_invertible]
      have hRinvSq : (CFC.sqrt R)⁻¹ * (CFC.sqrt R)⁻¹ = R⁻¹ := by
        simpa [S, ← PosSemidef.inv_sqrt hR.posSemidef] using hSsq
      have hG' : (CFC.sqrt R)⁻¹ * (CFC.sqrt R * X * CFC.sqrt R) *
          (CFC.sqrt R)⁻¹ = X := by
        simpa [← PosSemidef.inv_sqrt hR.posSemidef] using hG
      have hcore : (R⁻¹ * (CFC.sqrt R * X * CFC.sqrt R)).trace = 1 := by
        calc
          (R⁻¹ * (CFC.sqrt R * X * CFC.sqrt R)).trace =
              ((CFC.sqrt R)⁻¹ * (CFC.sqrt R)⁻¹ *
                (CFC.sqrt R * X * CFC.sqrt R)).trace := by rw [hRinvSq]
          _ = ((CFC.sqrt R)⁻¹ * (CFC.sqrt R * X * CFC.sqrt R) *
                (CFC.sqrt R)⁻¹).trace := by
            rw [← Matrix.trace_mul_cycle]
          _ = X.trace := by rw [hG']
          _ = 1 := hX.2
      simp only [conditionedState, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul]
      simp [Complex.real_smul, hcore, htr, hG, smul_smul]
    have hreverse : traceDistance ρ σ ≤
        (rhi / rlo) * traceDistance (conditionedState R ρ) (conditionedState R σ) := by
      have hh := hInvUpper (conditionedState R ρ) (conditionedState R σ)
        (hCondDensity ρ hρ) (hCondDensity σ hσ)
      rw [hτinv ρ hρ, hτinv σ hσ] at hh
      simpa [div_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hh
    constructor
    · have hk : 0 < rhi / rlo := div_pos hrhi hrlo
      have hh := mul_le_mul_of_nonneg_left hreverse (le_of_lt (inv_pos.mpr hk))
      have hh' : (rhi / rlo)⁻¹ * traceDistance ρ σ ≤
          traceDistance (conditionedState R ρ) (conditionedState R σ) := by
        calc
          (rhi / rlo)⁻¹ * traceDistance ρ σ ≤
              (rhi / rlo)⁻¹ * ((rhi / rlo) *
                traceDistance (conditionedState R ρ) (conditionedState R σ)) := hh
          _ = traceDistance (conditionedState R ρ) (conditionedState R σ) := by
            field_simp [ne_of_gt hk]
      simpa [conditionNumber, rlo, rhi] using hh'
    · exact hupper

  let densityOfMatrix (X : Matrix (Fin d) (Fin d) ℂ) (hX : IsDensity X) :
      DensityState (Fin d) :=
    ⟨CStarMatrix.ofMatrix X, map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hX.1.nonneg,
      by
        change Matrix.trace (CStarMatrix.ofMatrix X) = 1
        exact hX.2⟩
  have rawDensityOfDensity (ρ : DensityState (Fin d)) :
      IsDensity (CStarMatrix.ofMatrix.symm ρ.val) := by
    constructor
    · change (CStarMatrix.ofMatrixStarAlgEquiv.symm ρ.val).PosSemidef
      simpa [CStarMatrix.ofMatrix_eq_ofMatrixStarAlgEquiv] using
        (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm ρ.prop.1).posSemidef
    · change Matrix.trace (CStarMatrix.ofMatrixStarAlgEquiv.symm ρ.val) = 1
      exact ρ.prop.2
  have conditionedState_val (X : Matrix (Fin d) (Fin d) ℂ) (hX : IsDensity X) :
      CStarMatrix.ofMatrix.symm
          (D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.conditionedState
            (by omega) R hR (densityOfMatrix X hX)).val = conditionedState R X := by
    rfl
  have conditionedState_density_val (ρ : DensityState (Fin d)) :
      CStarMatrix.ofMatrix.symm
          (D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.conditionedState
            (by omega) R hR ρ).val = conditionedState R (CStarMatrix.ofMatrix.symm ρ.val) := by
    rfl
  let rawRatioSet : Set ℝ := {x : ℝ | ∃ ρ σ : Matrix (Fin d) (Fin d) ℂ,
    IsDensity ρ ∧ IsDensity σ ∧ ρ ≠ σ ∧
      x = traceDistance (conditionedState R ρ) (conditionedState R σ) /
        traceDistance ρ σ}
  have ratioSet_eq :
      {x : ℝ | ∃ ρ σ : DensityState (Fin d), ρ ≠ σ ∧
        x = D5.S3.Quantum.Foundation.FiniteTraceDistance.traceDistance
          (D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.conditionedState
            (by omega) R hR ρ)
          (D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.conditionedState
            (by omega) R hR σ) /
          D5.S3.Quantum.Foundation.FiniteTraceDistance.traceDistance ρ σ} = rawRatioSet := by
    ext x
    constructor
    · rintro ⟨ρ, σ, hne, hx⟩
      refine ⟨CStarMatrix.ofMatrix.symm ρ.val, CStarMatrix.ofMatrix.symm σ.val,
        rawDensityOfDensity ρ, rawDensityOfDensity σ, ?_, ?_⟩
      · intro h
        apply hne
        apply Subtype.ext
        simpa using congrArg CStarMatrix.ofMatrix h
      · simpa [D5.S3.Quantum.Foundation.FiniteTraceDistance.traceDistance,
          conditionedState_density_val] using hx
    · rintro ⟨ρ, σ, hρ, hσ, hne, hx⟩
      let ρ' := densityOfMatrix ρ hρ
      let σ' := densityOfMatrix σ hσ
      have hne' : ρ' ≠ σ' := by
        intro h
        apply hne
        have hv := congrArg (fun q : DensityState (Fin d) =>
          CStarMatrix.ofMatrix.symm q.val) h
        simpa [ρ', σ', densityOfMatrix] using hv
      refine ⟨ρ', σ', hne', ?_⟩
      dsimp [ρ', σ']
      rw [D5.S3.Quantum.Foundation.FiniteTraceDistance.traceDistance,
        conditionedState_val ρ hρ, conditionedState_val σ hσ]
      exact hx

  have equalExtreme : ∀ ρ : DensityState (Fin d),
      rMin (by omega) R hH = rMax (by omega) R hH →
        D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.conditionedState
          (by omega) R hR ρ = ρ := by
    intro ρ heq
    let r : ℝ := rMin (by omega) R hH
    have hr : 0 < r := by
      dsimp [r]
      let k : Fin (Fintype.card (Fin d)) :=
        ⟨Fintype.card (Fin d) - 1, by simpa using hd0⟩
      have hp := hH.posDef_iff_eigenvalues_pos.mp hR
        ((RHLinalg.eigEquiv (n := Fin d)) k)
      rw [RHLinalg.eigenvalues_eigEquiv hH k] at hp
      simpa [rMin, k] using hp
    have hRscalar : R = (r : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
      have hs := spectralSandwich R hR
      have hu : R ≤ (r : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
        simpa [r, heq] using hs.2
      have hl : (r : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) ≤ R := by
        simpa [r] using hs.1
      exact le_antisymm hu hl
    have hG : CFC.sqrt R = (Real.sqrt r : ℂ) •
        (1 : Matrix (Fin d) (Fin d) ℂ) := by
      let rr : NNReal := ⟨r, hr.le⟩
      have hscalar : (r : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) =
          algebraMap NNReal (Matrix (Fin d) (Fin d) ℂ) rr := by
        rw [Algebra.algebraMap_eq_smul_one]
        change (r : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) =
          (rr : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)
        congr 1
      calc
        CFC.sqrt R = CFC.sqrt ((r : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) := by
          rw [hRscalar]
        _ = (Real.sqrt r : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
          rw [hscalar, CFC.sqrt_algebraMap]
          rw [Algebra.algebraMap_eq_smul_one]
          change (↑(NNReal.sqrt rr) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) = _
          congr 1
          have hnon : 0 ≤ (NNReal.sqrt rr : ℝ) := (NNReal.sqrt rr).property
          have hrnon : 0 ≤ r := hr.le
          have hsq : (NNReal.sqrt rr : ℝ) ^ 2 = r := by
            have h := congrArg (fun x : NNReal => (x : ℝ)) (NNReal.sq_sqrt rr)
            change (NNReal.sqrt rr : ℝ) ^ 2 = r at h
            exact h
          have hrealnon : 0 ≤ Real.sqrt r := Real.sqrt_nonneg r
          have hreal : (NNReal.sqrt rr : ℝ) = Real.sqrt r := by
            nlinarith [hsq, Real.sq_sqrt hrnon, hrealnon]
          exact_mod_cast hreal
    apply Subtype.ext
    change CStarMatrix.ofMatrix.symm
        (D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.conditionedState
          (by omega) R hR ρ).val = CStarMatrix.ofMatrix.symm ρ.val
    let X : Matrix (Fin d) (Fin d) ℂ := CStarMatrix.ofMatrix.symm ρ.val
    change (1 / (R * X).trace.re) • (CFC.sqrt R * X * CFC.sqrt R) = X
    have htrace : Matrix.trace X = 1 := by
      change Matrix.trace (CStarMatrix.ofMatrix.symm ρ.val) = 1
      exact ρ.prop.2
    rw [hG, hRscalar]
    have hsqrt : (Real.sqrt r : ℂ) ^ 2 = (r : ℂ) := by
      exact_mod_cast (Real.sq_sqrt hr.le)
    ext a b
    simp [Matrix.smul_apply, Matrix.mul_apply, Matrix.one_apply, htrace,
      Complex.real_smul]
    calc
      (↑r : ℂ)⁻¹ * ((Real.sqrt r : ℂ) *
          ((Real.sqrt r : ℂ) * X a b)) =
        (↑r : ℂ)⁻¹ * ((Real.sqrt r : ℂ) ^ 2 *
          X a b) := by ring
      _ = X a b := by
        rw [hsqrt]
        field_simp [hr.ne']

  refine ⟨?_, ?_, ?_⟩
  · intro ρ σ
    have hraw := hTwoSided (CStarMatrix.ofMatrix.symm ρ.val)
      (CStarMatrix.ofMatrix.symm σ.val) (rawDensityOfDensity ρ)
      (rawDensityOfDensity σ)
    simpa [D5.S3.Quantum.Foundation.FiniteTraceDistance.traceDistance,
      conditionedState_density_val] using hraw
  · exact equalExtreme
  · rw [ratioSet_eq]
    let kMin : Fin (Fintype.card (Fin d)) :=
        ⟨Fintype.card (Fin d) - 1, by simpa using hd0⟩
    let kMax : Fin (Fintype.card (Fin d)) := ⟨0, by simpa using hd0⟩
    let kOne : Fin (Fintype.card (Fin d)) :=
      ⟨1, by simpa using (show 1 < d by omega)⟩
    let iMin : Fin d := (RHLinalg.eigEquiv (n := Fin d)) kMin
    let iMax : Fin d := (RHLinalg.eigEquiv (n := Fin d)) kMax
    let iOne : Fin d := (RHLinalg.eigEquiv (n := Fin d)) kOne
    let v (i : Fin d) : Fin d → ℂ :=
      ⇑(hH.eigenvectorBasis i)
    have hvnorm (i : Fin d) :
        star (v i) ⬝ᵥ v i = 1 := by
      have hn := hH.eigenvectorBasis.orthonormal.norm_eq_one i
      have hi := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (hH.eigenvectorBasis i)
      rw [EuclideanSpace.inner_eq_star_dotProduct] at hi
      simpa [v, dotProduct_comm, hn] using hi
    have heig (i : Fin d) :
        R *ᵥ v i = (hH.eigenvalues i : ℂ) • v i := by
      simpa [v] using hH.mulVec_eigenvectorBasis i
    let P (i : Fin d) : Matrix (Fin d) (Fin d) ℂ :=
      Matrix.vecMulVec (v i) (star (v i))
    have hPpsd (i : Fin d) : (P i).PosSemidef := by
      exact Matrix.posSemidef_vecMulVec_self_star (v i)
    have hPtrace (i : Fin d) : (P i).trace = 1 := by
      change Matrix.trace (Matrix.vecMulVec (v i) (star (v i))) = 1
      rw [Matrix.trace_vecMulVec]
      simpa [dotProduct_comm] using hvnorm i
    have hPleft (i : Fin d) :
        R * P i = (hH.eigenvalues i : ℂ) • P i := by
      change R * Matrix.vecMulVec (v i) (star (v i)) =
        (hH.eigenvalues i : ℂ) • Matrix.vecMulVec (v i) (star (v i))
      rw [Matrix.mul_vecMulVec, heig]
      simp [Matrix.smul_vecMulVec]
    have hPright (i : Fin d) :
        P i * R = (hH.eigenvalues i : ℂ) • P i := by
      have h := congrArg Matrix.conjTranspose (hPleft i)
      simpa [P, Matrix.conjTranspose_mul, hH.eq, Matrix.conjTranspose_smul] using h
    have hPorth (i j : Fin d) (hij : i ≠ j) :
        P i * P j = 0 := by
      change Matrix.vecMulVec (v i) (star (v i)) *
          Matrix.vecMulVec (v j) (star (v j)) = 0
      rw [Matrix.vecMulVec_mul_vecMulVec]
      have ho := hH.eigenvectorBasis.orthonormal.inner_eq_zero hij
      have hodot : star (v i) ⬝ᵥ v j = 0 := by
        rw [dotProduct_comm]
        exact (EuclideanSpace.inner_eq_star_dotProduct _ _).symm.trans
          (by simpa using ho)
      simp [hodot]
    have hPstar (i : Fin d) : (P i)ᴴ = P i := by
      change (Matrix.vecMulVec (v i) (star (v i)))ᴴ = _
      rw [Matrix.conjTranspose_vecMulVec]
      simp [P]
    have hPidemp (i : Fin d) : P i * P i = P i := by
      change Matrix.vecMulVec (v i) (star (v i)) *
          Matrix.vecMulVec (v i) (star (v i)) =
        Matrix.vecMulVec (v i) (star (v i))
      rw [Matrix.vecMulVec_mul_vecMulVec]
      simp [hvnorm]
    have hsumP : (∑ j : Fin d, P j) = (1 : Matrix (Fin d) (Fin d) ℂ) := by
      have hUU := Unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2
      ext a b
      have hab := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M a b) hUU
      simp only [Matrix.sum_apply, P, Matrix.vecMulVec_apply]
      simpa only [v, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.star_apply, Pi.star_apply,
        Matrix.IsHermitian.eigenvectorUnitary_apply] using hab
    have hPcomp (i : Fin d) : (1 - P i).PosSemidef := by
      have hsumErase :
          (Finset.univ.erase i).sum P = 1 - P i := by
        have hs := Finset.sum_erase_add (Finset.univ : Finset (Fin d)) P
          (Finset.mem_univ i)
        calc
          (Finset.univ.erase i).sum P =
              ((Finset.univ.erase i).sum P + P i) - P i := by abel
          _ = (Finset.univ.sum P) - P i := by rw [hs]
          _ = 1 - P i := by rw [hsumP]
      rw [← hsumErase]
      exact Matrix.posSemidef_sum _ (fun j _ => hPpsd j)
    have hGstar : (CFC.sqrt R)ᴴ = CFC.sqrt R := by
      simpa [star_eq_conjTranspose] using (CFC.sqrt_nonneg R).isSelfAdjoint.star_eq
    have hGsq : CFC.sqrt R * CFC.sqrt R = R := by
      simpa using CFC.sqrt_mul_sqrt_self R hR.posSemidef.nonneg
    have hGPcomm (i : Fin d) : Commute (CFC.sqrt R) (P i) := by
      have hRP : Commute R (P i) := by
        show R * P i = P i * R
        rw [hPleft i, hPright i]
      have hc := hRP.cfcₙ_real Real.sqrt
      rw [CFC.sqrt_eq_real_sqrt (a := R) (ha := hR.posSemidef.nonneg)]
      exact hc
    have hFilter (i : Fin d) :
        CFC.sqrt R * P i * CFC.sqrt R = (hH.eigenvalues i : ℂ) • P i := by
      calc
        CFC.sqrt R * P i * CFC.sqrt R = P i * CFC.sqrt R * CFC.sqrt R := by
          rw [(hGPcomm i).eq, Matrix.mul_assoc]
        _ = P i * R := by rw [Matrix.mul_assoc, hGsq]
        _ = (hH.eigenvalues i : ℂ) • P i := hPright i
    have htraceRP (i : Fin d) :
        (R * P i).trace.re = hH.eigenvalues i := by
      rw [hPleft i, Matrix.trace_smul, hPtrace i]
      simp [Complex.real_smul]
    have hEigPos (i : Fin d) : 0 < hH.eigenvalues i := by
      exact hH.posDef_iff_eigenvalues_pos.mp hR i
    have hTauP (i : Fin d) : conditionedState R (P i) = P i := by
      dsimp [conditionedState]
      rw [htraceRP i, hFilter i]
      ext a b
      simp [Complex.real_smul]
      field_simp [show (hH.eigenvalues i : ℂ) ≠ 0 by
        exact_mod_cast (ne_of_gt (hEigPos i))]
    have hProjBranch (i : Fin d) (X Y : Matrix (Fin d) (Fin d) ℂ)
        (hX : IsDensity X) (hY : IsDensity Y) :
        |(X * P i).trace.re - (Y * P i).trace.re| ≤ traceDistance X Y := by
      let K : Unit → Matrix (Fin d) (Fin d) ℂ := fun _ => P i
      have hB : (∑ j : Unit, (K j)ᴴ * K j) ≤
          (1 : Matrix (Fin d) (Fin d) ℂ) := by
        have hsumK : (∑ j : Unit, (K j)ᴴ * K j) = P i := by
          simp [K, hPstar i, hPidemp i]
        rw [hsumK]
        have hsub : (0 : Matrix (Fin d) (Fin d) ℂ) ≤
            (1 : Matrix (Fin d) (Fin d) ℂ) - P i := (hPcomp i).nonneg
        exact sub_nonneg.mp hsub
      have hb :=
        D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.branch_conditioned_trace_distance
          X Y K hX.1 hX.2 hY.1 hY.2 hB
      have hb1 := hb.1
      change |((X * (∑ j : Unit, (K j)ᴴ * K j)).trace.re) -
          ((Y * (∑ j : Unit, (K j)ᴴ * K j)).trace.re)| ≤
        traceNorm (X - Y) / 2 at hb1
      simpa [K, hPstar i, hPidemp i, traceDistance] using hb1
    have hNormP (c : ℝ) (hc : 0 ≤ c) (i : Fin d) :
        traceNorm (c • P i) = c := by
      have hh := congrArg Complex.re
        (traceNorm_of_posSemidef ((hPpsd i).smul hc))
      simpa [Matrix.trace_smul, hPtrace i, Complex.real_smul] using hh
    have hOrthDistance (i j : Fin d) (hij : i ≠ j) :
        traceDistance (P i) (P j) = 1 := by
      have hPi : IsDensity (P i) := ⟨hPpsd i, hPtrace i⟩
      have hPj : IsDensity (P j) := ⟨hPpsd j, hPtrace j⟩
      have hlow := hProjBranch i (P i) (P j) hPi hPj
      have hprob :
          |((P i * P i).trace.re) - ((P j * P i).trace.re)| = 1 := by
        rw [hPidemp i, hPorth j i (Ne.symm hij), hPtrace i]
        norm_num
      rw [hprob] at hlow
      have hdiff : P i - P j = (1 : ℝ) • P i + -((1 : ℝ) • P j) := by
        ext a b
        simp only [one_smul]
        abel
      have hupp : traceDistance (P i) (P j) ≤ 1 := by
        dsimp [traceDistance]
        rw [hdiff]
        calc
          traceNorm ((1 : ℝ) • P i + -((1 : ℝ) • P j)) / 2 ≤
              (traceNorm ((1 : ℝ) • P i) + traceNorm (-((1 : ℝ) • P j))) / 2 := by
            gcongr
            exact traceNorm_add_le _ _
          _ = 1 := by
            rw [hNormP 1 (by norm_num) i, traceNorm_neg, hNormP 1 (by norm_num) j]
            norm_num
      exact le_antisymm hupp hlow
    have hEigMin : hH.eigenvalues iMin = rMin (by omega) R hH := by
      simpa [iMin, kMin, rMin] using RHLinalg.eigenvalues_eigEquiv hH kMin
    have hEigMax : hH.eigenvalues iMax = rMax (by omega) R hH := by
      simpa [iMax, kMax, rMax] using RHLinalg.eigenvalues_eigEquiv hH kMax
    have hiMinMax : iMin ≠ iMax := by
      intro h
      have hk : kMin = kMax := (RHLinalg.eigEquiv (n := Fin d)).injective h
      simp [kMin, kMax, hd] at hk
      omega
    have hiMaxOne : iMax ≠ iOne := by
      intro h
      have hk : kMax = kOne := (RHLinalg.eigEquiv (n := Fin d)).injective h
      simp [kMax, kOne, hd] at hk
    have hrMinPos : 0 < rMin (by omega) R hH := by
      rw [← hEigMin]
      exact hEigPos iMin
    have hrMaxPos : 0 < rMax (by omega) R hH := by
      rw [← hEigMax]
      exact hEigPos iMax
    by_cases heq : rMin (by omega) R hH = rMax (by omega) R hH
    · have hkEq : conditionNumber (by omega) R hH = 1 := by
        simp [conditionNumber, heq, ne_of_gt hrMinPos, ne_of_gt hrMaxPos]
      have hmember : conditionNumber (by omega) R hH ∈
          {x : ℝ | ∃ ρ σ : Matrix (Fin d) (Fin d) ℂ,
            IsDensity ρ ∧ IsDensity σ ∧ ρ ≠ σ ∧
              x = traceDistance (conditionedState R ρ) (conditionedState R σ) /
                traceDistance ρ σ} := by
        refine ⟨P iMax, P iOne, ⟨hPpsd iMax, hPtrace iMax⟩,
          ⟨hPpsd iOne, hPtrace iOne⟩, ?_, ?_⟩
        · intro h
          have hz0 : traceDistance (P iMax) (P iOne) = 0 := by
            rw [h]
            simp [traceDistance, traceNorm]
          rw [hOrthDistance iMax iOne hiMaxOne] at hz0
          norm_num at hz0
        · rw [hTauP iMax, hTauP iOne, hOrthDistance iMax iOne hiMaxOne, hkEq]
          norm_num
      refine ⟨?_, ?_⟩
      · intro x hx
        rcases hx with ⟨ρ, σ, hρ, hσ, hne, rfl⟩
        have hu := (hTwoSided ρ σ hρ hσ).2
        by_cases hz : traceDistance ρ σ = 0
        · have hnon : 0 ≤ traceDistance (conditionedState R ρ) (conditionedState R σ) := by
            change 0 ≤ traceNorm (conditionedState R ρ - conditionedState R σ) / 2
            exact div_nonneg
              (D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm_nonneg _)
              (by norm_num)
          have hz' : traceDistance (conditionedState R ρ) (conditionedState R σ) = 0 := by
            have hle : traceDistance (conditionedState R ρ) (conditionedState R σ) ≤ 0 := by
              simpa [hkEq, hz] using hu
            exact le_antisymm hle hnon
          simp [hz, hz']
          exact (div_pos hrMaxPos hrMinPos).le
        · have hdpos : 0 < traceDistance ρ σ :=
            lt_of_le_of_ne (div_nonneg (traceNorm_nonneg _) (by norm_num)) (Ne.symm hz)
          apply (div_le_iff₀ hdpos).2
          simpa [hkEq] using hu
      · intro b hb
        exact (hb hmember)
    · let rlo : ℝ := rMin (by omega) R hH
      let rhi : ℝ := rMax (by omega) R hH
      let σe (e : ℝ) : Matrix (Fin d) (Fin d) ℂ :=
        (1 - e) • P iMin + e • P iMax
      let δ (e : ℝ) : ℝ := (1 - e) * rlo + e * rhi
      have hSigmaDensity (e : ℝ) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
          IsDensity (σe e) := by
        constructor
        · dsimp [σe]
          exact (hPpsd iMin).smul (sub_nonneg.mpr he1) |>.add
            ((hPpsd iMax).smul he0)
        · dsimp [σe]
          rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
            hPtrace iMin, hPtrace iMax]
          simp [Complex.real_smul]
      have hSigmaR (e : ℝ) :
          R * σe e = (1 - e) • ((rlo : ℂ) • P iMin) +
            e • ((rhi : ℂ) • P iMax) := by
        dsimp [σe, rlo, rhi]
        rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul,
          hPleft iMin, hPleft iMax, hEigMin, hEigMax]
        ext a b
        simp [Matrix.smul_apply, Complex.real_smul, Complex.ofReal_mul]
      have hSigmaFilter (e : ℝ) :
          CFC.sqrt R * σe e * CFC.sqrt R =
            (1 - e) • ((rlo : ℂ) • P iMin) +
              e • ((rhi : ℂ) • P iMax) := by
        dsimp [σe, rlo, rhi]
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul]
        rw [hFilter iMin, hFilter iMax, hEigMin, hEigMax]
        ext a b
        simp [Matrix.smul_apply, Complex.real_smul, Complex.ofReal_mul]
      have hDeltaPos (e : ℝ) (he0 : 0 ≤ e) (he1 : e < 1) : 0 < δ e := by
        dsimp [δ]
        have hlo : 0 < (1 - e) * rlo := mul_pos (sub_pos.mpr he1) hrMinPos
        have hhi : 0 ≤ e * rhi := mul_nonneg he0 hrMaxPos.le
        linarith
      have hSigmaTrace (e : ℝ) : (R * σe e).trace.re = δ e := by
        rw [hSigmaR]
        simp [Matrix.trace_add, Matrix.trace_smul, hPtrace iMin, hPtrace iMax,
          δ, Complex.real_smul]
      have hTauSigma (e : ℝ) (he0 : 0 ≤ e) (he1 : e < 1) :
          conditionedState R (σe e) =
            (((1 - e) * rlo / δ e) : ℝ) • P iMin +
              ((e * rhi / δ e) : ℝ) • P iMax := by
        dsimp [conditionedState]
        rw [hSigmaTrace, hSigmaFilter]
        ext a b
        simp [Matrix.smul_apply, Complex.real_smul, Complex.ofReal_mul]
        field_simp [ne_of_gt (hDeltaPos e he0 he1)]
      have hTauSigmaDensity (e : ℝ) (he0 : 0 ≤ e) (he1 : e < 1) :
          IsDensity (conditionedState R (σe e)) := by
        rw [hTauSigma e he0 he1]
        constructor
        · exact (hPpsd iMin).smul (div_nonneg (mul_nonneg (sub_nonneg.mpr he1.le) hrMinPos.le)
            (hDeltaPos e he0 he1).le) |>.add
            ((hPpsd iMax).smul (div_nonneg (mul_nonneg he0 hrMaxPos.le)
              (hDeltaPos e he0 he1).le))
        · rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
            hPtrace iMin, hPtrace iMax]
          simp [Complex.real_smul, δ]
          have hden : -e * rlo + e * rhi + rlo ≠ 0 := by
            nlinarith [hDeltaPos e he0 he1]
          norm_cast
          rw [div_eq_mul_inv, div_eq_mul_inv]
          calc
            (1 - e) * rlo * ((1 - e) * rlo + e * rhi)⁻¹ +
                e * rhi * ((1 - e) * rlo + e * rhi)⁻¹ =
                ((1 - e) * rlo + e * rhi) *
                  ((1 - e) * rlo + e * rhi)⁻¹ := by ring
            _ = 1 := by
              apply mul_inv_cancel₀
              exact ne_of_gt (hDeltaPos e he0 he1)
      have hSourceUpper (e : ℝ) (he0 : 0 ≤ e) :
          traceDistance (P iMin) (σe e) ≤ e := by
        have hdiff : P iMin - σe e = e • P iMin + -(e • P iMax) := by
          dsimp [σe]
          ext a b
          simp [Matrix.smul_apply]
          ring_nf
        dsimp [traceDistance]
        rw [hdiff]
        calc
          traceNorm (e • P iMin + -(e • P iMax)) / 2 ≤
              (traceNorm (e • P iMin) + traceNorm (-(e • P iMax))) / 2 := by
            gcongr
            exact traceNorm_add_le _ _
          _ = e := by
            rw [hNormP e he0 iMin, traceNorm_neg, hNormP e he0 iMax]
            ring
      have hImageLower (e : ℝ) (he0 : 0 ≤ e) (he1 : e < 1) :
          e * rhi / δ e ≤
            traceDistance (conditionedState R (P iMin))
              (conditionedState R (σe e)) := by
        have hPi : IsDensity (P iMin) := ⟨hPpsd iMin, hPtrace iMin⟩
        have hprobTau :
            ((conditionedState R (σe e) * P iMin).trace.re) =
              (1 - e) * rlo / δ e := by
          rw [hTauSigma e he0 he1]
          simp only [Matrix.add_mul, Matrix.smul_mul, hPidemp iMin,
            hPorth iMax iMin (Ne.symm hiMinMax), zero_mul, Matrix.trace_add,
            Matrix.trace_smul, hPtrace iMin, Complex.real_smul, Matrix.trace_zero,
            add_zero, zero_add]
          norm_num
        have hprob :
            (P iMin * P iMin).trace.re -
                (conditionedState R (σe e) * P iMin).trace.re =
              e * rhi / δ e := by
          rw [hPidemp iMin, hPtrace iMin, hprobTau]
          have hden : δ e ≠ 0 := ne_of_gt (hDeltaPos e he0 he1)
          field_simp [hden]
          norm_num
          ring
        have hb := hProjBranch iMin (P iMin) (conditionedState R (σe e)) hPi
          (hTauSigmaDensity e he0 he1)
        rw [hprob] at hb
        rw [abs_of_nonneg (div_nonneg (mul_nonneg he0 hrMaxPos.le)
          (hDeltaPos e he0 he1).le)] at hb
        simpa [hTauP iMin] using hb
      have hSourceLower (e : ℝ) (he0 : 0 < e) (he1 : e < 1) :
          e ≤ traceDistance (P iMin) (σe e) := by
        have hPi : IsDensity (P iMin) := ⟨hPpsd iMin, hPtrace iMin⟩
        have hprob :
            (P iMin * P iMin).trace.re - (σe e * P iMin).trace.re = e := by
          rw [hPidemp iMin, hPtrace iMin]
          dsimp [σe]
          simp only [Matrix.add_mul, Matrix.smul_mul,
            hPidemp iMin, hPorth iMax iMin (Ne.symm hiMinMax), zero_mul,
            Matrix.trace_add, Matrix.trace_smul, hPtrace iMin,
            Complex.real_smul, Matrix.trace_zero, add_zero, zero_add]
          ring
          norm_num [Complex.ofReal_re]
        have hb := hProjBranch iMin (P iMin) (σe e) hPi
          (hSigmaDensity e he0.le he1.le)
        rw [hprob, abs_of_pos he0] at hb
        exact hb
      have hRatioLower (e : ℝ) (he0 : 0 < e) (he1 : e < 1) :
          rhi / δ e ≤
            traceDistance (conditionedState R (P iMin))
              (conditionedState R (σe e)) /
              traceDistance (P iMin) (σe e) := by
        have hsrc : 0 < traceDistance (P iMin) (σe e) :=
          lt_of_lt_of_le he0 (hSourceLower e he0 he1)
        have hcoef : 0 ≤ rhi / δ e :=
          div_nonneg hrMaxPos.le (hDeltaPos e he0.le he1).le
        apply (le_div_iff₀ hsrc).2
        calc
          (rhi / δ e) * traceDistance (P iMin) (σe e) ≤
              (rhi / δ e) * e :=
            mul_le_mul_of_nonneg_left (hSourceUpper e he0.le) hcoef
          _ = e * rhi / δ e := by ring
          _ ≤ traceDistance (conditionedState R (P iMin))
              (conditionedState R (σe e)) := hImageLower e he0.le he1
      refine ⟨?_, ?_⟩
      · intro x hx
        rcases hx with ⟨ρ, σ, hρ, hσ, hne, rfl⟩
        have hu := (hTwoSided ρ σ hρ hσ).2
        by_cases hz : traceDistance ρ σ = 0
        · have hnon : 0 ≤ traceDistance (conditionedState R ρ)
              (conditionedState R σ) := by
            exact div_nonneg (traceNorm_nonneg _) (by norm_num)
          have hz' : traceDistance (conditionedState R ρ)
              (conditionedState R σ) = 0 := by
            have hle : traceDistance (conditionedState R ρ)
                (conditionedState R σ) ≤ 0 := by
              simpa [hz] using hu
            exact le_antisymm hle hnon
          simp [hz, hz']
          exact (div_pos hrMaxPos hrMinPos).le
        · have hpos : 0 < traceDistance ρ σ :=
            lt_of_le_of_ne (div_nonneg (traceNorm_nonneg _) (by norm_num))
              (Ne.symm hz)
          apply (div_le_iff₀ hpos).2
          simpa [conditionNumber, rlo, rhi] using hu
      · intro b hb
        have hfamily : ∀ e : ℝ, 0 < e → e < 1 → rhi / δ e ≤ b := by
          intro e he0 he1
          have hne : P iMin ≠ σe e := by
            intro hEq
            have hzero : traceDistance (P iMin) (σe e) = 0 := by
              rw [hEq]
              dsimp [traceDistance]
              simp [traceNorm]
            have hlow := hSourceLower e he0 he1
            rw [hzero] at hlow
            linarith
          have hmem :
              traceDistance (conditionedState R (P iMin))
                  (conditionedState R (σe e)) /
                traceDistance (P iMin) (σe e) ∈
                {x : ℝ | ∃ ρ σ : Matrix (Fin d) (Fin d) ℂ,
                  IsDensity ρ ∧ IsDensity σ ∧ ρ ≠ σ ∧
                    x = traceDistance (conditionedState R ρ)
                      (conditionedState R σ) / traceDistance ρ σ} := by
            exact ⟨P iMin, σe e, ⟨hPpsd iMin, hPtrace iMin⟩,
              hSigmaDensity e he0.le he1.le, hne, rfl⟩
          exact (hRatioLower e he0 he1).trans (hb hmem)
        let f : ℕ → ℝ := fun n => rhi / δ (1 / ((n : ℝ) + 2))
        have hlimBase : Filter.Tendsto
            (fun n : ℕ => (2 * rhi + rhi * (n : ℝ)) /
              (2 * rlo + (rhi - rlo) + rlo * (n : ℝ)))
            atTop (𝓝 (rhi / rlo)) := by
          exact tendsto_add_mul_div_add_mul_atTop_nhds
            (𝕜 := ℝ) (2 * rhi) (2 * rlo + (rhi - rlo)) rhi
            (d := rlo) (ne_of_gt hrMinPos)
        have hlim : Filter.Tendsto f atTop (𝓝 (rhi / rlo)) := by
          apply hlimBase.congr'
          exact Eventually.of_forall (fun n => by
            dsimp [f, δ]
            have hn : 0 < (n : ℝ) + 2 := by positivity
            have hden : 0 < (1 - 1 / ((n : ℝ) + 2)) * rlo +
                (1 / ((n : ℝ) + 2)) * rhi := by
              exact hDeltaPos _ (by positivity) (by
                apply (div_lt_iff₀ hn).2
                have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
                nlinarith)
            field_simp [ne_of_gt hden, ne_of_gt hn]
            ring)
        have hbound : ∀ n : ℕ, f n ≤ b := by
          intro n
          apply hfamily (1 / ((n : ℝ) + 2))
          · positivity
          · apply (div_lt_iff₀ (show 0 < (n : ℝ) + 2 by positivity)).2
            have hnle : (1 : ℝ) ≤ (n : ℝ) + 1 := by
              exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
            norm_num
            linarith
        have hkb : rhi / rlo ≤ b := le_of_tendsto' hlim hbound
        simpa [conditionNumber, rlo, rhi] using hkb

end D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant
