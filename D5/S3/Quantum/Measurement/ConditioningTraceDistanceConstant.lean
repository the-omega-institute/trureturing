/- GID: D5/S3/Quantum/Measurement/ConditioningTraceDistanceConstant
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/ConditioningTraceDistanceConstant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The sharp trace-distance constant of a positive conditioning filter. -/

import D5.S3.Quantum.Measurement.BranchConditionedTraceDistance
import D5.S3.Quantum.Measurement.ExactConditionalPreparationCost
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
import Mathlib.Analysis.Matrix.PosDef

noncomputable section
namespace D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant

open BigOperators Matrix Filter Topology
open scoped ComplexOrder MatrixOrder InnerProductSpace
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Measurement.ExactConditionalPreparationCost
open D5.S3.Quantum.PureState.PureStateHandshake

local notation "kact" => fun K X => PhyslibLeaf.MatrixMap.of_kraus K K X

set_option autoImplicit false
set_option relaxedAutoImplicit false

def conditionedState {d : ℕ} (hd : 0 < d) (R : Matrix (Fin d) (Fin d) ℂ) (hR : R.PosDef)
    (ρ : DensityState (Fin d)) : DensityState (Fin d) := by
  let hH : R.IsHermitian := hR.isHermitian
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  let rlo : ℝ := leastEigenvalue R hR
  have hrlo : 0 < rlo := by
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf'
      (s := (Finset.univ : Finset (Fin d))) Finset.univ_nonempty hH.eigenvalues
    dsimp only [rlo, leastEigenvalue]
    rw [hi]
    exact hR.eigenvalues_pos i
  have hlower : ∀ x ∈ spectrum ℝ R, rlo ≤ x := by
    rw [hH.spectrum_real_eq_range_eigenvalues]
    rintro _ ⟨i, rfl⟩
    exact Finset.inf'_le (s := (Finset.univ : Finset (Fin d)))
      hH.eigenvalues (Finset.mem_univ i)
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
    let h0 : 0 < d := by omega
    letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp h0
    (∀ ρ σ : DensityState (Fin d),
      (greatestEigenvalue R hR / leastEigenvalue R hR)⁻¹ * traceDistance ρ σ ≤
        traceDistance (conditionedState h0 R hR ρ)
          (conditionedState h0 R hR σ) ∧
      traceDistance (conditionedState h0 R hR ρ)
          (conditionedState h0 R hR σ) ≤
        (greatestEigenvalue R hR / leastEigenvalue R hR) * traceDistance ρ σ) ∧
      (∀ ρ : DensityState (Fin d),
        leastEigenvalue R hR = greatestEigenvalue R hR →
          conditionedState h0 R hR ρ = ρ) ∧
      IsLUB {x : ℝ | ∃ ρ σ : DensityState (Fin d),
        ρ ≠ σ ∧
          x = traceDistance (conditionedState h0 R hR ρ)
              (conditionedState h0 R hR σ) /
            traceDistance ρ σ} (greatestEigenvalue R hR / leastEigenvalue R hR) := by
  dsimp only
  classical
  have hd0 : 0 < d := by omega
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd0
  let hH : R.IsHermitian := hR.isHermitian
  let IsDensity (X : Matrix (Fin d) (Fin d) ℂ) : Prop :=
    X.PosSemidef ∧ X.trace = 1
  let traceDistance (X Y : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
    traceNorm (X - Y) / 2
  let conditionedState (R' X : Matrix (Fin d) (Fin d) ℂ) :
      Matrix (Fin d) (Fin d) ℂ :=
    (1 / (R' * X).trace.re) • (CFC.sqrt R' * X * CFC.sqrt R')
  have spectralSandwich : ∀ (R' : Matrix (Fin d) (Fin d) ℂ) (hR' : R'.PosDef),
      (leastEigenvalue R' hR' : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) ≤ R' ∧
        R' ≤ (greatestEigenvalue R' hR' : ℂ) •
          (1 : Matrix (Fin d) (Fin d) ℂ) := by
    intro R' hR'
    let hH' : R'.IsHermitian := hR'.isHermitian
    have hupper : ∀ x ∈ spectrum ℝ R', x ≤ greatestEigenvalue R' hR' := by
      rw [hH'.spectrum_real_eq_range_eigenvalues]
      rintro _ ⟨i, rfl⟩
      exact Finset.le_sup' (s := (Finset.univ : Finset (Fin d)))
        hH'.eigenvalues (Finset.mem_univ i)
    have hlower : ∀ x ∈ spectrum ℝ R', leastEigenvalue R' hR' ≤ x := by
      rw [hH'.spectrum_real_eq_range_eigenvalues]
      rintro _ ⟨i, rfl⟩
      exact Finset.inf'_le (s := (Finset.univ : Finset (Fin d)))
        hH'.eigenvalues (Finset.mem_univ i)
    constructor
    · simpa [leastEigenvalue, Algebra.algebraMap_eq_smul_one] using
        algebraMap_le_of_le_spectrum hlower hH'
    · simpa [greatestEigenvalue, Algebra.algebraMap_eq_smul_one] using
        le_algebraMap_of_spectrum_le hupper hH'

  have hUpper : ∀ (R' : Matrix (Fin d) (Fin d) ℂ) (hR' : R'.PosDef),
      ∀ ρ σ : Matrix (Fin d) (Fin d) ℂ, IsDensity ρ → IsDensity σ →
        traceDistance (conditionedState R' ρ) (conditionedState R' σ) ≤
          (greatestEigenvalue R' hR' / leastEigenvalue R' hR') *
            traceDistance ρ σ := by
    intro R' hR' ρ σ hρ hσ
    let hH' : R'.IsHermitian := hR'.isHermitian
    let rlo : ℝ := leastEigenvalue R' hR'
    let rhi : ℝ := greatestEigenvalue R' hR'
    have hrlo : 0 < rlo := by
      obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf'
        (s := (Finset.univ : Finset (Fin d))) Finset.univ_nonempty hH'.eigenvalues
      dsimp only [rlo, leastEigenvalue]
      rw [hi]
      exact hR'.eigenvalues_pos i
    have hrhi : 0 < rhi := by
      obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup'
        (s := (Finset.univ : Finset (Fin d))) Finset.univ_nonempty hH'.eigenvalues
      dsimp only [rhi, greatestEigenvalue]
      rw [hi]
      exact hR'.eigenvalues_pos i
    let G' : Matrix (Fin d) (Fin d) ℂ := CFC.sqrt R'
    let K : Fin 1 → Matrix (Fin d) (Fin d) ℂ := fun _ =>
      (((1 / Real.sqrt rhi : ℝ) : ℂ) • G')
    let B : Matrix (Fin d) (Fin d) ℂ := ∑ i, (K i)ᴴ * K i
    have hopt :=
      (exact_conditional_preparation_cost R' hR').2.2.2.2.1
    dsimp only at hopt
    have hcontract : ExactPreparationContract R' K := by
      simpa only [K, G', rhi] using hopt.1
    have htni : TraceNonincreasing K := by
      simpa only [K, G', rhi] using hopt.2.1
    have hfloor (X : Matrix (Fin d) (Fin d) ℂ) (hX : X.PosSemidef)
        (hXtrace : X.trace = 1) :
        rlo / rhi ≤ (kact K X).trace.re := by
      simpa only [K, G', rlo, rhi] using hopt.2.2.2 X hX hXtrace
    have hGstar : G'ᴴ = G' := by
      simpa [G', star_eq_conjTranspose] using (CFC.sqrt_nonneg R').isSelfAdjoint.star_eq
    have hGsq : G' * G' = R' := by
      simpa [G'] using CFC.sqrt_mul_sqrt_self R' hR'.posSemidef.nonneg
    have hB : B ≤ (1 : Matrix (Fin d) (Fin d) ℂ) := by
      unfold TraceNonincreasing at htni
      exact sub_nonneg.mp htni.nonneg
    have hGtrace (X : Matrix (Fin d) (Fin d) ℂ) :
        (G' * X * G').trace = (R' * X).trace := by
      calc
        (G' * X * G').trace = (X * G' * G').trace :=
          (Matrix.trace_mul_cycle X G' G').symm
        _ = (X * (G' * G')).trace := by rw [Matrix.mul_assoc]
        _ = (X * R').trace := by rw [hGsq]
        _ = (R' * X).trace := Matrix.trace_mul_comm X R'
    have hbsq : (1 / Real.sqrt rhi) * (1 / Real.sqrt rhi) = 1 / rhi := by
      field_simp [Real.sqrt_ne_zero'.mpr hrhi]
      rw [Real.sq_sqrt hrhi.le]
    have hPhi (X : Matrix (Fin d) (Fin d) ℂ) :
        (∑ i : Fin 1, K i * X * (K i)ᴴ) =
          ((rhi⁻¹ : ℝ) : ℂ) • (G' * X * G') := by
      simp only [K, Matrix.conjTranspose_smul, hGstar, Complex.star_def,
        Complex.conj_ofReal, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        Fin.sum_univ_one]
      rw [← Complex.ofReal_mul, hbsq]
      simp only [one_div]
    have htraceAction (X : Matrix (Fin d) (Fin d) ℂ) :
        (∑ i : Fin 1, K i * X * (K i)ᴴ).trace = (X * B).trace := by
      dsimp only [B]
      rw [Matrix.trace_sum, Matrix.mul_sum, Matrix.trace_sum]
      apply Finset.sum_congr rfl
      intro i _
      calc
        (K i * X * (K i)ᴴ).trace = (K i * (X * (K i)ᴴ)).trace := by
          rw [Matrix.mul_assoc]
        _ = (X * ((K i)ᴴ * K i)).trace :=
          (Matrix.trace_mul_cycle' X (K i)ᴴ (K i)).symm
    have hp : 0 < (ρ * B).trace.re := by
      rw [← htraceAction]
      simpa only [PhyslibLeaf.MatrixMap.of_kraus, LinearMap.sum_apply,
        LinearMap.coe_mk, AddHom.coe_mk] using (hcontract ρ hρ.1 hρ.2).1
    have hq : 0 < (σ * B).trace.re := by
      rw [← htraceAction]
      simpa only [PhyslibLeaf.MatrixMap.of_kraus, LinearMap.sum_apply,
        LinearMap.coe_mk, AddHom.coe_mk] using (hcontract σ hσ.1 hσ.2).1
    let pR : ℝ := (R' * ρ).trace.re
    let qR : ℝ := (R' * σ).trace.re
    have hpB : (ρ * B).trace.re = rhi⁻¹ * pR := by
      rw [← htraceAction, hPhi, Matrix.trace_smul, hGtrace]
      simp [pR, Complex.real_smul]
    have hqB : (σ * B).trace.re = rhi⁻¹ * qR := by
      rw [← htraceAction, hPhi, Matrix.trace_smul, hGtrace]
      simp [qR, Complex.real_smul]
    have hpRne : pR ≠ 0 := by
      intro hpR0
      rw [hpB, hpR0, mul_zero] at hp
      exact lt_irrefl 0 hp
    have hqRne : qR ≠ 0 := by
      intro hqR0
      rw [hqB, hqR0, mul_zero] at hq
      exact lt_irrefl 0 hq
    have hnormρ :
        (1 / (ρ * B).trace.re) • (∑ i : Fin 1, K i * ρ * (K i)ᴴ) =
          conditionedState R' ρ := by
      rw [hPhi, hpB]
      simp only [conditionedState, G', pR]
      have hscalar : (1 / (rhi⁻¹ * pR)) * rhi⁻¹ = 1 / pR := by
        field_simp [hpRne, hrhi.ne']
      ext a b
      simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
      rw [← mul_assoc, ← Complex.ofReal_mul, hscalar]
    have hnormσ :
        (1 / (σ * B).trace.re) • (∑ i : Fin 1, K i * σ * (K i)ᴴ) =
          conditionedState R' σ := by
      rw [hPhi, hqB]
      simp only [conditionedState, G', qR]
      have hscalar : (1 / (rhi⁻¹ * qR)) * rhi⁻¹ = 1 / qR := by
        field_simp [hqRne, hrhi.ne']
      ext a b
      simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
      rw [← mul_assoc, ← Complex.ofReal_mul, hscalar]
    have hbranch :=
      D5.S3.Quantum.Measurement.BranchConditionedTraceDistance.branch_conditioned_trace_distance
        ρ σ K hρ.1 hρ.2 hσ.1 hσ.2 hB
    have hweighted := hbranch.2.1 ⟨hp, hq⟩
    have hweighted' :
        max ((ρ * B).trace.re) ((σ * B).trace.re) *
            traceDistance (conditionedState R' ρ) (conditionedState R' σ) ≤
          traceDistance ρ σ := by
      change max ((ρ * B).trace.re) ((σ * B).trace.re) *
          (traceNorm ((1 / (ρ * B).trace.re) • (∑ i : Fin 1, K i * ρ * (K i)ᴴ) -
            (1 / (σ * B).trace.re) • (∑ i : Fin 1, K i * σ * (K i)ᴴ)) / 2) ≤
        traceNorm (ρ - σ) / 2 at hweighted
      rw [hnormρ, hnormσ] at hweighted
      simpa [traceDistance] using hweighted
    have hfloorρ : rlo / rhi ≤ (ρ * B).trace.re := by
      rw [← htraceAction]
      simpa only [PhyslibLeaf.MatrixMap.of_kraus, LinearMap.sum_apply,
        LinearMap.coe_mk, AddHom.coe_mk] using hfloor ρ hρ.1 hρ.2
    have hfloorσ : rlo / rhi ≤ (σ * B).trace.re := by
      rw [← htraceAction]
      simpa only [PhyslibLeaf.MatrixMap.of_kraus, LinearMap.sum_apply,
        LinearMap.coe_mk, AddHom.coe_mk] using hfloor σ hσ.1 hσ.2
    have hfloorMax : rlo / rhi ≤ max ((ρ * B).trace.re) ((σ * B).trace.re) :=
      by
        rcases le_total ((ρ * B).trace.re) ((σ * B).trace.re) with hpq | hqp
        · rw [max_eq_right hpq]
          exact hfloorσ
        · rw [max_eq_left hqp]
          exact hfloorρ
    have hDcond : 0 ≤ traceDistance (conditionedState R' ρ) (conditionedState R' σ) :=
      div_nonneg (traceNorm_nonneg _) (by norm_num)
    have hscaled : (rlo / rhi) *
          traceDistance (conditionedState R' ρ) (conditionedState R' σ) ≤
        traceDistance ρ σ := by
      exact (mul_le_mul_of_nonneg_right hfloorMax hDcond).trans hweighted'
    have hresult : traceDistance (conditionedState R' ρ) (conditionedState R' σ) ≤
        traceDistance ρ σ / (rlo / rhi) := by
      exact (le_div_iff₀ (div_pos hrlo hrhi)).2 (by simpa [mul_comm] using hscaled)
    calc
      traceDistance (conditionedState R' ρ) (conditionedState R' σ) ≤
          traceDistance ρ σ / (rlo / rhi) := hresult
      _ = (greatestEigenvalue R' hR' / leastEigenvalue R' hR') *
          traceDistance ρ σ := by
        dsimp only [rlo, rhi]
        field_simp [hrlo.ne', hrhi.ne']
  have hTwoSided : ∀ ρ σ : Matrix (Fin d) (Fin d) ℂ, IsDensity ρ → IsDensity σ →
      (greatestEigenvalue R hR / leastEigenvalue R hR)⁻¹ * traceDistance ρ σ ≤
          traceDistance (conditionedState R ρ) (conditionedState R σ) ∧
        traceDistance (conditionedState R ρ) (conditionedState R σ) ≤
          (greatestEigenvalue R hR / leastEigenvalue R hR) * traceDistance ρ σ := by
    intro ρ σ hρ hσ
    have hupper := hUpper R hR ρ σ hρ hσ
    let rlo : ℝ := leastEigenvalue R hR
    let rhi : ℝ := greatestEigenvalue R hR
    have hrlo : 0 < rlo := by
      obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf'
        (s := (Finset.univ : Finset (Fin d))) Finset.univ_nonempty hH.eigenvalues
      dsimp only [rlo, leastEigenvalue]
      rw [hi]
      exact hR.eigenvalues_pos i
    have hrhi : 0 < rhi := by
      obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup'
        (s := (Finset.univ : Finset (Fin d))) Finset.univ_nonempty hH.eigenvalues
      dsimp only [rhi, greatestEigenvalue]
      rw [hi]
      exact hR.eigenvalues_pos i
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
    let hHinv : R⁻¹.IsHermitian := hRinv.isHermitian
    let invLo : ℝ := leastEigenvalue R⁻¹ hRinv
    let invHi : ℝ := greatestEigenvalue R⁻¹ hRinv
    let vInv (i : Fin d) : Fin d → ℂ := ⇑(hHinv.eigenvectorBasis i)
    let PInv (i : Fin d) : Matrix (Fin d) (Fin d) ℂ := rankOneDensity (vInv i)
    have hvInvNorm (i : Fin d) : star (vInv i) ⬝ᵥ vInv i = 1 := by
      have hn := hHinv.eigenvectorBasis.orthonormal.norm_eq_one i
      have hi := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (hHinv.eigenvectorBasis i)
      rw [EuclideanSpace.inner_eq_star_dotProduct] at hi
      simpa [vInv, dotProduct_comm, hn] using hi
    have hPInvPsd (i : Fin d) : (PInv i).PosSemidef := by
      exact Matrix.posSemidef_vecMulVec_self_star (vInv i)
    have hPInvTrace (i : Fin d) : (PInv i).trace = 1 := by
      dsimp only [PInv]
      rw [rankOneDensity, Matrix.trace_vecMulVec]
      simpa [dotProduct_comm] using hvInvNorm i
    have hRinvPTrace (i : Fin d) :
        (R⁻¹ * PInv i).trace = hHinv.eigenvalues i := by
      dsimp only [PInv]
      rw [rankOneDensity, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec,
        dotProduct_comm, hHinv.mulVec_eigenvectorBasis, dotProduct_smul, hvInvNorm]
      norm_num
    obtain ⟨iInvLo, _, hiInvLo⟩ := Finset.exists_mem_eq_inf'
      (s := (Finset.univ : Finset (Fin d))) Finset.univ_nonempty hHinv.eigenvalues
    obtain ⟨iInvHi, _, hiInvHi⟩ := Finset.exists_mem_eq_sup'
      (s := (Finset.univ : Finset (Fin d))) Finset.univ_nonempty hHinv.eigenvalues
    have hInvLoEq : invLo = hHinv.eigenvalues iInvLo := by
      simpa only [invLo, leastEigenvalue] using hiInvLo
    have hInvHiEq : invHi = hHinv.eigenvalues iInvHi := by
      simpa only [invHi, greatestEigenvalue] using hiInvHi
    have hInvLoLower : rhi⁻¹ ≤ invLo := by
      have ht := RHLinalg.trace_mul_nonneg_of_posSemidef (hPInvPsd iInvLo)
        (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hinvLower))
      rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_sub,
        Matrix.trace_smul, Matrix.trace_mul_comm (PInv iInvLo) R⁻¹,
        hRinvPTrace, hPInvTrace, ← hInvLoEq] at ht
      norm_num at ht
      exact ht
    have hInvHiUpper : invHi ≤ rlo⁻¹ := by
      have ht := RHLinalg.trace_mul_nonneg_of_posSemidef (hPInvPsd iInvHi)
        (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hinvUpper))
      rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_sub,
        Matrix.trace_smul, Matrix.trace_mul_comm (PInv iInvHi) R⁻¹,
        hRinvPTrace, hPInvTrace, ← hInvHiEq] at ht
      norm_num at ht
      exact ht
    have hInvLoPos : 0 < invLo :=
      lt_of_lt_of_le (inv_pos.mpr hrhi) hInvLoLower
    have hInvRatio : invHi / invLo ≤ rhi / rlo := by
      apply (div_le_iff₀ hInvLoPos).2
      calc
        invHi ≤ rlo⁻¹ := hInvHiUpper
        _ = (rhi / rlo) * rhi⁻¹ := by field_simp [hrlo.ne', hrhi.ne']
        _ ≤ (rhi / rlo) * invLo :=
          mul_le_mul_of_nonneg_left hInvLoLower (div_nonneg hrhi.le hrlo.le)
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
      have hh := hUpper R⁻¹ hRinv (conditionedState R ρ) (conditionedState R σ)
        (hCondDensity ρ hρ) (hCondDensity σ hσ)
      rw [hτinv ρ hρ, hτinv σ hσ] at hh
      have hnonneg : 0 ≤ traceDistance (conditionedState R ρ) (conditionedState R σ) :=
        div_nonneg (traceNorm_nonneg _) (by norm_num)
      have hh' := hh.trans (mul_le_mul_of_nonneg_right hInvRatio hnonneg)
      simpa only [invLo, invHi] using hh'
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
      simpa only [rlo, rhi] using hh'
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
      leastEigenvalue R hR = greatestEigenvalue R hR →
        D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant.conditionedState
          (by omega) R hR ρ = ρ := by
    intro ρ heq
    let r : ℝ := leastEigenvalue R hR
    have hr : 0 < r := by
      obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf'
        (s := (Finset.univ : Finset (Fin d))) Finset.univ_nonempty hH.eigenvalues
      dsimp only [r, leastEigenvalue]
      rw [hi]
      exact hR.eigenvalues_pos i
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
    obtain ⟨iMin, _, hiMin⟩ := Finset.exists_mem_eq_inf'
      (s := (Finset.univ : Finset (Fin d))) Finset.univ_nonempty hH.eigenvalues
    obtain ⟨iMax, _, hiMax⟩ := Finset.exists_mem_eq_sup'
      (s := (Finset.univ : Finset (Fin d))) Finset.univ_nonempty hH.eigenvalues
    letI : Nontrivial (Fin d) := Fintype.one_lt_card_iff_nontrivial.mp
      (by simpa using (show 1 < d by omega))
    obtain ⟨iOne, hiOneMax⟩ := exists_ne iMax
    have hiMaxOne : iMax ≠ iOne := Ne.symm hiOneMax
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
    let P (i : Fin d) : Matrix (Fin d) (Fin d) ℂ := rankOneDensity (v i)
    have hPpsd (i : Fin d) : (P i).PosSemidef := by
      exact Matrix.posSemidef_vecMulVec_self_star (v i)
    have hPtrace (i : Fin d) : (P i).trace = 1 := by
      dsimp only [P]
      rw [rankOneDensity, Matrix.trace_vecMulVec]
      simpa [dotProduct_comm] using hvnorm i
    have hPleft (i : Fin d) :
        R * P i = (hH.eigenvalues i : ℂ) • P i := by
      dsimp only [P]
      rw [rankOneDensity]
      rw [Matrix.mul_vecMulVec, heig]
      simp [Matrix.smul_vecMulVec]
    have hPstar (i : Fin d) : (P i)ᴴ = P i := by
      dsimp only [P]
      rw [rankOneDensity, Matrix.conjTranspose_vecMulVec]
      simp
    have hPright (i : Fin d) :
        P i * R = (hH.eigenvalues i : ℂ) • P i := by
      have h := congrArg Matrix.conjTranspose (hPleft i)
      simpa [Matrix.conjTranspose_mul, hH.eq, Matrix.conjTranspose_smul,
        hPstar i] using h
    have hPorth (i j : Fin d) (hij : i ≠ j) :
        P i * P j = 0 := by
      dsimp only [P]
      rw [rankOneDensity, rankOneDensity]
      rw [Matrix.vecMulVec_mul_vecMulVec]
      have ho := hH.eigenvectorBasis.orthonormal.inner_eq_zero hij
      have hodot : star (v i) ⬝ᵥ v j = 0 := by
        rw [dotProduct_comm]
        exact (EuclideanSpace.inner_eq_star_dotProduct _ _).symm.trans
          (by simpa using ho)
      simp [hodot]
    have hPidemp (i : Fin d) : P i * P i = P i := by
      exact (pure_state_handshake (v i) (hvnorm i)
        (0 : Matrix (Fin d) (Fin d) ℂ)).1
    have hsumP : (∑ j : Fin d, P j) = (1 : Matrix (Fin d) (Fin d) ℂ) := by
      have hUU := Unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2
      ext a b
      have hab := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M a b) hUU
      simp only [Matrix.sum_apply, P, rankOneDensity, Matrix.vecMulVec_apply]
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
    have hEigMin : hH.eigenvalues iMin = leastEigenvalue R hR := by
      simpa only [leastEigenvalue] using hiMin.symm
    have hEigMax : hH.eigenvalues iMax = greatestEigenvalue R hR := by
      simpa only [greatestEigenvalue] using hiMax.symm
    have hrMinPos : 0 < leastEigenvalue R hR := by
      rw [← hEigMin]
      exact hEigPos iMin
    have hrMaxPos : 0 < greatestEigenvalue R hR := by
      rw [← hEigMax]
      exact hEigPos iMax
    by_cases heq : leastEigenvalue R hR = greatestEigenvalue R hR
    · have hkEq : greatestEigenvalue R hR / leastEigenvalue R hR = 1 := by
        rw [← heq]
        exact div_self hrMinPos.ne'
      have hmember : greatestEigenvalue R hR / leastEigenvalue R hR ∈
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
    · have hiMinMax : iMin ≠ iMax := by
        intro h
        apply heq
        rw [← hEigMin, ← hEigMax, h]
      let rlo : ℝ := leastEigenvalue R hR
      let rhi : ℝ := greatestEigenvalue R hR
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
          simpa only [rlo, rhi] using hu
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
        simpa only [rlo, rhi] using hkb

#print axioms conditioning_trace_distance_constant

end D5.S3.Quantum.Measurement.ConditioningTraceDistanceConstant
