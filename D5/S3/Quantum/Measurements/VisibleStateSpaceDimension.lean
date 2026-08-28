/- GID: D5/S3/Quantum/Measurements/VisibleStateSpaceDimension
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurements/VisibleStateSpaceDimension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Visible quantum states form a compact convex range with the expected affine dimension. -/

import D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition
import D5.S3.Quantum.Fibers.FutureStatisticsEquivalence
import D5.S3.Quantum.Fibers.PhysicalFiber
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dual.Lemmas
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped CStarAlgebra ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology
namespace D5.S3.Quantum.Measurements.VisibleStateSpaceDimension
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition
open D5.S3.Quantum.Fibers.FutureStatisticsEquivalence
open D5.S3.Quantum.Fibers.OperatorSystemTowerStability
open D5.S3.Quantum.Fibers.PhysicalFiber
open D5.S3.Quantum.Measurement.BasisMeasurementProjection
private def selfAdjointRealInclusion (d : Nat) : selfAdjoint (MatrixAlgebra (Fin d)) →ₗ[ℝ]
    Matrix (Fin d) (Fin d) ℂ where
  toFun effect := CStarMatrix.ofMatrix.symm effect.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
local instance selfAdjointContinuousSMul (d : Nat) : ContinuousSMul ℝ
    (selfAdjoint (MatrixAlgebra (Fin d))) := ContinuousSMul.induced (selfAdjointRealInclusion d)
local instance selfAdjointFiniteDimensional (d : Nat) : FiniteDimensional ℝ
    (selfAdjoint (MatrixAlgebra (Fin d))) := FiniteDimensional.of_injective
      (selfAdjointRealInclusion d) Subtype.val_injective
local instance systemCarrierNormedSpace (d : Nat) (system : MatrixOperatorSystem (Fin d)) :
    NormedSpace ℝ system.carrier where
  norm_smul_le scalar effect := NormedSpace.norm_smul_le scalar
    (effect : selfAdjoint (MatrixAlgebra (Fin d)))
local instance systemCarrierContinuousSMul (d : Nat) (system : MatrixOperatorSystem (Fin d)) :
    ContinuousSMul ℝ system.carrier := ContinuousSMul.induced system.carrier.subtype
local instance systemCarrierFiniteDimensional (d : Nat) (system : MatrixOperatorSystem (Fin d)) :
    FiniteDimensional ℝ system.carrier := FiniteDimensional.of_injective
      system.carrier.subtype Subtype.val_injective
private theorem cstar_trace_add {d : Type*} [Fintype d] (first second : MatrixAlgebra d) :
    Matrix.trace (first + second) = Matrix.trace first + Matrix.trace second := by
  simp [Matrix.trace, Finset.sum_add_distrib]
private theorem cstar_trace_real_smul {d : Type*} [Fintype d] (scalar : ℝ)
    (matrix : MatrixAlgebra d) :
    Matrix.trace (scalar • matrix) = scalar • Matrix.trace matrix := by
  simp [Matrix.trace, Finset.mul_sum]
private noncomputable def ambientStateReadout (d : Nat) (system : MatrixOperatorSystem (Fin d)) :
    Matrix (Fin d) (Fin d) ℂ →ₗ[ℝ] (system.carrier →L[ℝ] ℝ) where
  toFun matrix := LinearMap.toContinuousLinearMap {
      toFun := fun effect => (Matrix.trace (matrix * CStarMatrix.ofMatrix.symm effect.1.1)).re
      map_add' := by
        intro first second
        change (Matrix.trace (matrix * (CStarMatrix.ofMatrix.symm first.1.1 +
          CStarMatrix.ofMatrix.symm second.1.1))).re = _
        rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re]
      map_smul' := by
        intro scalar effect
        change (Matrix.trace (matrix * ((scalar : ℂ) •
          CStarMatrix.ofMatrix.symm effect.1.1))).re = _
        rw [Matrix.mul_smul, Matrix.trace_smul]
        simp [smul_eq_mul, Complex.mul_re] }
  map_add' first second := by
    ext effect
    change (Matrix.trace ((first + second) * CStarMatrix.ofMatrix.symm effect.1.1)).re = _
    rw [Matrix.add_mul, Matrix.trace_add, Complex.add_re]
    rfl
  map_smul' scalar matrix := by
    ext effect
    change (Matrix.trace (((scalar : ℂ) • matrix) * CStarMatrix.ofMatrix.symm effect.1.1)).re = _
    rw [Matrix.smul_mul, Matrix.trace_smul]
    simp [smul_eq_mul, Complex.mul_re]

noncomputable def visibleStateReadout (d : Nat) (system : MatrixOperatorSystem (Fin d))
    (rho : DensityState (Fin d)) : system.carrier →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap {
      toFun := fun effect => (operatorSystemReadout system rho effect).re
      map_add' := by
        intro first second
        change (Matrix.trace (rho.1 * (first.1.1 + second.1.1))).re =
          (Matrix.trace (rho.1 * first.1.1)).re + (Matrix.trace (rho.1 * second.1.1)).re
        rw [mul_add, cstar_trace_add, Complex.add_re]
      map_smul' := by
        intro scalar effect
        change (Matrix.trace (rho.1 * (scalar • effect.1.1))).re =
          scalar • (Matrix.trace (rho.1 * effect.1.1)).re
        rw [mul_smul_comm, cstar_trace_real_smul]
        simp [Algebra.smul_def, Complex.mul_re] }

noncomputable def centeredStateReadout (d : Nat) (system : MatrixOperatorSystem (Fin d)) :
    traceZeroHermitian d →ₗ[ℝ] (system.carrier →L[ℝ] ℝ) :=
  (ambientStateReadout d system).comp ((HermitianSpace d).subtype.comp
    (traceZeroHermitian d).subtype)

private theorem visible_state_readout_eq_ambient (d : Nat) (system : MatrixOperatorSystem (Fin d))
    (rho : DensityState (Fin d)) :
    visibleStateReadout d system rho = ambientStateReadout d system
      (CStarMatrix.ofMatrix.symm rho.1) := by
  ext effect
  rfl

private theorem traceless_density_perturbations (d : Nat) [NeZero d]
    (difference : traceZeroHermitian d) :
    ∃ eps : ℝ, 0 < eps ∧
      ∃ plus minus : DensityState (Fin d), CStarMatrix.ofMatrix.symm plus.1 -
        CStarMatrix.ofMatrix.symm minus.1 = (2 * eps) • difference.1.1 := by
  let matrix : CStarMatrix (Fin d) (Fin d) ℂ := CStarMatrix.ofMatrix difference.1.1
  let center : ℝ := (d : ℝ)⁻¹
  let eps : ℝ := center / (2 * (‖matrix‖ + 1))
  have hcenter : 0 < center := inv_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d))
  have hdenominator : 0 < 2 * (‖matrix‖ + 1) := mul_pos (by norm_num) (by positivity)
  have heps : 0 < eps := div_pos hcenter hdenominator
  have hproduct : eps * (‖matrix‖ + 1) = center / 2 := by
    dsimp only [eps]
    field_simp
  have hcoefficient : 0 ≤ center - eps * ‖matrix‖ := by
    have hstrict : eps * ‖matrix‖ < eps * (‖matrix‖ + 1) := by nlinarith
    rw [hproduct] at hstrict
    linarith
  have hself : IsSelfAdjoint matrix := congrArg CStarMatrix.ofMatrix difference.1.2
  have hlower := IsSelfAdjoint.neg_algebraMap_norm_le_self (a := matrix) (ha := hself)
  have hlowerScaled := smul_le_smul_of_nonneg_left hlower heps.le
  have hlowerShifted := add_le_add_left hlowerScaled
    ((algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) center)
  have hpositiveLeft : 0 ≤ eps •
      (-(algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) ‖matrix‖) +
      (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) center := by
    have heq : eps • (-(algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) ‖matrix‖) +
        (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) center =
        (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) (center - eps * ‖matrix‖) := by
      simp only [map_sub, map_mul, Algebra.smul_def]
      noncomm_ring
    rw [heq]
    exact algebraMap_nonneg (β := CStarMatrix (Fin d) (Fin d) ℂ) hcoefficient
  have hplus : 0 ≤ (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) center +
      (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) eps * matrix := by
    have hresult := hpositiveLeft.trans hlowerShifted
    rw [add_comm (eps • matrix) ((algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) center)]
      at hresult
    simpa only [Algebra.smul_def] using hresult
  have hupper := IsSelfAdjoint.le_algebraMap_norm_self (a := matrix) (ha := hself)
  have hupperScaled := smul_le_smul_of_nonneg_left hupper heps.le
  have hpositiveBase : 0 ≤ (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) center -
      eps • (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) ‖matrix‖ := by
    have heq : (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) center -
        eps • (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) ‖matrix‖ =
        (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) (center - eps * ‖matrix‖) := by
      simp only [map_sub, map_mul, Algebra.smul_def]
    rw [heq]
    exact algebraMap_nonneg (β := CStarMatrix (Fin d) (Fin d) ℂ) hcoefficient
  have hminus : 0 ≤ (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) center -
      (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) eps * matrix := by
    have hbound := sub_le_sub_left hupperScaled
      ((algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) center)
    simp only [Algebra.smul_def] at hpositiveBase hbound ⊢
    exact hpositiveBase.trans hbound
  have hmatrixPlus : CStarMatrix.ofMatrix.symm
      ((algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) center +
        (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) eps * matrix) =
      (center : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) + (eps : ℂ) • difference.1.1 := by
    ext i j
    simp [matrix, Algebra.smul_def, CStarMatrix.algebraMap_apply,
      Matrix.algebraMap_matrix_apply, CStarMatrix.mul_apply, Matrix.mul_apply]
  have hmatrixMinus : CStarMatrix.ofMatrix.symm
      ((algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) center -
        (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) eps * matrix) =
      (center : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) - (eps : ℂ) • difference.1.1 := by
    ext i j
    simp [matrix, Algebra.smul_def, CStarMatrix.algebraMap_apply,
      Matrix.algebraMap_matrix_apply, CStarMatrix.mul_apply, Matrix.mul_apply]
  have htracePlus : Matrix.trace (CStarMatrix.ofMatrix.symm
      ((algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) center +
        (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) eps * matrix)) = 1 := by
    rw [hmatrixPlus]
    have hcenterComplex : (center : ℂ) = (d : ℂ)⁻¹ := by
      dsimp only [center]; exact Complex.ofReal_inv (d : ℝ)
    have hdifferenceTrace : Matrix.trace difference.1.1 = 0 := difference.2
    simp only [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one,
      hdifferenceTrace, Fintype.card_fin, smul_eq_mul]
    rw [hcenterComplex]
    simp [show (d : ℂ) ≠ 0 by exact_mod_cast NeZero.ne d]
  have htraceMinus : Matrix.trace (CStarMatrix.ofMatrix.symm
      ((algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) center -
        (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) eps * matrix)) = 1 := by
    rw [hmatrixMinus]
    have hcenterComplex : (center : ℂ) = (d : ℂ)⁻¹ := by
      dsimp only [center]; exact Complex.ofReal_inv (d : ℝ)
    have hdifferenceTrace : Matrix.trace difference.1.1 = 0 := difference.2
    simp only [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one,
      hdifferenceTrace, Fintype.card_fin, smul_eq_mul]
    rw [hcenterComplex]
    simp [show (d : ℂ) ≠ 0 by exact_mod_cast NeZero.ne d]
  let plus : DensityState (Fin d) :=
    ⟨(algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) center +
      (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) eps * matrix, hplus, htracePlus⟩
  let minus : DensityState (Fin d) :=
    ⟨(algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) center -
      (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) eps * matrix, hminus, htraceMinus⟩
  refine ⟨eps, heps, plus, minus, ?_⟩
  dsimp only [plus, minus]
  rw [hmatrixPlus, hmatrixMinus]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  change ((center : ℂ) * (1 : Matrix (Fin d) (Fin d) ℂ) i j + (eps : ℂ) *
    difference.1.1 i j) - ((center : ℂ) * (1 : Matrix (Fin d) (Fin d) ℂ) i j -
    (eps : ℂ) * difference.1.1 i j) = ((2 * eps : ℝ) : ℂ) * difference.1.1 i j
  norm_num [map_mul]
  ring

private theorem affine_direction_eq_centered_range (d : Nat) [NeZero d]
    (system : MatrixOperatorSystem (Fin d)) :
    (affineSpan ℝ (Set.range (visibleStateReadout d system))).direction =
      LinearMap.range (centeredStateReadout d system) := by
  apply le_antisymm
  · rw [direction_affineSpan, vectorSpan_def, Submodule.span_le]
    rintro value ⟨first, ⟨rho, rfl⟩, second, ⟨sigma, rfl⟩, rfl⟩
    let difference : traceZeroHermitian d :=
      ⟨⟨CStarMatrix.ofMatrix.symm rho.1 - CStarMatrix.ofMatrix.symm sigma.1,
        by
          have hrho : (CStarMatrix.ofMatrix.symm rho.1).IsHermitian :=
            congrArg CStarMatrix.ofMatrix.symm rho.2.1.isSelfAdjoint.star_eq
          have hsigma : (CStarMatrix.ofMatrix.symm sigma.1).IsHermitian :=
            congrArg CStarMatrix.ofMatrix.symm sigma.2.1.isSelfAdjoint.star_eq
          exact hrho.sub hsigma⟩,
        by
          change Matrix.trace (CStarMatrix.ofMatrix.symm rho.1 -
            CStarMatrix.ofMatrix.symm sigma.1) = 0
          have hrhoTrace : Matrix.trace (CStarMatrix.ofMatrix.symm rho.1) = 1 := rho.2.2
          have hsigmaTrace : Matrix.trace (CStarMatrix.ofMatrix.symm sigma.1) = 1 := sigma.2.2
          rw [Matrix.trace_sub, hrhoTrace, hsigmaTrace, sub_self]⟩
    refine ⟨difference, ?_⟩
    rw [centeredStateReadout, LinearMap.comp_apply, LinearMap.coe_comp, Function.comp_apply]
    change ambientStateReadout d system (CStarMatrix.ofMatrix.symm rho.1 -
      CStarMatrix.ofMatrix.symm sigma.1) =
      visibleStateReadout d system rho - visibleStateReadout d system sigma
    rw [visible_state_readout_eq_ambient, visible_state_readout_eq_ambient,
      map_sub]
  · rintro value ⟨difference, rfl⟩
    obtain ⟨eps, heps, plus, minus, hmatrices⟩ := traceless_density_perturbations d difference
    have hdifference : visibleStateReadout d system plus -
        visibleStateReadout d system minus =
        (2 * eps) • centeredStateReadout d system difference := by
      rw [visible_state_readout_eq_ambient, visible_state_readout_eq_ambient,
        ← map_sub, hmatrices, map_smul]
      rfl
    have hvsub : visibleStateReadout d system plus - visibleStateReadout d system minus ∈
        vectorSpan ℝ (Set.range (visibleStateReadout d system)) :=
      vsub_mem_vectorSpan ℝ (Set.mem_range_self plus) (Set.mem_range_self minus)
    rw [direction_affineSpan]
    have hscalar : (2 * eps : ℝ) ≠ 0 := mul_ne_zero (by norm_num) heps.ne'
    have hscaled := (vectorSpan ℝ (Set.range (visibleStateReadout d system))).smul_mem
      (2 * eps)⁻¹ hvsub
    rw [hdifference, smul_smul, inv_mul_cancel₀ hscalar, one_smul] at hscaled
    exact hscaled

private theorem centered_readout_injective_of_visible_injective (d : Nat) [NeZero d]
    (system : MatrixOperatorSystem (Fin d))
    (hvisible : Function.Injective (visibleStateReadout d system)) :
    Function.Injective (centeredStateReadout d system) := by
  intro first second hequal
  let difference : traceZeroHermitian d := first - second
  have hzero : centeredStateReadout d system difference = 0 := by
    dsimp only [difference]
    rw [map_sub, hequal, sub_self]
  obtain ⟨eps, heps, plus, minus, hmatrices⟩ := traceless_density_perturbations d difference
  have hreadoutDifference : visibleStateReadout d system plus -
      visibleStateReadout d system minus =
      (2 * eps) • centeredStateReadout d system difference := by
    rw [visible_state_readout_eq_ambient, visible_state_readout_eq_ambient,
      ← map_sub, hmatrices, map_smul]
    rfl
  rw [hzero, smul_zero, sub_eq_zero] at hreadoutDifference
  have hstates : plus = minus := hvisible hreadoutDifference
  have hvalues := congrArg
    (fun rho : DensityState (Fin d) => CStarMatrix.ofMatrix.symm rho.1) hstates
  have hscaled : (2 * eps : ℝ) • difference.1.1 = 0 := by
    rw [← hmatrices]
    exact sub_eq_zero.mpr hvalues
  have hmatrixZero : difference.1.1 = 0 := (smul_eq_zero.mp hscaled).resolve_left
    (mul_ne_zero (by norm_num) heps.ne')
  have hdifferenceZero : difference = 0 := by
    apply Subtype.ext
    apply Subtype.ext
    exact hmatrixZero
  exact sub_eq_zero.mp hdifferenceZero

private theorem density_matrix_set_compact_convex (d : Nat) [NeZero d] : IsCompact
    {matrix : Matrix (Fin d) (Fin d) ℂ | matrix.PosSemidef ∧ Matrix.trace matrix = 1} ∧
    Convex ℝ {matrix : Matrix (Fin d) (Fin d) ℂ | matrix.PosSemidef ∧
      Matrix.trace matrix = 1} := by
  obtain ⟨_, _, rho, _, _⟩ := traceless_density_perturbations d (0 : traceZeroHermitian d)
  let emptyReadout : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] (Empty → ℂ) := 0
  have hrhoPos : (CStarMatrix.ofMatrix.symm rho.1).PosSemidef := by
    rw [← Matrix.nonneg_iff_posSemidef]
    have heq : CStarMatrix.ofMatrix.symm rho.1 =
        CStarMatrix.ofMatrixStarAlgEquiv.symm rho.1 := by ext i j; rfl
    rw [heq]
    exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm rho.2.1
  have hphysical := finite_dimensional_physical_fiber emptyReadout
    (CStarMatrix.ofMatrix.symm rho.1) hrhoPos rho.2.2
  have hset : physicalFiber emptyReadout (CStarMatrix.ofMatrix.symm rho.1) =
      {matrix : Matrix (Fin d) (Fin d) ℂ |
        matrix.PosSemidef ∧ Matrix.trace matrix = 1} := by
    ext matrix; simp [physicalFiber, emptyReadout]
  rw [hset] at hphysical
  exact ⟨hphysical.2.1, hphysical.2.2⟩
theorem visible_state_space_compact_convex_dimension
    (d : Nat) [NeZero d] (system : MatrixOperatorSystem (Fin d)) :
    IsCompact (Set.range (visibleStateReadout d system)) ∧
      Convex ℝ (Set.range (visibleStateReadout d system)) ∧
      Module.finrank ℝ (affineSpan ℝ (Set.range (visibleStateReadout d system))).direction ≤
        Module.finrank ℝ system.carrier - 1 ∧
      (Function.Injective (visibleStateReadout d system) →
        Module.finrank ℝ (affineSpan ℝ (Set.range (visibleStateReadout d system))).direction =
          d ^ 2 - 1) := by
  let densityMatrices : Set (Matrix (Fin d) (Fin d) ℂ) :=
    {matrix | matrix.PosSemidef ∧ Matrix.trace matrix = 1}
  have hdensity := density_matrix_set_compact_convex d
  have hrange : Set.range (visibleStateReadout d system) =
      ambientStateReadout d system '' densityMatrices := by
    ext readout
    constructor
    · rintro ⟨rho, rfl⟩
      refine ⟨CStarMatrix.ofMatrix.symm rho.1, ?_, ?_⟩
      · constructor
        · rw [← Matrix.nonneg_iff_posSemidef]
          have heq : CStarMatrix.ofMatrix.symm rho.1 =
              CStarMatrix.ofMatrixStarAlgEquiv.symm rho.1 := by ext i j; rfl
          rw [heq]
          exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm rho.2.1
        · exact rho.2.2
      · exact (visible_state_readout_eq_ambient d system rho).symm
    · rintro ⟨matrix, hmatrix, rfl⟩
      let rho : DensityState (Fin d) := ⟨CStarMatrix.ofMatrixStarAlgEquiv matrix, by
          constructor
          · exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hmatrix.1.nonneg
          · exact hmatrix.2⟩
      exact ⟨rho, (visible_state_readout_eq_ambient d system rho).trans rfl⟩
  have hcontinuous : Continuous (ambientStateReadout d system) :=
    LinearMap.continuous_of_finiteDimensional _
  have hcompact : IsCompact (Set.range (visibleStateReadout d system)) := by
    rw [hrange]; exact hdensity.1.image hcontinuous
  have hconvex : Convex ℝ (Set.range (visibleStateReadout d system)) := by
    rw [hrange]; exact hdensity.2.linear_image (ambientStateReadout d system)
  refine ⟨hcompact, hconvex, ?_, ?_⟩
  · rw [affine_direction_eq_centered_range d system]
    let identity : system.carrier := ⟨⟨1, IsSelfAdjoint.one _⟩, system.one_mem⟩
    let evaluation : (system.carrier →L[ℝ] ℝ) →ₗ[ℝ] ℝ :=
      { toFun := fun readout => readout identity
        map_add' := by simp
        map_smul' := by simp }
    have hidentity : identity ≠ 0 := by
      intro hzero
      have hone : (1 : CStarMatrix (Fin d) (Fin d) ℂ) = 0 :=
        congrArg (fun effect : system.carrier => effect.1.1) hzero
      exact one_ne_zero hone
    have hevaluation : evaluation ≠ 0 := by
      obtain ⟨functional, hfunctional⟩ := Module.Projective.exists_dual_eq_one ℝ hidentity
      intro hzero
      have := LinearMap.congr_fun hzero (LinearMap.toContinuousLinearMap functional)
      change functional identity = 0 at this
      rw [hfunctional] at this
      norm_num at this
    have hrangeLe : LinearMap.range (centeredStateReadout d system) ≤
        LinearMap.ker evaluation := by
      rintro readout ⟨difference, rfl⟩
      change evaluation (centeredStateReadout d system difference) = 0
      dsimp only [evaluation]
      have htraceReal := congrArg Complex.re difference.2
      rw [centeredStateReadout, LinearMap.comp_apply]
      change (ambientStateReadout d system difference.1.1) identity = 0
      change (Matrix.trace (difference.1.1 * CStarMatrix.ofMatrix.symm identity.1.1)).re = 0
      have hone : CStarMatrix.ofMatrix.symm (1 : CStarMatrix (Fin d) (Fin d) ℂ) =
          (1 : Matrix (Fin d) (Fin d) ℂ) := by ext i j; rfl
      have hidentityValue : identity.1.1 = (1 : CStarMatrix (Fin d) (Fin d) ℂ) := rfl
      rw [hidentityValue, hone, Matrix.mul_one]
      exact htraceReal
    have hkerDimension : Module.finrank ℝ (LinearMap.ker evaluation) =
        Module.finrank ℝ system.carrier - 1 := by
      have hcodimension := Module.Dual.finrank_ker_add_one_of_ne_zero hevaluation
      have hdualDimension : Module.finrank ℝ (system.carrier →L[ℝ] ℝ) =
          Module.finrank ℝ system.carrier := by
        calc
          Module.finrank ℝ (system.carrier →L[ℝ] ℝ) =
              Module.finrank ℝ (Module.Dual ℝ system.carrier) :=
            (LinearMap.toContinuousLinearMap :
              Module.Dual ℝ system.carrier ≃ₗ[ℝ] (system.carrier →L[ℝ] ℝ)).finrank_eq.symm
          _ = Module.finrank ℝ system.carrier := Subspace.dual_finrank_eq
      rw [hdualDimension] at hcodimension
      omega
    exact (Submodule.finrank_mono hrangeLe).trans_eq hkerDimension
  · intro hcomplete
    rw [affine_direction_eq_centered_range d system, LinearMap.finrank_range_of_inj
      (centered_readout_injective_of_visible_injective d system hcomplete),
      trace_zero_hermitian_finrank]
#print axioms visible_state_space_compact_convex_dimension
end D5.S3.Quantum.Measurements.VisibleStateSpaceDimension
