/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/UniformNativeCriticalMatrix
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/UniformNativeCriticalMatrix
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Polynomial rank criterion at every residual length. -/
import D5.S3.Combinatorics.Matroids.LinearRado
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.UniformNativeRotation

/-!
# Polynomial rank criterion at every residual length

At the positive mixed-trace slice the physical chart has eight independent real
directions. Its raw Pauli differential, augmented by the raw value, gives a
polynomial matrix with ten rows and nine columns. Normalization removes one
dimension from the image, so its maximal minors detect full rank of the
normalized adjacent marginal.
-/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.UniformNativeCriticalMatrix

open Function Matrix MvPolynomial
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open TwoQubitMarginalReflection (Density)
open PeriodicMPSCompactReadout (Readout readout)
open SevenSiteCriticalCertificate (observedRow)
open SevenSitePhysicalRankBridge
  (Rotation SlicePoint physicalChart sliceOrdinary rotationLine analyticAt_physicalChart
    bijective_fderiv_physicalChart_center)
open UniformRankNormalization (ordinaryAmplitude ordinaryRaw ordinaryMarginal rawReadout
  finrank_rawReadout_span)
open PeriodicMPSUniformNativeSliceReadout (rawSlicePolynomial eval_rawSlicePolynomial_eq_moment
  rawReadout_slice_eq_eval fderiv_rawReadout_sliceColumn)
open UniformNativeRotation (rotationPolynomial eval_rotationPolynomial_real
  fderiv_rawReadout_rotationColumn)

open private columnTangent coordinates sum_columnTangent moment_real from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSitePhysicalRankAssembly
open private hasDerivAt_eval_slice_line from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSitePhysicalRankBridge
open private isHermitian_pairGram from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteCompactReadout
open private differentiable_ordinaryMass differentiable_ordinaryRaw from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.UniformRankNormalization

noncomputable section

/-- The trace and nine Pauli rows, with columns for the five slice partials,
the raw value, and the three physical rotations in the seven-site order. -/
def criticalMatrix (m : ℕ) : Matrix (Fin 10) (Fin 9) (MvPolynomial (Fin 5) ℂ) :=
  fun i j =>
    let ab := observedRow i
    if h : j.val < 5 then pderiv ⟨j.val, h⟩ (rawSlicePolynomial m ab)
    else if j = 5 then rawSlicePolynomial m ab
    else rotationPolynomial m ⟨j.val - 6, by omega⟩ ab

private def realMatrix (m : ℕ) (x : SlicePoint) : Matrix (Fin 10) (Fin 9) ℝ :=
  (criticalMatrix m).map fun p => (eval (fun k => (x k : ℂ)) p).re

private theorem eval_value_real (m : ℕ) (x : SlicePoint) (ab : Fin 4 × Fin 4) :
    ((eval (fun k => (x k : ℂ)) (rawSlicePolynomial m ab)).re : ℂ) =
      eval (fun k => (x k : ℂ)) (rawSlicePolynomial m ab) := by
  rw [eval_rawSlicePolynomial_eq_moment]
  exact moment_real ab (isHermitian_pairGram (ordinaryAmplitude m (sliceOrdinary x)))

private theorem eval_partial_real (m : ℕ) (x : SlicePoint) (ab : Fin 4 × Fin 4) (j : Fin 5) :
    ((eval (fun k => (x k : ℂ)) (pderiv j (rawSlicePolynomial m ab))).re : ℂ) =
      eval (fun k => (x k : ℂ)) (pderiv j (rawSlicePolynomial m ab)) := by
  have h := hasDerivAt_eval_slice_line (rawSlicePolynomial m ab) x j
  have hReal := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 h).ofReal_comp
  have heq (t : ℝ) := eval_value_real m (x + t • Pi.single j 1) ab
  exact (hReal.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => (heq t).symm)).unique h

private theorem realMatrix_cast (m : ℕ) (x : SlicePoint) (i : Fin 10) (j : Fin 9) :
    (realMatrix m x i j : ℂ) = eval (fun k => (x k : ℂ)) (criticalMatrix m i j) := by
  by_cases hj : j.val < 5
  · simpa only [realMatrix, Matrix.map_apply, criticalMatrix, dite_eq_left hj] using
      eval_partial_real m x (observedRow i) ⟨j.val, hj⟩
  · by_cases hv : j = 5
    · simpa only [realMatrix, Matrix.map_apply, criticalMatrix, dite_eq_right hj, ite_eq_left hv] using
        eval_value_real m x (observedRow i)
    · simpa only [realMatrix, Matrix.map_apply, criticalMatrix, dite_eq_right hj, ite_eq_right hv] using
        eval_rotationPolynomial_real m x ⟨j.val - 6, by omega⟩ (observedRow i)

private abbrev Tangent := Rotation × SlicePoint

private def augmented (m : ℕ) (x : SlicePoint) : Tangent × ℝ →ₗ[ℝ] ℝ × Readout :=
  (fderiv ℝ (rawReadout m ∘ physicalChart 1) (0, x)).toLinearMap.coprod
    ((LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight (rawReadout m (sliceOrdinary x)))

private def rowCoordinates : (ℝ × Readout) ≃ₗ[ℝ] (Fin 10 → ℝ) :=
  Fin.consLinearEquiv ℝ (fun _ : Fin 10 => ℝ)

private theorem rowCoordinates_apply (v : ℝ × Readout) (i : Fin 10) :
    rowCoordinates v i = Fin.cons (α := fun _ => ℝ) v.1 v.2 i :=
  rfl

private theorem augmented_tangent (m : ℕ) (x : SlicePoint) (v : Tangent) :
    augmented m x (v, 0) = fderiv ℝ (rawReadout m ∘ physicalChart 1) (0, x) v := by
  simp [augmented]

private theorem augmented_value (m : ℕ) (x : SlicePoint) :
    augmented m x (0, 1) = rawReadout m (sliceOrdinary x) := by
  simp [augmented]

private theorem augmented_column (m : ℕ) (x : SlicePoint) (i : Fin 10) (j : Fin 9) :
    rowCoordinates (augmented m x (columnTangent j)) i = realMatrix m x i j := by
  by_cases hj : j.val < 5
  · simpa only [columnTangent, realMatrix, Matrix.map_apply, criticalMatrix, dite_eq_left hj,
      augmented_tangent, rowCoordinates_apply] using
      fderiv_rawReadout_sliceColumn m x i ⟨j.val, hj⟩
  · by_cases hv : j = 5
    · simpa only [columnTangent, realMatrix, Matrix.map_apply, criticalMatrix, dite_eq_right hj,
        ite_eq_left hv, augmented_value, rowCoordinates_apply] using rawReadout_slice_eq_eval m x i
    · simpa only [columnTangent, realMatrix, Matrix.map_apply, criticalMatrix, dite_eq_right hj,
        ite_eq_right hv, augmented_tangent, rowCoordinates_apply] using
        fderiv_rawReadout_rotationColumn m x i ⟨j.val - 6, by omega⟩

private def columnCombination : (Fin 9 → ℝ) →ₗ[ℝ] Tangent × ℝ :=
  Fintype.linearCombination ℝ columnTangent

private theorem columnCombination_surjective : Surjective columnCombination :=
  fun v => ⟨coordinates v, sum_columnTangent v⟩

private theorem mulVecLin_realMatrix (m : ℕ) (x : SlicePoint) :
    (realMatrix m x).mulVecLin =
      (rowCoordinates.toLinearMap.comp (augmented m x)).comp columnCombination := by
  apply LinearMap.ext
  intro c
  funext i
  calc
    _ = ∑ j : Fin 9, c j • rowCoordinates (augmented m x (columnTangent j)) i := by
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, ← augmented_column,
        smul_eq_mul]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    _ = _ := by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, columnCombination,
        Fintype.linearCombination_apply, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply]

private theorem range_augmented (m : ℕ) (x : SlicePoint) (hx : 0 < x 1) :
    LinearMap.range (augmented m x) =
      LinearMap.range (fderiv ℝ (rawReadout m) (sliceOrdinary x)).toLinearMap ⊔
        Submodule.span ℝ {rawReadout m (sliceOrdinary x)} := by
  let D := (fderiv ℝ (rawReadout m) (sliceOrdinary x)).toLinearMap
  let P := (fderiv ℝ (physicalChart 1) ((0 : Rotation), x)).toLinearMap
  have hraw : Differentiable ℝ (rawReadout m) :=
    (differentiable_ordinaryMass m).prodMk
      (readout.differentiable.comp (differentiable_ordinaryRaw m))
  have hcomp :
      (fderiv ℝ (rawReadout m ∘ physicalChart 1) (0, x)).toLinearMap = D.comp P := by
    have hchart := (analyticAt_physicalChart 1 ((0 : Rotation), x)).differentiableAt
    exact congrArg (fun L : Tangent →L[ℝ] ℝ × Readout => L.toLinearMap)
      (fderiv_comp (0, x) (hraw (sliceOrdinary x)) hchart)
  have hP : LinearMap.range P = ⊤ :=
    LinearMap.range_eq_top.mpr (bijective_fderiv_physicalChart_center x hx).2
  have hId : Surjective (LinearMap.id : ℝ →ₗ[ℝ] ℝ) := fun t => ⟨t, rfl⟩
  rw [augmented, LinearMap.range_coprod, hcomp, LinearMap.range_comp_of_range_eq_top D hP,
    LinearMap.range_smulRight_apply_of_surjective hId]

private theorem rank_realMatrix (m : ℕ) (x : SlicePoint) (hx : 0 < x 1)
    (hA : ordinaryAmplitude m (sliceOrdinary x) ≠ 0) :
    (realMatrix m x).rank =
      Module.finrank ℝ (LinearMap.range (fderiv ℝ (ordinaryMarginal m)
        (sliceOrdinary x)).toLinearMap : Submodule ℝ Density) + 1 := by
  calc
    _ = Module.finrank ℝ (LinearMap.range (rowCoordinates.toLinearMap.comp (augmented m x))) := by
      rw [Matrix.rank, mulVecLin_realMatrix,
        LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr
          columnCombination_surjective)]
    _ = Module.finrank ℝ (LinearMap.range (augmented m x)) := by
      rw [LinearMap.range_comp]
      exact rowCoordinates.finrank_map_eq _
    _ = _ := by
      rw [range_augmented m x hx]
      exact (finrank_rawReadout_span m (sliceOrdinary x) hA).1

private theorem rank_eq_nine_iff_minor (A : Matrix (Fin 10) (Fin 9) ℝ) :
    A.rank = 9 ↔ ∃ d : Fin 10, (A.submatrix d.succAbove id).det ≠ 0 := by
  classical
  constructor
  · intro hRank
    have hSpan : Submodule.span ℝ (Set.range A.row) = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [← Matrix.rank_eq_finrank_span_row, hRank, Module.finrank_pi, Fintype.card_fin]
    obtain ⟨f, hf, hdet⟩ :=
      D5.S3.Combinatorics.Matroids.LinearRado.exists_nonsingular_rows A hSpan
    have hn : ¬ Surjective f := by
      intro h
      have hcard := Fintype.card_le_of_surjective f h
      norm_num [Fintype.card_fin] at hcard
    change ¬ ∀ i, ∃ j, f j = i at hn
    obtain ⟨d, hd⟩ := not_forall.mp hn
    let g : Fin 9 → Fin 9 := fun j =>
      (finSuccAboveEquiv d).symm ⟨f j, fun h => hd ⟨j, h⟩⟩
    have hg (j : Fin 9) : d.succAbove (g j) = f j := by
      have h := (finSuccAboveEquiv d).apply_symm_apply
        (⟨f j, fun h => hd ⟨j, h⟩⟩ : {i : Fin 10 // i ≠ d})
      exact congrArg Subtype.val h
    have hgi : Injective g := by
      intro a b h
      apply hf
      rw [← hg a, ← hg b, h]
    let e : Equiv.Perm (Fin 9) :=
      Equiv.ofBijective g ⟨hgi, Finite.injective_iff_surjective.mp hgi⟩
    refine ⟨d, fun hz => hdet ?_⟩
    have he : A.submatrix f id = (A.submatrix d.succAbove id).submatrix e id := by
      apply Matrix.ext
      intro i j
      change A (f i) j = A (d.succAbove (g i)) j
      rw [hg]
    rw [he, Matrix.det_permute, hz, mul_zero]
  · rintro ⟨d, hd⟩
    have hl := Matrix.rank_submatrix_le A d.succAbove id
    rw [Matrix.rank_of_det_ne_zero hd, Fintype.card_fin] at hl
    exact le_antisymm (by simpa only [Fintype.card_fin] using A.rank_le_card_width) hl

private theorem eval_minor_eq (m : ℕ) (x : SlicePoint) (d : Fin 10) :
    eval (fun k => (x k : ℂ)) ((criticalMatrix m).submatrix d.succAbove id).det =
      (((realMatrix m x).submatrix d.succAbove id).det : ℂ) := by
  let e := MvPolynomial.eval (fun k : Fin 5 => (x k : ℂ))
  change e ((criticalMatrix m).submatrix d.succAbove id).det =
    Complex.ofRealHom ((realMatrix m x).submatrix d.succAbove id).det
  rw [e.map_det, Complex.ofRealHom.map_det]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  exact (realMatrix_cast m x (d.succAbove i) j).symm

/-- At a positive mixed-trace slice point with nonzero amplitude, the literal
normalized adjacent marginal for a ring of length `2 + m` has real derivative
rank eight exactly when a maximal minor of the polynomial matrix evaluates
to a nonzero number. -/
theorem ordinaryMarginal_rank_eq_eight_iff_minor (m : ℕ) (x : SlicePoint) (hx : 0 < x 1)
    (hA : ordinaryAmplitude m (sliceOrdinary x) ≠ 0) :
    Module.finrank ℝ (LinearMap.range (fderiv ℝ (ordinaryMarginal m)
      (sliceOrdinary x)).toLinearMap : Submodule ℝ Density) = 8 ↔
      ∃ d : Fin 10, eval (fun k => (x k : ℂ))
        ((criticalMatrix m).submatrix d.succAbove id).det ≠ 0 := by
  calc
    _ ↔ (realMatrix m x).rank = 9 := by
      rw [rank_realMatrix m x hx hA]
      omega
    _ ↔ _ := by
      rw [rank_eq_nine_iff_minor]
      simp only [eval_minor_eq, Complex.ofReal_ne_zero]

#print axioms ordinaryMarginal_rank_eq_eight_iff_minor

end

end D5.S3.Quantum.TensorNetworks.UniformNativeCriticalMatrix
