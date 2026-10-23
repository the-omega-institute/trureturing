/- GID: D5/S3/Quantum/Fibers/DensityConjugationGeometry
   generality: I
   mirror-B: D5/B/S3/Quantum/Fibers/DensityConjugationGeometry
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Topology.MetricSpace.HausdorffDimension]
   utility: none
   digest: The nonreal density conjugation quotient has Hausdorff dimension twenty-four. -/

import D5.S3.Quantum.Fibers.RealCopyConjugation
import D5.S3.Geometry.InvolutionOrbitDimension
import Mathlib.Analysis.Normed.Affine.AddTorsorBases

/-! The orbit metric on actual normalized density states, including singular states. -/

set_option autoImplicit false
noncomputable section
open Set Metric Topology MeasureTheory
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.Elementwise

namespace D5.S3.Quantum.Fibers.DensityConjugationGeometry
open D5.S3.Quantum.Fibers.RealCopyConjugation
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Measurement.BasisMeasurementProjection
open D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Measurements.VisibleStateSpaceDimension
open D5.S3.Quantum.Fibers.FiveModeRealResponse
open D5.S3.Geometry.InvolutionOrbitDimension

/-- Centered coordinates of trace-one Hermitian matrices, with the inherited matrix norm. -/
abbrev Coordinates := traceZeroHermitian 5

private def center : Matrix (Fin 5) (Fin 5) ℂ := (1 / 5 : ℂ) • 1

private theorem center_trace : Matrix.trace center = 1 := by
  norm_num [center, Matrix.trace_smul]

private theorem center_hermitian : center.IsHermitian := by
  simpa [center] using (Matrix.isHermitian_one (n := Fin 5) (α := ℂ)).smul
    (k := (1 / 5 : ℂ)) (by norm_num [IsSelfAdjoint])

/-- Subtract the maximally mixed density matrix; this is a bijective physical coordinate map. -/
def coordinate (rho : FiveModeState) : Coordinates :=
  ⟨⟨stateMatrix rho - center, (density_posSemidef rho).isHermitian.sub center_hermitian⟩,
    by change Matrix.trace (stateMatrix rho - center) = 0
       rw [Matrix.trace_sub, show Matrix.trace (stateMatrix rho) = 1 from rho.2.2,
         center_trace, sub_self]⟩

/-- Positivity is imposed on the actual trace-one matrix reconstructed from a coordinate. -/
def physical : Set Coordinates := {x | (center + x.1.1).PosSemidef}

private theorem coordinate_physical (rho : FiveModeState) : coordinate rho ∈ physical := by
  change (center + (stateMatrix rho - center)).PosSemidef
  convert density_posSemidef rho using 1; abel

private theorem coordinate_injective : Function.Injective coordinate := by
  intro rho sigma h
  apply Subtype.ext
  have hh := congrArg (fun x : Coordinates => x.1.1) h
  change stateMatrix rho - center = stateMatrix sigma - center at hh
  have hm := congrArg (fun M => M + center) hh
  simp only [sub_add_cancel] at hm
  exact congrArg CStarMatrix.ofMatrix hm

/-- Reconstruct the native positive normalized density state, with no rank restriction. -/
def stateOfCoordinate (x : Coordinates) (hx : x ∈ physical) : FiveModeState :=
  ⟨CStarMatrix.ofMatrix (center + x.1.1),
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hx.nonneg, by
      change Matrix.trace (center + x.1.1) = 1
      rw [Matrix.trace_add, center_trace, x.2, add_zero]⟩

private theorem coordinate_state (x : Coordinates) (hx : x ∈ physical) :
    coordinate (stateOfCoordinate x hx) = x := by
  apply Subtype.ext
  apply Subtype.ext
  change (center + x.1.1) - center = x.1.1
  exact add_sub_cancel_left _ _

/-- Transpose on centered Hermitian matrices is conjugation and is an isometry. -/
def transpose : Coordinates ≃ᵢ Coordinates where
  toFun x := ⟨⟨x.1.1.transpose, (show x.1.1.IsHermitian from x.1.2).transpose⟩,
    (Matrix.trace_transpose _).trans x.2⟩
  invFun x := ⟨⟨x.1.1.transpose, (show x.1.1.IsHermitian from x.1.2).transpose⟩,
    (Matrix.trace_transpose _).trans x.2⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; exact Matrix.transpose_transpose _
  right_inv x := by apply Subtype.ext; apply Subtype.ext; exact Matrix.transpose_transpose _
  isometry_toFun := by
    apply Isometry.of_dist_eq
    intro x y
    simp only [dist_eq_norm]
    change ‖x.1.1.transpose - y.1.1.transpose‖ = ‖x.1.1 - y.1.1‖
    rw [← Matrix.transpose_sub, Matrix.norm_transpose]

private theorem transpose_involutive : Function.Involutive transpose := by
  intro x
  apply Subtype.ext
  apply Subtype.ext
  exact Matrix.transpose_transpose _

private theorem coordinate_conjugate (rho : FiveModeState) :
    coordinate (conjugate rho) = transpose (coordinate rho) := by
  apply Subtype.ext
  apply Subtype.ext
  change (stateMatrix rho).transpose - center = (stateMatrix rho - center).transpose
  rw [Matrix.transpose_sub]
  congr 1
  simp [center]

private theorem physical_convex : Convex ℝ physical := by
  have h := (density_matrix_set_compact_convex 5).2
  intro x hx y hy a b ha hb hab
  have htrace (z : Coordinates) : Matrix.trace (center + z.1.1) = 1 := by
    rw [Matrix.trace_add, center_trace, z.2, add_zero]
  have hh := h ⟨hx, htrace x⟩ ⟨hy, htrace y⟩ ha hb hab
  change (center + (a • x.1.1 + b • y.1.1)).PosSemidef
  have he : center + (a • x.1.1 + b • y.1.1) =
      a • (center + x.1.1) + b • (center + y.1.1) := by
    rw [smul_add, smul_add, add_add_add_comm, ← add_smul, hab, one_smul]
  rw [he]
  exact hh.1

private theorem physical_span : vectorSpan ℝ physical = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨eps, heps, plus, minus, hmatrices⟩ := traceless_density_perturbations 5 x
  have hdiff : coordinate plus - coordinate minus = (2 * eps) • x := by
    apply Subtype.ext
    apply Subtype.ext
    change (stateMatrix plus - center) - (stateMatrix minus - center) = _
    rw [sub_sub_sub_cancel_right]
    exact hmatrices
  have hv := vsub_mem_vectorSpan ℝ (coordinate_physical plus) (coordinate_physical minus)
  change coordinate plus - coordinate minus ∈ vectorSpan ℝ physical at hv
  rw [hdiff] at hv
  have hs := (vectorSpan ℝ physical).smul_mem (2 * eps)⁻¹ hv
  rw [smul_smul, inv_mul_cancel₀ (mul_ne_zero (by norm_num) heps.ne'), one_smul] at hs
  exact hs

private theorem physical_interior : (interior physical).Nonempty := by
  have hne : (affineSpan ℝ physical : Set Coordinates).Nonempty := by
    obtain ⟨eps, heps, plus, minus, hmatrices⟩ :=
      traceless_density_perturbations 5 (0 : Coordinates)
    exact ⟨coordinate plus, subset_affineSpan ℝ physical (coordinate_physical plus)⟩
  apply physical_convex.interior_nonempty_iff_affineSpan_eq_top.mpr
  apply (AffineSubspace.direction_eq_top_iff_of_nonempty hne).mp
  rw [direction_affineSpan, physical_span]

private def fixedSpace : Submodule ℝ Coordinates where
  carrier := {x | transpose x = x}
  zero_mem' := by apply Subtype.ext; apply Subtype.ext; simp [transpose]
  add_mem' := by
    intro x y hx hy
    change transpose (x + y) = x + y
    change transpose x = x at hx
    change transpose y = y at hy
    have hh : transpose (x + y) = transpose x + transpose y := by
      apply Subtype.ext; apply Subtype.ext; exact Matrix.transpose_add _ _
    rw [hh, hx, hy]
  smul_mem' := by
    intro a x hx
    change transpose (a • x) = a • x
    change transpose x = x at hx
    have hh : transpose (a • x) = a • transpose x := by
      apply Subtype.ext; apply Subtype.ext; exact Matrix.transpose_smul _ _
    rw [hh, hx]

private theorem fixedSpace_ne_top : fixedSpace ≠ ⊤ := by
  intro htop
  let rho : FiveModeState := ⟨CStarMatrix.ofMatrix (pairState 1),
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv orthogonal_pair_same_actual_responses.1.nonneg,
    orthogonal_pair_same_actual_responses.2.1⟩
  have hx : coordinate rho ∈ fixedSpace := by rw [htop]; trivial
  have he := congrArg (fun x : Coordinates => (x.1.1 0 1).im)
    (show transpose (coordinate rho) = coordinate rho from hx)
  norm_num [transpose, coordinate, rho, stateMatrix, center, pairState, pairKet,
    Matrix.vecMulVec, Pi.single_apply] at he

/-- All nonreal physical states in centered coordinates, including every singular stratum. -/
def nonrealPhysical : Set Coordinates := {x ∈ physical | transpose x ≠ x}

private theorem nonreal_physical_dimension : dimH nonrealPhysical = 24 := by
  have hnot : ¬ interior physical ⊆ (fixedSpace : Set Coordinates) := by
    intro hsub
    apply fixedSpace_ne_top
    apply Submodule.eq_top_of_nonempty_interior' fixedSpace
    exact physical_interior.mono (interior_maximal hsub isOpen_interior)
  simp only [Set.subset_def, not_forall] at hnot
  obtain ⟨x, hx, hn⟩ := hnot
  have hne : IsOpen {x : Coordinates | transpose x ≠ x} :=
    isOpen_ne_fun transpose.continuous continuous_id
  have hnhds : nonrealPhysical ∈ 𝓝 x :=
    Filter.inter_mem (mem_interior_iff_mem_nhds.mp hx) (hne.mem_nhds hn)
  rw [Real.dimH_of_mem_nhds hnhds, trace_zero_hermitian_finrank]
  norm_num

/-- A metric realization of the literal density-state quotient in the centered matrix orbit space. -/
def orbitRealization :
    fiveModeOrbitQuotient → Orbit transpose transpose_involutive :=
  Quotient.lift (fun rho => project transpose transpose_involutive (coordinate rho)) (by
    intro rho sigma h
    rcases h with rfl | rfl
    · rfl
    · change Quotient.mk _ (coordinate rho) = Quotient.mk _ (coordinate (conjugate rho))
      apply Quotient.sound
      refine ⟨Multiplicative.ofAdd true, ?_⟩
      exact (coordinate_conjugate rho).symm)

private theorem orbitRealization_injective : Function.Injective orbitRealization := by
  intro q r
  induction q using Quotient.inductionOn with
  | h rho =>
    induction r using Quotient.inductionOn with
    | h sigma =>
      intro h
      obtain ⟨g, hg⟩ := Quotient.exact h
      apply Quotient.sound
      change Bool at g
      cases g
      · left
        apply coordinate_injective
        exact hg.symm
      · right
        apply coordinate_injective
        exact hg.symm.trans (coordinate_conjugate rho).symm

/-- The actual density orbit quotient carries the metric induced by its isometric orbit realization. -/
instance fiveModeOrbitMetric : MetricSpace fiveModeOrbitQuotient :=
  MetricSpace.induced orbitRealization orbitRealization_injective inferInstance

/-- The nonreal part of the literal quotient; real density states remain in the ambient quotient. -/
def fiveModeNonrealQuotient : Set fiveModeOrbitQuotient :=
  fiveModeOrbitProjection '' {rho | conjugate rho ≠ rho}

private theorem realization_nonreal_image :
    orbitRealization '' fiveModeNonrealQuotient =
      project transpose transpose_involutive '' nonrealPhysical := by
  ext q
  constructor
  · rintro ⟨_, ⟨rho, hrho, rfl⟩, rfl⟩
    refine ⟨coordinate rho, ⟨coordinate_physical rho, ?_⟩, rfl⟩
    intro h
    apply hrho
    apply coordinate_injective
    exact (coordinate_conjugate rho).trans h
  · rintro ⟨x, ⟨hx, hfree⟩, rfl⟩
    let rho := stateOfCoordinate x hx
    have hc : coordinate rho = x := coordinate_state x hx
    refine ⟨fiveModeOrbitProjection rho, ⟨rho, ?_, rfl⟩, ?_⟩
    · intro h
      apply hfree
      calc
        transpose x = coordinate (conjugate rho) := by rw [← hc, coordinate_conjugate]
        _ = coordinate rho := congrArg coordinate h
        _ = x := hc
    · change project transpose transpose_involutive (coordinate rho) = _
      rw [hc]

/-- The entire nonreal normalized-density conjugation quotient has intrinsic real Hausdorff
 dimension 24 in its finite-action orbit metric. No rank stratum is removed. -/
theorem five_mode_nonreal_quotient_dimension : dimH fiveModeNonrealQuotient = 24 := by
  have hi : Isometry orbitRealization :=
    MetricSpace.isometry_induced orbitRealization orbitRealization_injective
  rw [← hi.dimH_image fiveModeNonrealQuotient, realization_nonreal_image,
    dimH_project, nonreal_physical_dimension]

#print axioms five_mode_nonreal_quotient_dimension
end D5.S3.Quantum.Fibers.DensityConjugationGeometry
