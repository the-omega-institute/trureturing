/- GID: D5/S3/VertexAlgebra/OriginalAbsoluteGhostSupport
   generality: G
   mirror-B: none
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integral ghost degree separates the two actual kappa-zero native branches. -/

import D5.S3.VertexAlgebra.RelativePairing.NativePhysicalRealization
import D5.S3.VertexAlgebra.OriginalNonzeroGhostMultiplicity

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace D5.S3.VertexAlgebra.OriginalAbsoluteGhostSupport

open LatticeGeneratingFieldLocality LatticeBcGhostBrstCharge BcGhostFockSupport
  OriginalQQuartetSource OriginalBrstReassembly
open scoped BigOperators TensorProduct

noncomputable section

variable (D : LatticeData) (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (leftFrame : inverse * frame = 1) (rightFrame : frame * inverse = 1)
variable (beta : Charge D)

def nativeGhostDegree (index : NativeIndex D) : ℤ :=
  1 + epsilonCount index.2 + (thetaCount index.2 : ℤ) - (etaCount index.2 : ℤ)

theorem nativeWord_number (index : NativeIndex D) :
    nativeJ D (nativeWord D frame beta index) =
      (nativeGhostDegree D index : ℂ) • nativeWord D frame beta index := by
  simpa only [nativeGhostDegree, nativeJ] using nativeWord_J D frame beta index

theorem native_number_coeff (state : State D)
    (sector : chargeProjection D beta state = state) (index : NativeIndex D) :
    nativeCoefficients D frame inverse leftFrame rightFrame beta (nativeJ D state) index =
      (nativeGhostDegree D index : ℂ) *
        nativeCoefficients D frame inverse leftFrame rightFrame beta state index := by
  classical
  let coefficients := nativeCoefficients D frame inverse leftFrame rightFrame beta state
  have expansion := native_sector_finite_expansion D frame inverse leftFrame rightFrame
    beta state sector
  conv_lhs => rw [← expansion]
  simp only [map_sum, map_smul, nativeWord_number, nativeCoefficients_word,
    Finsupp.finsetSum_apply, Finsupp.smul_apply]
  change (∑ source ∈ coefficients.support,
    coefficients source • ((nativeGhostDegree D source : ℂ) •
      Finsupp.single source (1 : ℂ) index)) = _
  rw [Finset.sum_eq_single index]
  · simp [coefficients, mul_comm]
  · intro source member different
    simp [Finsupp.single_apply, different, Ne.symm different]
  · intro absent
    have zero : coefficients index = 0 := Finsupp.notMem_support_iff.mp absent
    simp [zero, coefficients] at *

theorem native_ghost_support (degree : ℤ) (state : State D)
    (sector : chargeProjection D beta state = state)
    (homogeneous : state ∈ ghostPart D degree) (index : NativeIndex D)
    (nonzero : nativeCoefficients D frame inverse leftFrame rightFrame beta state index ≠ 0) :
    nativeGhostDegree D index = degree := by
  have equation := congrArg
    (fun vector => nativeCoefficients D frame inverse leftFrame rightFrame beta vector index)
    ((ghostPart_iff_number D degree state).mp homogeneous)
  rw [native_number_coeff D frame inverse leftFrame rightFrame beta state sector index,
    map_smul, Finsupp.smul_apply, smul_eq_mul] at equation
  exact Int.cast_injective (mul_right_cancel₀ nonzero equation)

theorem kappa_zero_ghost_branches (xAxis yAxis : Fin D.rank) (index : NativeIndex D)
    (occupation : kappa D xAxis yAxis index.1 index.2 = 0) :
    (index.2 = ∅ ∧ nativeGhostDegree D index = 1) ∨
      (index.2 = {3} ∧ nativeGhostDegree D index = 2) := by
  classical
  have onlyEpsilon := ((kappa_zero_iff D xAxis yAxis index.1 index.2).mp occupation).2.2
  by_cases present : 3 ∈ index.2
  · have singleton : index.2 = {3} := Finset.Subset.antisymm onlyEpsilon
      (Finset.singleton_subset_iff.mpr present)
    right
    refine ⟨singleton, ?_⟩
    norm_num [nativeGhostDegree, singleton, epsilonCount, thetaCount, etaCount,
      Finset.filter_insert, Finset.filter_singleton]
  · have empty : index.2 = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
      intro site member
      have equality := Finset.mem_singleton.mp (onlyEpsilon member)
      exact present (equality ▸ member))
    left
    refine ⟨empty, ?_⟩
    norm_num [nativeGhostDegree, empty, epsilonCount, thetaCount, etaCount,
      Finset.filter_insert, Finset.filter_singleton]

theorem projector_ghost_support (xAxis yAxis : Fin D.rank) (degree : ℤ) (state : State D)
    (sector : chargeProjection D beta state = state)
    (fixed : P D frame inverse leftFrame rightFrame xAxis yAxis state = state)
    (homogeneous : state ∈ ghostPart D degree) (index : NativeIndex D)
    (nonzero : nativeCoefficients D frame inverse leftFrame rightFrame beta state index ≠ 0) :
    (index.2 = ∅ ∧ degree = 1) ∨ (index.2 = {3} ∧ degree = 2) := by
  have diagonal := RelativePairing.NativeTransverseCoordinates.projector_coordinates
    D frame inverse leftFrame rightFrame beta xAxis yAxis state sector index
  rw [fixed] at diagonal
  have occupation : kappa D xAxis yAxis index.1 index.2 = 0 := by
    by_contra different
    rw [if_neg different] at diagonal
    exact nonzero diagonal
  have degreeEquation := native_ghost_support D frame inverse leftFrame rightFrame
    beta degree state sector homogeneous index nonzero
  simpa only [degreeEquation] using kappa_zero_ghost_branches D xAxis yAxis index occupation

theorem ghost_one_projector_relative (xAxis yAxis : Fin D.rank) (state : State D)
    (sector : chargeProjection D beta state = state)
    (fixed : P D frame inverse leftFrame rightFrame xAxis yAxis state = state)
    (homogeneous : state ∈ ghostPart D 1) : B D 0 state = 0 := by
  classical
  rw [← native_sector_finite_expansion D frame inverse leftFrame rightFrame beta state sector]
  simp only [map_sum, map_smul]
  apply Finset.sum_eq_zero
  intro index member
  have branches := projector_ghost_support D frame inverse leftFrame rightFrame beta
    xAxis yAxis 1 state sector fixed homogeneous index (Finsupp.mem_support_iff.mp member)
  have empty : index.2 = ∅ := by
    rcases branches with branch | branch
    · exact branch.1
    · omega
  simp only [nativeWord_Bzero, empty, Finset.notMem_empty, if_false, smul_zero]

theorem projector_other_ghost_vanishes (xAxis yAxis : Fin D.rank) (degree : ℤ)
    (notOne : degree ≠ 1) (notTwo : degree ≠ 2) (state : State D)
    (sector : chargeProjection D beta state = state)
    (fixed : P D frame inverse leftFrame rightFrame xAxis yAxis state = state)
    (homogeneous : state ∈ ghostPart D degree) : state = 0 := by
  classical
  rw [← native_sector_finite_expansion D frame inverse leftFrame rightFrame beta state sector]
  apply Finset.sum_eq_zero
  intro index member
  have branches := projector_ghost_support D frame inverse leftFrame rightFrame beta
    xAxis yAxis degree state sector fixed homogeneous index (Finsupp.mem_support_iff.mp member)
  exact False.elim (branches.elim (fun branch => notOne branch.2) (fun branch => notTwo branch.2))

#print axioms native_ghost_support
#print axioms ghost_one_projector_relative
#print axioms projector_other_ghost_vanishes

end
end D5.S3.VertexAlgebra.OriginalAbsoluteGhostSupport
