/- GID: D5/S3/VertexAlgebra/RelativePairing/NativeTransverseCoordinates
   generality: I
   mirror-B: none
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact finite native coordinates on the relative transverse original energy sector. -/

import D5.S3.VertexAlgebra.OriginalQEnergyInclusionPairing
import D5.S3.VertexAlgebra.TemporaryTransverseJointBasis16

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace D5.S3.VertexAlgebra.RelativePairing.NativeTransverseCoordinates

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeBcGhostBrstCharge
  LatticeFiniteNegativeGeneration OriginalQQuartetSource OriginalQEnergyInclusionPairing
open scoped BigOperators TensorProduct

noncomputable section

variable (D : LatticeData) (H frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (leftGram : H * gramComplex D = 1) (rightGram : gramComplex D * H = 1)
variable (leftFrame : inverse * frame = 1) (rightFrame : frame * inverse = 1)
variable (beta : Charge D) (xAxis yAxis : Fin D.rank) (level : ℤ)

def downIndex (powers : TransverseDownIndex D xAxis yAxis level) : NativeIndex D :=
  (powers.val, ∅)

private theorem downIndex_injective : Function.Injective (downIndex D xAxis yAxis level) := by
  intro first second equality
  exact Subtype.ext (congrArg Prod.fst equality)

def coordinates : State D →ₗ[ℂ] TransverseDownIndex D xAxis yAxis level →₀ ℂ :=
  (Finsupp.lcomapDomain (downIndex D xAxis yAxis level)
    (downIndex_injective D xAxis yAxis level)).comp
      (nativeCoefficients D frame inverse leftFrame rightFrame beta)

def downState : (TransverseDownIndex D xAxis yAxis level →₀ ℂ) →ₗ[ℂ] State D :=
  Finsupp.linearCombination ℂ (fun powers => nativeWord D frame beta (powers.val, ∅))

theorem coordinates_downState (coefficients : TransverseDownIndex D xAxis yAxis level →₀ ℂ) :
    coordinates D frame inverse leftFrame rightFrame beta xAxis yAxis level
      (downState D frame beta xAxis yAxis level coefficients) = coefficients := by
  classical
  induction coefficients using Finsupp.induction_linear with
  | zero => simp
  | add first second firstProof secondProof =>
    simp only [map_add, firstProof, secondProof]
  | single powers scalar =>
    ext target
    simp only [downState, Finsupp.linearCombination_single, coordinates,
      LinearMap.comp_apply, map_smul, nativeCoefficients_word,
      Finsupp.lcomapDomain_apply, Finsupp.comapDomain_apply, Finsupp.smul_apply]
    simp [downIndex, Finsupp.single_apply, Subtype.ext_iff]

private theorem projector_word (index : NativeIndex D) :
    P D frame inverse leftFrame rightFrame xAxis yAxis (nativeWord D frame beta index) =
      (if kappa D xAxis yAxis index.1 index.2 = 0 then 1 else 0 : ℂ) •
        nativeWord D frame beta index := by
  simpa only [nativeWord, nativeState] using
    P_native D frame inverse leftFrame rightFrame xAxis yAxis beta index.1 1 index.2

theorem projector_coordinates (state : State D)
    (sector : chargeProjection D beta state = state) (index : NativeIndex D) :
    nativeCoefficients D frame inverse leftFrame rightFrame beta
      (P D frame inverse leftFrame rightFrame xAxis yAxis state) index =
    if kappa D xAxis yAxis index.1 index.2 = 0 then
      nativeCoefficients D frame inverse leftFrame rightFrame beta state index else 0 := by
  classical
  let coefficients := nativeCoefficients D frame inverse leftFrame rightFrame beta state
  have expansion := native_sector_finite_expansion D frame inverse leftFrame rightFrame beta state sector
  conv_lhs => rw [← expansion]
  simp only [map_sum, map_smul, projector_word, nativeCoefficients_word,
    Finsupp.finsetSum_apply, Finsupp.smul_apply]
  change (∑ source ∈ coefficients.support,
    coefficients source • ((if kappa D xAxis yAxis source.1 source.2 = 0 then 1 else 0 : ℂ) •
      Finsupp.single source (1 : ℂ) index)) = _
  rw [Finset.sum_eq_single index]
  · simp [coefficients]
  · intro source member different
    simp [Finsupp.single_apply, different, Ne.symm different]
  · intro absent
    have zero : coefficients index = 0 := Finsupp.notMem_support_iff.mp absent
    simp only [zero, zero_smul]

include leftGram rightGram in
theorem downState_coordinates (state : originalEnergySector D H beta level)
    (fixed : P D frame inverse leftFrame rightFrame xAxis yAxis state.val = state.val)
    (relative : B D 0 state.val = 0) :
    downState D frame beta xAxis yAxis level
      (coordinates D frame inverse leftFrame rightFrame beta xAxis yAxis level state.val) =
      state.val := by
  classical
  let coefficients := nativeCoefficients D frame inverse leftFrame rightFrame beta state.val
  have supported (index : NativeIndex D) (member : index ∈ coefficients.support) :
      ∃ powers : TransverseDownIndex D xAxis yAxis level,
        downIndex D xAxis yAxis level powers = index := by
    have nonzero : coefficients index ≠ 0 := Finsupp.mem_support_iff.mp member
    have diagonal := projector_coordinates D frame inverse leftFrame rightFrame beta
      xAxis yAxis state.val state.property.1 index
    rw [fixed] at diagonal
    have zeroOccupation : kappa D xAxis yAxis index.1 index.2 = 0 := by
      by_contra nonzeroOccupation
      rw [if_neg nonzeroOccupation] at diagonal
      exact nonzero diagonal
    have transverse := (kappa_zero_iff D xAxis yAxis index.1 index.2).mp zeroOccupation
    have epsilonAbsent := native_relative_support D frame inverse leftFrame rightFrame beta
      state.val state.property.1 relative index nonzero
    have ghostEmpty : index.2 = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro site present
      have same : site = 3 := Finset.mem_singleton.mp (transverse.2.2 present)
      exact epsilonAbsent (same ▸ present)
    have atLevel := nativeT0_support_level D frame inverse leftFrame rightFrame beta H
      leftGram rightGram level state.val state.property.1 state.property.2 index nonzero
    refine ⟨⟨index.1, transverse.1, transverse.2.1, ?_⟩, ?_⟩
    · simpa only [ghostEmpty] using atLevel
    · exact Prod.ext rfl ghostEmpty.symm
  have bijective : Set.BijOn (downIndex D xAxis yAxis level)
      ((downIndex D xAxis yAxis level) ⁻¹' ↑coefficients.support) ↑coefficients.support := by
    refine ⟨fun _ member => member, (downIndex_injective D xAxis yAxis level).injOn, ?_⟩
    intro index member
    obtain ⟨powers, equality⟩ := supported index member
    exact ⟨powers, by change downIndex D xAxis yAxis level powers ∈ coefficients.support
                      rw [equality]; exact member, equality⟩
  have sumRecovery := Finsupp.sum_comapDomain (downIndex D xAxis yAxis level) coefficients
    (fun index scalar => scalar • nativeWord D frame beta index) bijective
  change (Finsupp.comapDomain (downIndex D xAxis yAxis level) coefficients
    (downIndex_injective D xAxis yAxis level).injOn).sum
      (fun powers scalar => scalar • nativeWord D frame beta (powers.val, ∅)) = state.val
  exact sumRecovery.trans
    (native_sector_finite_expansion D frame inverse leftFrame rightFrame beta
      state.val state.property.1)

theorem energyInput_state (coefficients : TransverseDownIndex D xAxis yAxis level →₀ ℂ) :
    ((energyTransverseDownCombination D H frame inverse leftGram rightGram leftFrame rightFrame
      xAxis yAxis beta level coefficients).val : State D) =
      downState D frame beta xAxis yAxis level coefficients := by
  simp only [energyTransverseDownCombination, downState, Finsupp.linearCombination_apply,
    Finsupp.sum, Submodule.coe_sum, Submodule.coe_smul, energyTransverseDownInput]

theorem downState_tensor (coefficients : TransverseDownIndex D xAxis yAxis level →₀ ℂ) :
    downState D frame beta xAxis yAxis level coefficients =
      Finsupp.single beta (transverseDownOscillator D frame xAxis yAxis level coefficients)
        ⊗ₜ[ℂ] down := by
  simp only [downState, transverseDownOscillator, Finsupp.linearCombination_apply, Finsupp.sum,
    nativeWord, downWord, Finset.sort_empty, List.map_nil, List.prod_nil, Module.End.one_apply,
    Finsupp.single_finsetSum, Finsupp.smul_single, TensorProduct.sum_tmul,
    TensorProduct.smul_tmul]
  simp only [← Finsupp.smul_single, TensorProduct.smul_tmul']

#print axioms downState_coordinates
#print axioms projector_coordinates

end
end D5.S3.VertexAlgebra.RelativePairing.NativeTransverseCoordinates
