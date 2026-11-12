/-
SOURCE_ONLY_UNCOMPILED.

Finite joint integral zero-current weights of actual Omega, consumed from
the actual opposite-charge/Taylor proof, with the original rational dual
parameter. This file derives the auxiliary coordinate projections before
Q normalization. ActualGroundCanonicalProjectors subsequently identifies
the concrete finite basis product of Q with the joint projection.

The direct-sum operations and eigenspace independence are pinned Mathlib.
The physical dual parameter and dual equation are reused from the canonical
LatticeDiscriminantTheta / ActualZhuMinimum APIs; no Zhu-bottom restriction
is placed on the arbitrary module.
-/
import D5.S3.VertexAlgebra.Modules.ActualGroundFiniteReconstruction
import D5.S3.VertexAlgebra.Lattice.ActualZhuMinimum
import Mathlib.LinearAlgebra.Eigenspace.Pi

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

noncomputable section
open scoped BigOperators DirectSum Classical

namespace D5.S3.VertexAlgebra.Modules.ActualGroundJointWeights

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open FullJacobiCurrentTransport ActualCurrentTaylor ActualChargedGroundCalculus
open ActualGroundFiniteReconstruction LatticeDiscriminantTheta
open D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock

universe u
variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]
variable (J : FullJacobiLatticeModule D M) (hNil : OriginalPositiveNilpotence J)
variable (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
variable (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))

theorem unitCharge_ne_zero (i : Fin D.rank) : unitCharge D i ≠ 0 := by
  intro h
  have hi := congrFun h i
  simp [unitCharge] at hi

abbrev C (i : Fin D.rank) : Module.End ℂ (Omega J) := Hzero J (unitCharge D i)

theorem C_coe (i : Fin D.rank) (v : Omega J) :
    (C J i v : M) = current J i 0 v.val := by
  simp [C, Hzero_coe, Hcharge, unitCharge]

theorem C_commute (i j : Fin D.rank) : Commute (C J i) (C J j) := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  simp only [Module.End.mul_apply, C_coe]
  exact WeylData.commute_apply _ _ (zero_current_commutes_current J i j 0) v.val

/-- These coordinate spaces are NOT a premise: their internal decomposition
has just been derived from original currents, local nilpotence and Taylor. -/
def coordinateDecomposition (i : Fin D.rank) :
    Omega J ≃ₗ[ℂ] (⨁ a : ℤ, integerEigenspace J (unitCharge D i) a) :=
  (LinearEquiv.ofBijective (DirectSum.coeLinearMap (integerEigenspace J (unitCharge D i)))
    (integer_eigenspaces_internal J hNil H hHG hGH hD (unitCharge D i)
      (unitCharge_ne_zero i))).symm

def coordinate (i : Fin D.rank) (a : ℤ) : Module.End ℂ (Omega J) :=
  (integerEigenspace J (unitCharge D i) a).subtype.comp
    ((DirectSum.component ℂ ℤ (fun a => integerEigenspace J (unitCharge D i) a) a).comp
      (coordinateDecomposition J hNil H hHG hGH hD i).toLinearMap)

theorem coordinate_mem (i : Fin D.rank) (a : ℤ) (v : Omega J) :
    coordinate J hNil H hHG hGH hD i a v ∈ integerEigenspace J (unitCharge D i) a :=
  ((coordinateDecomposition J hNil H hHG hGH hD i v) a).property

theorem coordinate_on_eigenvector (i : Fin D.rank) (a b : ℤ) (v : Omega J)
    (hv : v ∈ integerEigenspace J (unitCharge D i) b) :
    coordinate J hNil H hHG hGH hD i a v = if a = b then v else 0 := by
  classical
  have hi := integer_eigenspaces_internal J hNil H hHG hGH hD
    (unitCharge D i) (unitCharge_ne_zero i)
  by_cases hab : a = b
  · subst a
    rw [if_pos rfl]
    exact congrArg Subtype.val (hi.ofBijective_coeLinearMap_of_mem hv)
  · rw [if_neg hab]
    exact congrArg Subtype.val (hi.ofBijective_coeLinearMap_of_mem_ne (Ne.symm hab) hv)

theorem coordinate_sum (i : Fin D.rank) (v : Omega J) :
    (∑ a ∈ (coordinateDecomposition J hNil H hHG hGH hD i v).support,
      coordinate J hNil H hHG hGH hD i a v) = v := by
  classical
  have h := (coordinateDecomposition J hNil H hHG hGH hD i).symm_apply_apply v
  change DirectSum.coeLinearMap (integerEigenspace J (unitCharge D i))
    (coordinateDecomposition J hNil H hHG hGH hD i v) = v at h
  rw [DirectSum.coeLinearMap_eq_dfinsuppSum] at h
  exact h

/-- Every actual zero-current commutes with the derived finite coordinate
projections; proved on the spanning eigenspaces, not postulated. -/
theorem coordinate_commutes_C (i j : Fin D.rank) (a : ℤ) :
    Commute (C J j) (coordinate J hNil H hHG hGH hD i a) := by
  classical
  let R := coordinate J hNil H hHG hGH hD i a
  let U : Submodule ℂ (Omega J) := LinearMap.ker (C J j * R - R * C J j)
  have hle : (⨆ b : ℤ, integerEigenspace J (unitCharge D i) b) ≤ U := by
    apply iSup_le
    intro b v hv
    have ht : C J j v ∈ integerEigenspace J (unitCharge D i) b := by
      rw [integerEigenspace, Module.End.mem_eigenspace_iff] at hv ⊢
      rw [WeylData.commute_apply _ _ (C_commute J i j) v, hv, map_smul]
    change C J j (R v) - R (C J j v) = 0
    rw [coordinate_on_eigenvector J hNil H hHG hGH hD i a b v hv,
      coordinate_on_eigenvector J hNil H hHG hGH hD i a b (C J j v) ht]
    split_ifs <;> simp
  rw [integer_eigenspaces_span J hNil H hHG hGH hD (unitCharge D i)
    (unitCharge_ne_zero i)] at hle
  apply LinearMap.ext
  intro v
  exact sub_eq_zero.mp (hle (show v ∈ (⊤ : Submodule ℂ (Omega J)) from trivial))

def partialWeight (s : Finset (Fin D.rank)) (b : Charge D) : Submodule ℂ (Omega J) :=
  ⨅ i ∈ s, integerEigenspace J (unitCharge D i) (b i)

def jointWeight (b : Charge D) : Submodule ℂ (Omega J) :=
  ⨅ i, integerEigenspace J (unitCharge D i) (b i)

include hNil H hHG hGH hD in
/-- Finite basis induction. Earlier weights are preserved by the ACTUAL
commuting zero currents; no finite-dimensionality or joint spectrum is assumed.
The empty family is top, so rank zero needs no chosen lattice vector. -/
theorem partial_weights_span (s : Finset (Fin D.rank)) :
    (⨆ b : Charge D, partialWeight J s b) = ⊤ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [partialWeight]
  | @insert i s hi ih =>
    let U : Submodule ℂ (Omega J) := ⨆ b : Charge D, partialWeight J (insert i s) b
    have hle : (⨆ b : Charge D, partialWeight J s b) ≤ U := by
      apply iSup_le
      intro b v hv
      rw [← coordinate_sum J hNil H hHG hGH hD i v]
      apply Submodule.sum_mem
      intro a ha
      apply (le_iSup (partialWeight J (insert i s)) (Function.update b i a))
      simp only [partialWeight, Submodule.mem_iInf] at hv ⊢
      intro j hj
      rcases Finset.mem_insert.mp hj with hji | hjs
      · subst j
        simpa only [Function.update_self] using coordinate_mem J hNil H hHG hGH hD i a v
      · have hji : j ≠ i := fun h => hi (h ▸ hjs)
        rw [Function.update_of_ne hji]
        rw [integerEigenspace, Module.End.mem_eigenspace_iff]
        have he := hv j hjs
        rw [integerEigenspace, Module.End.mem_eigenspace_iff] at he
        rw [WeylData.commute_apply _ _
          (coordinate_commutes_C J hNil H hHG hGH hD i j a) v, he, map_smul]
    rw [ih] at hle
    exact top_unique hle

include hNil H hHG hGH hD in
theorem joint_weights_span : (⨆ b : Charge D, jointWeight J b) = ⊤ := by
  simpa only [partialWeight, jointWeight, Finset.mem_univ, iInf_true] using
    partial_weights_span J hNil H hHG hGH hD (Finset.univ : Finset (Fin D.rank))

/-- Directness is obtained from Mathlib's arbitrary-dimensional independence
of simultaneous generalized eigenspaces, taking ordinary subspaces and
restricting the index injectively to integral weights. -/
theorem joint_weights_independent : iSupIndep (jointWeight J) := by
  have hg := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (C J)
    (fun i j z => Module.End.mapsTo_genEigenspace_of_comm (C_commute J j i) z ⊤)
  have hinj : Function.Injective (fun b : Charge D => fun i => (b i : ℂ)) := by
    intro b c h
    funext i
    exact Int.cast_injective (congrFun h i)
  apply (hg.comp hinj).mono
  intro b
  apply iInf_mono
  intro i
  exact Module.End.eigenspace_le_maxGenEigenspace

include hNil H hHG hGH hD in
/-- Actual joint internal decomposition; its direct-sum carrier enforces
finite support of every vector without bounding multiplicities. -/
theorem joint_weights_internal : DirectSum.IsInternal (jointWeight J) := by
  exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (joint_weights_independent J) (joint_weights_span J hNil H hHG hGH hD)

def jointDecomposition : Omega J ≃ₗ[ℂ] (⨁ b : Charge D, jointWeight J b) :=
  let inverse := Classical.choose (LatticePositiveEnergy.complex_inverse_exists D hD)
  let hleft := (Classical.choose_spec (LatticePositiveEnergy.complex_inverse_exists D hD)).1
  let hright := (Classical.choose_spec (LatticePositiveEnergy.complex_inverse_exists D hD)).2
  (LinearEquiv.ofBijective (DirectSum.coeLinearMap (jointWeight J))
    (joint_weights_internal J hNil inverse hleft hright hD)).symm

include hD in
/-- The physical label is the canonical G^-1 b in the actual rational dual,
and b is literally the existing explicit sector's integral parameter. -/
theorem physical_dual_weight (b α : Charge D) (v : jointWeight J b) :
    Hcharge J α 0 (v.val : M) =
      ((LatticeDualCosetModule.physicalPairing D α (dualVector D b) : ℚ) : ℂ) • (v.val : M) := by
  have hd := Lattice.ActualZhuMinimum.dualVector_hDual D hD b
  rw [LatticeDualCosetModule.physical_pairing_integral D b (dualVector D b) hd α]
  have he (i : Fin D.rank) : current J i 0 (v.val : M) = (b i : ℂ) • (v.val : M) := by
    have hi := ((Submodule.mem_iInf _).mp v.property) i
    rw [integerEigenspace, Module.End.mem_eigenspace_iff] at hi
    simpa only [C_coe, Submodule.coe_smul] using congrArg Subtype.val hi
  simp only [Hcharge, LinearMap.sum_apply, LinearMap.smul_apply, he,
    smul_smul, ← Finset.sum_smul, Int.cast_sum, Int.cast_mul,
    Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast]

end D5.S3.VertexAlgebra.Modules.ActualGroundJointWeights
