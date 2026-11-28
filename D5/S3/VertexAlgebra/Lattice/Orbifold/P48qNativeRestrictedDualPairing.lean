/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeRestrictedDualPairing
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeRestrictedDualPairing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual twisted eigenspaces give a separating pairing with their restricted dual. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeRestrictedDualField
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeDualLinearField
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Dual.Defs
import OmegaBuild.Commands

/-! The evaluation pairing of the actual P48q restricted dual with the twisted state space. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeRestrictedDualField

open scoped BigOperators Classical DirectSum
open P48qThirdTwistedField (Fock State)
open P48qTwistedChargeAction (Momentum)
open P48qTwistedStateEnergy (totalLZero totalWeight totalLZero_single_monomial)

noncomputable section

local notation "E" => totalLZero.eigenspace

/-- Every state is a finite sum of vectors from actual real energy eigenspaces. -/
theorem actualGrades_iSup_eq_top : (⨆ w : ℝ, E (w : ℂ)) = ⊤ := by
  let S : Submodule ℂ State := ⨆ w : ℝ, E (w : ℂ)
  have single_mem (p : Momentum) (P : Fock) : Finsupp.single p P ∈ S := by
    induction P using MvPolynomial.induction_on' with
    | monomial d c =>
      exact (le_iSup (fun w : ℝ => E (w : ℂ)) (totalWeight p d))
        (Module.End.mem_eigenspace_iff.mpr (totalLZero_single_monomial p d c))
    | add P Q hP hQ =>
      rw [Finsupp.single_add]
      exact S.add_mem hP hQ
  apply top_unique
  intro v _
  change v ∈ S
  rw [← Finsupp.sum_single v]
  change (∑ p ∈ v.support, Finsupp.single p (v p)) ∈ S
  exact S.sum_mem fun p _ => single_mem p (v p)

/-- The real-indexed eigenspaces are an internal direct sum in the twisted carrier. -/
theorem actualGrades_isInternal : DirectSum.IsInternal (fun w : ℝ => E (w : ℂ)) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (totalLZero.eigenspaces_iSupIndep.comp Complex.ofReal_injective) actualGrades_iSup_eq_top

/-- Take the actual energy components of a twisted state. -/
def stateDecompose : State ≃ₗ[ℂ] (⨁ w : ℝ, ActualGrade w) :=
  (LinearEquiv.ofBijective (DirectSum.coeLinearMap (fun w : ℝ => E (w : ℂ)))
    actualGrades_isInternal).symm

/-- Evaluate the finitely supported dual against the corresponding state components. -/
def gradedPairing : RestrictedDual →ₗ[ℂ] State →ₗ[ℂ] ℂ :=
  DirectSum.toModule ℂ ℝ (State →ₗ[ℂ] ℂ) fun w =>
    ((DirectSum.component ℂ ℝ ActualGrade w).comp stateDecompose.toLinearMap).dualMap

@[simp] theorem gradedPairing_lof (w : ℝ) (f : GradeDual w) (v : State) :
    gradedPairing (DirectSum.lof ℂ ℝ GradeDual w f) v = f (stateDecompose v w) := by
  simp only [gradedPairing, DirectSum.toModule_lof, LinearMap.dualMap_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe, ← DirectSum.apply_eq_component]

/-- Against an actual grade, an arbitrary restricted dual evaluates by its component there. -/
theorem gradedPairing_apply_grade (f : RestrictedDual) (w : ℝ) (v : ActualGrade w) :
    gradedPairing f (v : State) = f w v := by
  have hEval : gradedPairing.flip (v : State) =
      (Module.Dual.eval ℂ (ActualGrade w) v).comp (DirectSum.component ℂ ℝ GradeDual w) := by
    apply DirectSum.linearMap_ext
    intro u
    apply LinearMap.ext
    intro g
    simp only [LinearMap.comp_apply, LinearMap.flip_apply, Module.Dual.eval_apply,
      gradedPairing_lof]
    by_cases h : u = w
    · subst u
      have hproj : stateDecompose (v : State) w = v :=
        DirectSum.IsInternal.ofBijective_coeLinearMap_same actualGrades_isInternal v
      rw [hproj, DirectSum.component.lof_self]
    · have hproj : stateDecompose (v : State) u = 0 :=
        DirectSum.IsInternal.ofBijective_coeLinearMap_of_ne actualGrades_isInternal (Ne.symm h) v
      simp only [hproj, map_zero, DirectSum.component.of, dite_eq_right h, LinearMap.zero_apply]
  simpa only [LinearMap.flip_apply, LinearMap.comp_apply, Module.Dual.eval_apply,
    ← DirectSum.apply_eq_component] using DFunLike.congr_fun hEval f

@[simp] theorem gradedPairing_lof_grade (w : ℝ) (f : GradeDual w) (v : ActualGrade w) :
    gradedPairing (DirectSum.lof ℂ ℝ GradeDual w f) (v : State) = f v := by
  rw [gradedPairing_apply_grade _ w v, DirectSum.lof_apply]

theorem gradedPairing_lof_grade_of_ne {u w : ℝ} (h : u ≠ w) (f : GradeDual w)
    (v : ActualGrade u) :
    gradedPairing (DirectSum.lof ℂ ℝ GradeDual w f) (v : State) = 0 := by
  rw [gradedPairing_apply_grade _ u v, DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ h,
    LinearMap.zero_apply]

/-- Testing against all homogeneous states determines the restricted-dual element. -/
theorem gradedPairing_ext {f g : RestrictedDual}
    (h : ∀ (w : ℝ) (v : ActualGrade w),
      gradedPairing f (v : State) = gradedPairing g (v : State)) : f = g := by
  apply DFinsupp.ext
  intro w
  apply LinearMap.ext
  intro v
  simpa only [gradedPairing_apply_grade f w v, gradedPairing_apply_grade g w v] using h w v

/-- The pairing is left separating on the actual restricted dual. -/
theorem gradedPairing_injective : Function.Injective gradedPairing := by
  intro f g h
  apply gradedPairing_ext
  intro w v
  exact DFunLike.congr_fun h (v : State)

end

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeRestrictedDualField

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeRestrictedDualField

open scoped BigOperators Classical DirectSum
open HalfFockSpectralFiberSource (actualInverse)
open LatticeSugawaraCurrents (sugawaraMode)
open P48qAllJetWickField (NativeStates)
open P48qNativeDualCoefficients (bpzTerm bpzTermOnEigenspaces)
open P48qNativeDualLinearField (dualField dualField_homogeneous)
open P48qThirdTwistedField (State)
open P48qTwistedChargeAction (lattice)
open P48qTwistedStateEnergy (totalLZero)

local notation "L₀" => sugawaraMode lattice (actualInverse lattice) 0

/-- A homogeneous dual coefficient is the transpose of the finite BPZ readout
under the actual restricted-dual evaluation pairing. -/
theorem gradedPairing_dualField_coeff (a : NativeStates) (d : ℕ)
    (ha : L₀ a = (d : ℂ) • a) (k : ℤ) (f : RestrictedDual) (v : State) :
    gradedPairing (HVertexOperator.coeff (dualField a) k f) v =
      gradedPairing f ((-1 : ℂ) ^ d •
        ∑ i ∈ Finset.range (d + 1), (i.factorial : ℂ)⁻¹ • bpzTerm a d k i v) := by
  classical
  rw [dualField_homogeneous a d ha, oppositeField_coeff]
  let readout : Module.End ℂ State :=
    (-1 : ℂ) ^ d • ∑ i ∈ Finset.range (d + 1), (i.factorial : ℂ)⁻¹ • bpzTerm a d k i
  suffices h : gradedPairing (coeff a d ha k f) v = gradedPairing f (readout v) by
    simpa only [readout, LinearMap.smul_apply, LinearMap.sum_apply] using h
  have hGrades (w t : ℝ) (g : GradeDual w) (x : ActualGrade (shiftedWeight t d k)) :
      gradedPairing (coeff a d ha k (DirectSum.lof ℂ ℝ GradeDual w g)) (x : State) =
        gradedPairing (DirectSum.lof ℂ ℝ GradeDual w g) (readout (x : State)) := by
    rw [coeff_lof]
    have hx : (shiftedGradeEquiv t d k x).val = (x : State) := by
      unfold shiftedGradeEquiv
      exact LinearEquiv.coe_ofEq_apply _ x
    let term (i : ℕ) : ActualGrade t :=
      bpzTermOnEigenspaces a d ha (t : ℂ) k i (shiftedGradeEquiv t d k x)
    have hTerm (i : ℕ) : (term i : State) = bpzTerm a d k i (x : State) := by
      change bpzTerm a d k i (shiftedGradeEquiv t d k x).val = _
      rw [hx]
    by_cases h : t = w
    · subst t
      rw [gradedPairing_lof_grade (shiftedWeight w d k) (gradeCoeff a d ha w k g) x, gradeCoeff_apply]
      simp only [readout, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum, smul_eq_mul]
      refine congrArg (fun z : ℂ => (-1 : ℂ) ^ d * z) ?_
      apply Finset.sum_congr rfl
      intro i _
      rw [← hTerm i, gradedPairing_lof_grade w g]
    · have hShift : shiftedWeight t d k ≠ shiftedWeight w d k := by
        intro heq
        unfold shiftedWeight at heq
        exact h (add_right_cancel (add_right_cancel heq))
      rw [gradedPairing_lof_grade_of_ne hShift (gradeCoeff a d ha w k g) x]
      have hZero (i : ℕ) :
          gradedPairing (DirectSum.lof ℂ ℝ GradeDual w g) (bpzTerm a d k i (x : State)) = 0 := by
        rw [← hTerm i]
        exact gradedPairing_lof_grade_of_ne h g (term i)
      simp only [readout, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum, smul_eq_mul,
        hZero, mul_zero, Finset.sum_const_zero]
  let assemble := DirectSum.coeLinearMap (fun u : ℝ => totalLZero.eigenspace (u : ℂ))
  have hAssemble : assemble (stateDecompose v) = v :=
    stateDecompose.symm_apply_apply v
  have hGlobal : (gradedPairing.flip v).comp (coeff a d ha k) =
      gradedPairing.flip (readout v) := by
    apply DirectSum.linearMap_ext
    intro w
    apply LinearMap.ext
    intro g
    let F := DirectSum.lof ℂ ℝ GradeDual w g
    change gradedPairing (coeff a d ha k F) v = gradedPairing F (readout v)
    have hState : (gradedPairing (coeff a d ha k F)).comp assemble =
        ((gradedPairing F).comp readout).comp assemble := by
      apply DirectSum.linearMap_ext
      intro u
      apply LinearMap.ext
      intro x
      simp only [LinearMap.comp_apply, assemble, DirectSum.coeLinearMap_lof]
      let t : ℝ := u - (d : ℝ) - (k : ℝ) / 3
      have ht : shiftedWeight t d k = u := by
        dsimp only [t, shiftedWeight]
        ring
      let y : ActualGrade (shiftedWeight t d k) := ⟨x.val, by
        rw [ht]
        exact x.property⟩
      exact hGrades w t g y
    simpa only [LinearMap.comp_apply, hAssemble] using
      LinearMap.congr_fun hState (stateDecompose v)
  simpa only [LinearMap.comp_apply, LinearMap.flip_apply] using LinearMap.congr_fun hGlobal f

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeRestrictedDualField
