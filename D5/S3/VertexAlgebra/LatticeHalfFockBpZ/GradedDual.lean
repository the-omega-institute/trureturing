/- GID: D5/S3/VertexAlgebra/LatticeHalfFockBpZ/GradedDual
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockBpZ/GradedDual
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original odd Leech W is bilinearly isomorphic to its genuine restricted graded dual. -/

import D5.S3.VertexAlgebra.LatticeHalfFockBpZ.Finiteness

set_option autoImplicit false
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 4000000

namespace D5.S3.VertexAlgebra.LatticeHalfFockBpZ

open LatticeGeneratingFieldLocality LatticeHalfFock LatticeHalfFockNativeSpectrum
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockIntegralOddFixedSector
open GolayLeech.ExplicitLeechLattice TwistedGround.NativeHyperbolicActions
open scoped DirectSum

noncomputable section

abbrev WComponents (spectrum : LeechNativeSpectrum) :=
  ⨁ value : ℤ, integralSector spectrum value

abbrev WRestrictedDual (spectrum : LeechNativeSpectrum) :=
  ⨁ value : ℤ, Module.Dual ℂ (integralSector spectrum value)

private def sectorEigenEquiv (spectrum : LeechNativeSpectrum) (value : ℤ) :
    integralSector spectrum value ≃ₗ[ℂ]
      eigenspace LeechData spectrum.native spectrum.inverse (value : ℂ) :=
  LinearEquiv.ofEq _ _ (integralSector_eq_native_eigenspace spectrum value)

def wAssemblyEquiv (spectrum : LeechNativeSpectrum) : WComponents spectrum ≃ₗ[ℂ] NativeW :=
  (DirectSum.congrLinearEquiv (sectorEigenEquiv spectrum)).trans
    (integerDirectSumEquiv LeechData spectrum.native spectrum.inverse
      spectrum.leftInverse spectrum.rightInverse spectrum.rank24)

private theorem w_assembly_single (spectrum : LeechNativeSpectrum) (value : ℤ)
    (state : integralSector spectrum value) :
    (wAssemblyEquiv spectrum
      (DirectSum.of (fun value : ℤ => integralSector spectrum value) value state)).val =
        state.val := by
  change integerAssembly LeechData spectrum.native spectrum.inverse
    (DirectSum.lmap (fun value : ℤ => (sectorEigenEquiv spectrum value).toLinearMap)
      (DirectSum.of (fun value : ℤ => integralSector spectrum value) value state)) = state.val
  rw [DirectSum.lmap_of, integerAssembly, DirectSum.coeLinearMap_of]
  rfl

private def nativeSectorVector (spectrum : LeechNativeSpectrum) (value : ℤ) :
    integralSector spectrum value →ₗ[ℂ] NativeTensor where
  toFun state := state.val
  map_add' first second := rfl
  map_smul' scalar state := rfl

theorem w_assembly_pairing (spectrum : LeechNativeSpectrum) (components : WComponents spectrum)
    (value : ℤ) (state : integralSector spectrum value) :
    tensorPairing (wAssemblyEquiv spectrum components).val (nativeSectorVector spectrum value state) =
      tensorPairing (nativeSectorVector spectrum value (components value))
        (nativeSectorVector spectrum value state) := by
  classical
  induction components using DirectSum.induction_on with
  | zero =>
    simp only [map_zero, Submodule.coe_zero, DirectSum.zero_apply, LinearMap.zero_apply]
  | add first second firstProof secondProof =>
    simp only [map_add, Submodule.coe_add, DirectSum.add_apply,
      LinearMap.add_apply, firstProof, secondProof]
  | of selected component =>
    have single := w_assembly_single spectrum selected component
    change (wAssemblyEquiv spectrum
      (DirectSum.of (fun value : ℤ => integralSector spectrum value) selected component)).val =
      nativeSectorVector spectrum selected component at single
    rw [single]
    by_cases same : selected = value
    · subst selected
      simp only [DirectSum.of_eq_same]
    · have sourceEigen : nativeSectorVector spectrum selected component ∈
          eigenspace data determinantUnit spectrum.inverse (selected : ℂ) := by
        change component.val ∈ eigenspace LeechData spectrum.native spectrum.inverse
          (selected : ℂ)
        rw [← integralSector_eq_native_eigenspace spectrum selected]
        exact component.property
      have targetEigen : nativeSectorVector spectrum value state ∈
          eigenspace data determinantUnit spectrum.inverse
          (value : ℂ) := by
        change state.val ∈ eigenspace LeechData spectrum.native spectrum.inverse (value : ℂ)
        rw [← integralSector_eq_native_eigenspace spectrum value]
        exact state.property
      have orthogonal := native_grade_orthogonal spectrum.inverse
        (selected : ℂ) (value : ℂ) (by exact_mod_cast same)
        (nativeSectorVector spectrum selected component) (nativeSectorVector spectrum value state)
        sourceEigen targetEigen
      rw [orthogonal]
      have zeroCoordinate :
          (DirectSum.of (fun value : ℤ => integralSector spectrum value) selected component)
            value = 0 := DirectSum.of_eq_of_ne
              (β := fun value : ℤ => ↥(integralSector spectrum value))
              selected value component (Ne.symm same)
      rw [zeroCoordinate]
      simp only [map_zero, LinearMap.zero_apply]

def gradedWSelfDuality (spectrum : LeechNativeSpectrum) :
    NativeW ≃ₗ[ℂ] WRestrictedDual spectrum :=
  (wAssemblyEquiv spectrum).symm.trans
    (DirectSum.congrLinearEquiv (integralSelfDuality spectrum))

theorem graded_w_self_duality_evaluation (spectrum : LeechNativeSpectrum)
    (state : NativeW) (value : ℤ) (test : integralSector spectrum value) :
    gradedWSelfDuality spectrum state value test = tensorPairing state.val test.val := by
  change integralSelfDuality spectrum value
    (((wAssemblyEquiv spectrum).symm state) value) test = _
  rw [integral_self_duality_apply]
  have equation := w_assembly_pairing spectrum ((wAssemblyEquiv spectrum).symm state) value test
  rw [LinearEquiv.apply_symm_apply] at equation
  exact equation.symm

#print axioms tensor_pairing_nondegenerate
#print axioms oscillator_current_adjoint
#print axioms tensor_stress_adjoint
#print axioms w_pairing_nondegenerate
#print axioms native_grade_finite
#print axioms integral_pairing_nondegenerate
#print axioms graded_w_self_duality_evaluation

end
end D5.S3.VertexAlgebra.LatticeHalfFockBpZ
