/- GID: D5/S3/VertexAlgebra/OriginalZeroChargeBrstCohomology
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/OriginalZeroChargeBrstCohomology
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Explicit representatives and inverse coordinates for the actual exceptional quotient. -/

import D5.S3.VertexAlgebra.OriginalZeroChargeBrstComplex

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.OriginalZeroChargeBrstCohomology

open LatticeGeneratingFieldLocality LatticeBcGhostBrstCharge
  OriginalZeroChargeEnergyBasis OriginalZeroChargeBrstComplex

noncomputable section

def survivingLabels (D : LatticeData) : Set (BasisIndex D) :=
  {index | index ≠ .inl .zeroMode ∧ index ≠ .inl .pair}

def quotientCoordinates (D : LatticeData) :
    cycles D →ₗ[ℂ] (survivingLabels D →₀ ℂ) :=
  (Finsupp.lsubtypeDomain (survivingLabels D)).comp
    ((sectorBasis D).repr.toLinearMap.comp (cycles D).subtype)

def representativeState (D : LatticeData) :
    (survivingLabels D →₀ ℂ) →ₗ[ℂ] sector D :=
  (sectorBasis D).repr.symm.toLinearMap.comp (Finsupp.lmapDomain ℂ ℂ Subtype.val)

private theorem representative_cycle (D : LatticeData) (coefficients : survivingLabels D →₀ ℂ) :
    representativeState D coefficients ∈ cycles D := by
  rw [cycles_iff]
  change (sectorBasis D).repr ((sectorBasis D).repr.symm
    (Finsupp.mapDomain Subtype.val coefficients)) (.inl .zeroMode) = 0
  rw [LinearEquiv.apply_symm_apply]
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨index, equal⟩
  exact index.2.1 equal

def representative (D : LatticeData) :
    (survivingLabels D →₀ ℂ) →ₗ[ℂ] cycles D :=
  (representativeState D).codRestrict (cycles D) (representative_cycle D)

theorem coordinates_representative (D : LatticeData) (coefficients : survivingLabels D →₀ ℂ) :
    quotientCoordinates D (representative D coefficients) = coefficients := by
  ext index
  change (sectorBasis D).repr ((sectorBasis D).repr.symm
    (Finsupp.mapDomain Subtype.val coefficients)) index.1 = coefficients index
  rw [LinearEquiv.apply_symm_apply]
  exact Finsupp.mapDomain_apply Subtype.val_injective coefficients index

theorem quotientCoordinates_surjective (D : LatticeData) :
    Function.Surjective (quotientCoordinates D) :=
  fun coefficients => ⟨representative D coefficients, coordinates_representative D coefficients⟩

theorem quotientCoordinates_kernel (D : LatticeData) :
    LinearMap.ker (quotientCoordinates D) = (boundaries D).comap (cycles D).subtype := by
  classical
  ext state
  change quotientCoordinates D state = 0 ↔ (state : sector D) ∈ boundaries D
  rw [boundaries_eq_span]
  constructor
  · intro zeroCoordinates
    have stateEquation : (state : sector D) =
        (sectorBasis D).repr (state : sector D) (.inl .pair) • sectorBasis D (.inl .pair) := by
      apply (sectorBasis D).repr.injective
      ext index
      by_cases pair : index = .inl .pair
      · subst index
        simp
      by_cases zeroMode : index = .inl .zeroMode
      · subst index
        simp [(cycles_iff D _).mp state.2]
      · have coefficient := congrArg
          (fun values : survivingLabels D →₀ ℂ => values ⟨index, zeroMode, pair⟩) zeroCoordinates
        change (sectorBasis D).repr (state : sector D) index = 0 at coefficient
        simp [coefficient, pair]
    rw [stateEquation]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · intro boundary
    obtain ⟨scalar, equation⟩ := Submodule.mem_span_singleton.mp boundary
    ext index
    change (sectorBasis D).repr (state : sector D) index.1 = 0
    rw [← equation]
    simp [index.2.2]

def cohomologyCoordinates (D : LatticeData) :
    Cohomology D ≃ₗ[ℂ] (survivingLabels D →₀ ℂ) :=
  (Submodule.quotEquivOfEq _ _ (quotientCoordinates_kernel D).symm).trans
    ((quotientCoordinates D).quotKerEquivOfSurjective (quotientCoordinates_surjective D))

def cohomologyBasis (D : LatticeData) :
    Module.Basis (survivingLabels D) ℂ (Cohomology D) :=
  Module.Basis.ofRepr (cohomologyCoordinates D)

#print axioms quotientCoordinates_kernel
#print axioms cohomologyCoordinates

end
end D5.S3.VertexAlgebra.OriginalZeroChargeBrstCohomology
