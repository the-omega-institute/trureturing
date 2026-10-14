import D5.S3.VertexAlgebra.OriginalCartanCohomology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.OriginalCartanFaithfulness

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeBcGhostBrstCharge
open LatticeBcGhostNeutralCohomology (OriginalCycles OriginalBoundaries OriginalCohomology)
open OriginalBrstReassembly OriginalCartanOperator OriginalCartanCohomology
open TensorConformal.OriginalTopologicalApplications
open TensorConformal.OriginalIntegralBVGerstBracketTransient
open scoped BigOperators TensorProduct

variable (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (leftInverse : H * gramComplex D = 1) (rightInverse : gramComplex D * H = 1)
  (critical : D.rank = 26)

def exceptionalLabelEquiv : OriginalZeroChargeEnergyBasis.FullIndex D ≃ FullLabel D where
  toFun label := ((label.1.1, label.1.2), label.2)
  invFun label := (⟨label.1.1, label.1.2⟩, label.2)
  left_inv label := by rcases label with ⟨⟨charge, powers⟩, ghost⟩; rfl
  right_inv label := rfl

theorem exceptionalBasis_reindex :
    (OriginalZeroChargeEnergyBasis.fullBasis D).reindex (exceptionalLabelEquiv D) = fullBasis D := by
  apply DFunLike.ext
  intro label
  rw [Module.Basis.reindex_apply, OriginalZeroChargeEnergyBasis.fullBasis_apply,
    fullBasis_apply, LatticePositiveEnergy.carrierBasis_apply]
  rfl

include leftInverse rightInverse in
theorem exceptionalSector_eq :
    OriginalZeroChargeEnergyBasis.sector D = zeroSpace D H ⊓ part D (chargeTag D) 0 := by
  ext state
  rw [OriginalZeroChargeEnergyBasis.mem_sector_iff D H leftInverse rightInverse,
    Submodule.mem_inf, mem_part]
  have coefficients (label : OriginalZeroChargeEnergyBasis.FullIndex D) :
      (OriginalZeroChargeEnergyBasis.fullBasis D).repr state label =
        (fullBasis D).repr state (exceptionalLabelEquiv D label) := by
    rw [← exceptionalBasis_reindex, Module.Basis.repr_reindex_apply]
    rfl
  constructor
  · rintro ⟨supported, zeroEnergy⟩
    refine ⟨zeroEnergy, ?_⟩
    intro label different
    have supportedCoordinate := supported ((exceptionalLabelEquiv D).symm label) different
    rw [coefficients] at supportedCoordinate
    simpa only [Equiv.apply_symm_apply] using supportedCoordinate
  · rintro ⟨zeroEnergy, supported⟩
    refine ⟨?_, zeroEnergy⟩
    intro label different
    rw [coefficients]
    exact supported _ different

def cartanSector (coefficients : Fin D.rank → ℂ) : OriginalZeroChargeEnergyBasis.sector D :=
  ⟨cartanState D coefficients, by
    rw [cartanState_apply]
    apply (OriginalZeroChargeEnergyBasis.sector D).neg_mem
    apply (OriginalZeroChargeEnergyBasis.sector D).sum_mem
    intro axis _
    apply (OriginalZeroChargeEnergyBasis.sector D).smul_mem
    rw [currentState_sector]
    exact (OriginalZeroChargeEnergyBasis.sectorBasis D (.inr (axis, false))).property⟩

theorem cartanSector_coe (coefficients : Fin D.rank → ℂ) :
    (cartanSector D coefficients : State D) = cartanState D coefficients := rfl

theorem cartanState_coordinate (coefficients : Fin D.rank → ℂ) (axis : Fin D.rank) :
    (fullBasis D).repr (cartanState D coefficients)
      ((0, Finsupp.single (axis, 0) 1), {1}) = -coefficients axis := by
  let coordinate : State D →ₗ[ℂ] ℂ :=
    (Finsupp.lapply ((0, Finsupp.single (axis, 0) 1), {1})).comp
      (fullBasis D).repr.toLinearMap
  have basisCoordinate (other : Fin D.rank) :
      coordinate (currentState D other) =
        if other = axis then 1 else 0 := by
    have basisState : currentState D other =
        fullBasis D ((0, Finsupp.single (other, 0) 1), {1}) := by
      rw [fullBasis_apply, LatticePositiveEnergy.carrierBasis_apply]
      rfl
    change (fullBasis D).repr (currentState D other)
      ((0, Finsupp.single (axis, 0) 1), {1}) = _
    rw [basisState, Module.Basis.repr_self]
    by_cases same : other = axis
    · subst other
      simp
    · have different : ((0, Finsupp.single (axis, 0) 1), {1}) ≠
          (((0 : Charge D), Finsupp.single (other, 0) 1), ({1} : Finset ℕ)) := by
        intro equality
        have powers := congrArg (fun label : FullLabel D => label.1.2 (axis, 0)) equality
        simp [Finsupp.single_apply, same, Ne.symm same] at powers
      simp [Finsupp.single_apply, different, same]
  have total : (∑ other : Fin D.rank, coefficients other •
      (if other = axis then (1 : ℂ) else 0)) = coefficients axis := by
    calc
      _ = ∑ other : Fin D.rank, if other = axis then coefficients other else 0 := by
        apply Finset.sum_congr rfl
        intro other _
        by_cases same : other = axis <;> simp [same, smul_eq_mul]
      _ = coefficients axis := by simp
  change coordinate (cartanState D coefficients) = -coefficients axis
  calc
    coordinate (cartanState D coefficients) =
        -(∑ other : Fin D.rank, coefficients other • coordinate
          (currentState D other)) := by
      simp only [cartanState_apply, map_neg, map_sum, map_smul]
    _ = -(∑ other : Fin D.rank, coefficients other •
        (if other = axis then (1 : ℂ) else 0)) := by
      simp only [basisCoordinate]
    _ = -coefficients axis := congrArg (fun scalar : ℂ => -scalar) total

include H leftInverse rightInverse in
theorem cartanState_chargeZero (coefficients : Fin D.rank → ℂ) :
    cartanState D coefficients ∈ part D (chargeTag D) 0 := by
  rw [← cartanSector_coe]
  have inclusion : OriginalZeroChargeEnergyBasis.sector D ≤
      zeroSpace D H ⊓ part D (chargeTag D) 0 :=
    (exceptionalSector_eq D H leftInverse rightInverse).le
  exact (inclusion (cartanSector D coefficients).property).2

theorem cartanClass_faithful (coefficients : Fin D.rank → ℂ)
    (zeroClass : cartanClass D H leftInverse rightInverse coefficients = 0) :
    coefficients = 0 := by
  have actualBoundary :
      ((cartanState D).codRestrict (OriginalCycles D H)
        (cartanState_Q D H leftInverse rightInverse)) coefficients ∈ OriginalBoundaries D H := by
    change (OriginalBoundaries D H).mkQ _ = 0 at zeroClass
    rw [← LinearMap.mem_ker, Submodule.ker_mkQ] at zeroClass
    exact zeroClass
  obtain ⟨preimage, equation⟩ := actualBoundary
  obtain ⟨sectorPreimage, sectorEquation⟩ :=
    (zero_charge_full_image D H leftInverse rightInverse 0 (cartanState D coefficients)
      ⟨cartanState_zero D H leftInverse rightInverse coefficients,
        cartanState_chargeZero D H leftInverse rightInverse coefficients⟩).mp ⟨preimage, equation⟩
  let nativePreimage : OriginalZeroChargeEnergyBasis.sector D :=
    ⟨sectorPreimage.val, by
      rw [exceptionalSector_eq D H leftInverse rightInverse]
      exact sectorPreimage.property⟩
  have nativeEquation := congrArg Subtype.val
    (OriginalZeroChargeBrstComplex.differential_formula D nativePreimage)
  rw [OriginalZeroChargeBrstComplex.differential_native D H leftInverse rightInverse] at nativeEquation
  change Q D H sectorPreimage.val = _ at nativeEquation
  rw [sectorEquation] at nativeEquation
  change cartanState D coefficients =
    _ • (OriginalZeroChargeEnergyBasis.sectorBasis D (.inl .pair) : State D) at nativeEquation
  ext axis
  have pairBasis : (OriginalZeroChargeEnergyBasis.sectorBasis D (.inl .pair) : State D) =
      fullBasis D ((0, 0), {1, 5}) := by
    rw [OriginalZeroChargeEnergyBasis.sectorBasis_coe,
      OriginalZeroChargeEnergyBasis.fullBasis_apply,
      fullBasis_apply, LatticePositiveEnergy.carrierBasis_apply]
    rfl
  have coordinate := congrArg (fun state : State D =>
    (fullBasis D).repr state ((0, Finsupp.single (axis, 0) 1), {1})) nativeEquation
  rw [cartanState_coordinate, pairBasis] at coordinate
  simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply] at coordinate
  have different : (((0 : Charge D), Finsupp.single (axis, 0) 1), ({1} : Finset ℕ)) ≠
      ((0, 0), {1, 5}) := by
    intro equality
    have ghosts := congrArg (fun label : FullLabel D => label.2) equality
    exact (by decide : ({1} : Finset ℕ) ≠ {1, 5}) ghosts
  simp only [if_neg different, if_neg (Ne.symm different), smul_zero] at coordinate
  exact neg_eq_zero.mp coordinate

theorem cartanClass_injective : Function.Injective (cartanClass D H leftInverse rightInverse) := by
  intro first second same
  have zeroDifference : cartanClass D H leftInverse rightInverse (first - second) = 0 := by
    rw [map_sub, same, sub_self]
  exact sub_eq_zero.mp (cartanClass_faithful D H leftInverse rightInverse (first - second)
    zeroDifference)

theorem mixedBracket_cartan_cartan (first second : Fin D.rank → ℂ) :
    mixedBracket D H leftInverse rightInverse critical
      (cartanClass D H leftInverse rightInverse first)
      (cartanClass D H leftInverse rightInverse second) = 0 := by
  rw [cartanClass_zeroCycle D H leftInverse rightInverse second,
    mixedBracket_cartan_zeroClass D H leftInverse rightInverse critical first 0
      (cartanZeroCycle D H leftInverse rightInverse second)
      (cartanState_chargeZero D H leftInverse rightInverse second)]
  simp [gramPair, complexCharge]

#print axioms cartanClass_injective
#print axioms mixedBracket_cartan_cartan

end D5.S3.VertexAlgebra.OriginalCartanFaithfulness
