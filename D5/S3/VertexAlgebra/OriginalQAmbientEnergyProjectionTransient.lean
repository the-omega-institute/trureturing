import D5.S3.VertexAlgebra.OriginalQActualQuotientTransferTransient
import D5.S3.VertexAlgebra.LatticeBcGhostCohomologyReassembly

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.OriginalQQuartetSource

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeBcGhostBrstCharge
  BcGhostFockSupport OriginalBrstReassembly
open scoped BigOperators TensorProduct

noncomputable section

def ambientEnergyTag (D : LatticeData) (label : FullLabel D) : Charge D × ℂ :=
  (label.1.1, (totalEnergy D label : ℂ))

def ambientEnergyProjection (D : LatticeData) (beta : Charge D) (level : ℤ) :
    Module.End ℂ (State D) :=
  projection D (ambientEnergyTag D) (beta, chosenH D beta + (level : ℂ) - 1)

theorem original_charge_projection_basis (D : LatticeData) (beta : Charge D)
    (label : FullLabel D) :
    chargeProjection D beta (fullBasis D label) =
      if label.1.1 = beta then fullBasis D label else 0 := by
  rw [fullBasis_apply, LatticePositiveEnergy.carrierBasis_apply,
    (terminationSupplier "chargeProjection_tmul")]
  by_cases same : label.1.1 = beta
  · subst beta
    rw [Finsupp.single_eq_same, if_pos rfl]
  · rw [Finsupp.single_eq_of_ne (Ne.symm same), Finsupp.single_zero, TensorProduct.zero_tmul,
      if_neg same]

theorem original_charge_projection_partition (D : LatticeData) (beta : Charge D) :
    chargeProjection D beta = projection D (chargeTag D) beta := by
  apply (fullBasis D).ext
  intro label
  rw [original_charge_projection_basis]
  by_cases same : chargeTag D label = beta
  · change label.1.1 = beta at same
    rw [if_pos same]
    exact (projection_fixed D (chargeTag D) beta
      (same ▸ basis_mem_part D (chargeTag D) label)).symm
  · change label.1.1 ≠ beta at same
    rw [if_neg same]
    exact (projection_other D (chargeTag D) beta (chargeTag D label) same
      (basis_mem_part D (chargeTag D) label)).symm

variable (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
  (leftGramInverse : H * gramComplex D = 1) (rightGramInverse : gramComplex D * H = 1)
  (beta : Charge D) (level : ℤ)

include leftGramInverse rightGramInverse in
theorem original_energy_sector_partition :
    originalEnergySector D H beta level =
      part D (ambientEnergyTag D) (beta, chosenH D beta + (level : ℂ) - 1) := by
  classical
  ext state
  change (chargeProjection D beta state = state ∧
    (M D H 0 + G D 0) state = (chosenH D beta + (level : ℂ) - 1) • state) ↔ _
  rw [mem_part]
  constructor
  · rintro ⟨chargeLaw, energyLaw⟩ label outside
    by_cases chargeEqual : label.1.1 = beta
    · have energyDifferent : (totalEnergy D label : ℂ) ≠ chosenH D beta + (level : ℂ) - 1 := by
        intro equality
        exact outside (Prod.ext chargeEqual equality)
      have coefficients := congrArg (fun input : State D => (fullBasis D).repr input label) energyLaw
      rw [totalZero_coeff D H leftGramInverse rightGramInverse] at coefficients
      simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at coefficients
      have cancelled : ((totalEnergy D label : ℂ) - (chosenH D beta + (level : ℂ) - 1)) *
          (fullBasis D).repr state label = 0 := by
        rw [sub_mul, coefficients, sub_self]
      exact (mul_eq_zero.mp cancelled).resolve_left (sub_ne_zero.mpr energyDifferent)
    · have coefficients := congrArg (fun input : State D => (fullBasis D).repr input label) chargeLaw
      rw [original_charge_projection_partition, projection_coeff] at coefficients
      simp only [chargeTag, if_neg chargeEqual] at coefficients
      exact coefficients.symm
  · intro supported
    constructor
    · apply (fullBasis D).repr.injective
      ext label
      rw [original_charge_projection_partition, projection_coeff]
      simp only [chargeTag]
      by_cases same : label.1.1 = beta
      · rw [if_pos same]
      · rw [if_neg same, supported label (by
          intro equality
          exact same (congrArg Prod.fst equality))]
    · apply (fullBasis D).repr.injective
      ext label
      rw [totalZero_coeff D H leftGramInverse rightGramInverse]
      simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
      by_cases same : ambientEnergyTag D label = (beta, chosenH D beta + (level : ℂ) - 1)
      · rw [show (totalEnergy D label : ℂ) = chosenH D beta + (level : ℂ) - 1 from
          congrArg Prod.snd same]
      · rw [supported label same, mul_zero, mul_zero]

include leftGramInverse rightGramInverse in
theorem ambient_energy_projection_mem (state : State D) :
    ambientEnergyProjection D beta level state ∈ originalEnergySector D H beta level := by
  rw [original_energy_sector_partition D H leftGramInverse rightGramInverse]
  exact projection_mem D (ambientEnergyTag D) _ state

include leftGramInverse rightGramInverse in
theorem ambient_energy_projection_fixed {state : State D}
    (member : state ∈ originalEnergySector D H beta level) :
    ambientEnergyProjection D beta level state = state := by
  rw [original_energy_sector_partition D H leftGramInverse rightGramInverse] at member
  exact projection_fixed D (ambientEnergyTag D) _ member

include leftGramInverse rightGramInverse in
theorem ambient_energy_projection_range :
    LinearMap.range (ambientEnergyProjection D beta level) = originalEnergySector D H beta level := by
  ext state
  constructor
  · rintro ⟨preimage, rfl⟩
    exact ambient_energy_projection_mem D H leftGramInverse rightGramInverse beta level preimage
  · intro member
    exact ⟨state, ambient_energy_projection_fixed D H leftGramInverse rightGramInverse beta level member⟩

theorem ambient_energy_projection_idempotent :
    ambientEnergyProjection D beta level * ambientEnergyProjection D beta level =
      ambientEnergyProjection D beta level := by
  change (projection D (ambientEnergyTag D) (beta, chosenH D beta + (level : ℂ) - 1)).comp
    (projection D (ambientEnergyTag D) (beta, chosenH D beta + (level : ℂ) - 1)) = _
  have result := projection_orthogonal D (ambientEnergyTag D)
    (beta, chosenH D beta + (level : ℂ) - 1) (beta, chosenH D beta + (level : ℂ) - 1)
  rw [if_pos rfl] at result
  exact result

include leftGramInverse rightGramInverse in
theorem ambient_energy_projection_Q :
    (ambientEnergyProjection D beta level).comp (Q D H) =
      (Q D H).comp (ambientEnergyProjection D beta level) := by
  apply projection_commutes
  intro input output different
  by_contra nonzero
  obtain ⟨chargeEqual, energyEqual⟩ := Q_coefficient_blocks D H leftGramInverse rightGramInverse
    input output nonzero
  exact different (Prod.ext chargeEqual (congrArg (fun energy : ℤ => (energy : ℂ)) energyEqual))

def ambientEnergyToSector : State D →ₗ[ℂ] originalEnergySector D H beta level :=
  (ambientEnergyProjection D beta level).codRestrict (originalEnergySector D H beta level)
    (ambient_energy_projection_mem D H leftGramInverse rightGramInverse beta level)

theorem ambient_boundary_sector_preimage (state : originalEnergySector D H beta level) :
    (∃ preimage : State D, Q D H preimage = state.val) ↔
      ∃ preimage : originalEnergySector D H beta level,
        energyOriginalQ D H leftGramInverse rightGramInverse beta level preimage = state := by
  constructor
  · rintro ⟨preimage, equality⟩
    refine ⟨ambientEnergyToSector D H leftGramInverse rightGramInverse beta level preimage, ?_⟩
    apply Subtype.ext
    change Q D H (ambientEnergyProjection D beta level preimage) = state.val
    have commutes := LinearMap.congr_fun
      (ambient_energy_projection_Q D H leftGramInverse rightGramInverse beta level) preimage
    simp only [LinearMap.comp_apply] at commutes
    rw [← commutes, equality]
    exact ambient_energy_projection_fixed D H leftGramInverse rightGramInverse beta level state.property
  · rintro ⟨preimage, equality⟩
    exact ⟨preimage.val, congrArg Subtype.val equality⟩

#print axioms original_energy_sector_partition
#print axioms ambient_energy_projection_Q
#print axioms ambient_boundary_sector_preimage

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource
