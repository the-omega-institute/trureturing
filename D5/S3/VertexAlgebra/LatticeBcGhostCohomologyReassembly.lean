import D5.S3.VertexAlgebra.LatticeBcGhostCohomologyDirectSum

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.OriginalBrstReassembly

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeBcGhostBrstCharge
open scoped BigOperators DirectSum Classical

noncomputable section

variable (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)

def zeroSpace : Submodule ℂ (State D) := LinearMap.ker (M D H 0 + G D 0)

def relativeSpace : Submodule ℂ (State D) := zeroSpace D H ⊓ LinearMap.ker (B D 0)

theorem top_stable (state : State D) (_member : state ∈ (⊤ : Submodule ℂ (State D))) :
    Q D H state ∈ (⊤ : Submodule ℂ (State D)) := Submodule.mem_top

variable (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)

include hHG hGH in
theorem zero_stable (state : State D) (member : state ∈ zeroSpace D H) :
    Q D H state ∈ zeroSpace D H := by
  have equality := LinearMap.congr_fun (totalZero_commutes D H hHG hGH) state
  change (M D H 0 + G D 0) (Q D H state) = Q D H ((M D H 0 + G D 0) state)
    at equality
  rw [member, map_zero] at equality
  exact equality

include hHG hGH in
theorem relative_stable (state : State D) (member : state ∈ relativeSpace D H) :
    Q D H state ∈ relativeSpace D H := by
  refine ⟨zero_stable D H hHG hGH state member.1, ?_⟩
  have equality := LinearMap.congr_fun (ward_identity D H 0) state
  change Q D H (B D 0 state) + B D 0 (Q D H state) =
    (M D H 0 + G D 0) state at equality
  rw [member.2, map_zero, zero_add, member.1] at equality
  exact equality

include hHG hGH in
theorem zero_projected {Index : Type*} (tag : FullLabel D → Index)
    (index : Index) (state : State D) (member : state ∈ zeroSpace D H) :
    projection D tag index state ∈ zeroSpace D H := by
  have equality := LinearMap.congr_fun (projection_T0 D tag H hHG hGH index) state
  change projection D tag index ((M D H 0 + G D 0) state) =
    (M D H 0 + G D 0) (projection D tag index state) at equality
  rw [member, map_zero] at equality
  exact equality.symm

include hHG hGH in
theorem relative_projected (charge : Charge D) (state : State D)
    (member : state ∈ relativeSpace D H) :
    projection D (chargeTag D) charge state ∈ relativeSpace D H := by
  refine ⟨zero_projected D H hHG hGH (chargeTag D) charge state member.1, ?_⟩
  have equality := LinearMap.congr_fun (chargeProjection_B D charge) state
  change projection D (chargeTag D) charge (B D 0 state) =
    B D 0 (projection D (chargeTag D) charge state) at equality
  rw [member.2, map_zero] at equality
  exact equality.symm

include hHG hGH in
theorem P0_mem (state : State D) : P0 D state ∈ zeroSpace D H := by
  exact LinearMap.congr_fun (totalZero_P0 D H hHG hGH) state

include hHG hGH in
theorem P0_fixed {state : State D} (member : state ∈ zeroSpace D H) : P0 D state = state := by
  apply (fullBasis D).repr.injective
  ext label
  change (fullBasis D).repr
    (energyWeight D (fun energy => if energy = 0 then 1 else 0) state) label = _
  rw [energyWeight_coeff]
  by_cases zeroEnergy : totalEnergy D label = 0
  · simp [zeroEnergy]
  · rw [if_neg zeroEnergy, zero_mul]
    have vanished := congrArg (fun vector => (fullBasis D).repr vector label) member
    rw [totalZero_coeff D H hHG hGH] at vanished
    change (totalEnergy D label : ℂ) * (fullBasis D).repr state label = 0 at vanished
    exact ((mul_eq_zero.mp vanished).resolve_left (Int.cast_ne_zero.mpr zeroEnergy)).symm

include hHG hGH in
theorem P0_Q : (P0 D).comp (Q D H) = (Q D H).comp (P0 D) :=
  energyWeight_commutes D H hHG hGH (fun energy => if energy = 0 then 1 else 0)

variable (hcritical : D.rank = 26)

abbrev absoluteCohomology :=
  Cohomology D H hHG hGH hcritical ⊤ (top_stable D H)

abbrev zeroCohomology :=
  Cohomology D H hHG hGH hcritical (zeroSpace D H) (zero_stable D H hHG hGH)

abbrev relativeCohomology :=
  Cohomology D H hHG hGH hcritical (relativeSpace D H) (relative_stable D H hHG hGH)

abbrev jointCohomology (index : Charge D × ℤ) :=
  sectorCohomology D H hHG hGH hcritical (jointTag D) ⊤ (top_stable D H)
    (jointProjection_Q D H hHG hGH) index

abbrev zeroChargeCohomology (charge : Charge D) :=
  sectorCohomology D H hHG hGH hcritical (chargeTag D) (zeroSpace D H)
    (zero_stable D H hHG hGH) (chargeProjection_Q D H) charge

abbrev relativeChargeCohomology (charge : Charge D) :=
  sectorCohomology D H hHG hGH hcritical (chargeTag D) (relativeSpace D H)
    (relative_stable D H hHG hGH) (chargeProjection_Q D H) charge

def absoluteJointEquiv : absoluteCohomology D H hHG hGH hcritical ≃ₗ[ℂ]
    ⨁ index : Charge D × ℤ, jointCohomology D H hHG hGH hcritical index :=
  cohomologyReassembly D H hHG hGH hcritical (jointTag D) ⊤ (top_stable D H)
    (fun _ _ _ => Submodule.mem_top) (jointProjection_Q D H hHG hGH)

include hHG hGH in
theorem full_image_iff_finite_boundaries (state : State D) :
    (∃ preimage : State D, Q D H preimage = state) ↔
    ∀ index : Charge D × ℤ, ∃ preimage : part D (jointTag D) index,
      Q D H preimage.val = projection D (jointTag D) index state := by
  have comparison := original_image_iff_sector_images D H (jointTag D)
    (⊤ : Submodule ℂ (State D)) (fun _ _ _ => Submodule.mem_top)
    (jointProjection_Q D H hHG hGH) ⟨state, Submodule.mem_top⟩
  constructor
  · rintro ⟨preimage, equation⟩ index
    obtain ⟨sectorPreimage, sectorEquation⟩ := comparison.mp
      ⟨⟨preimage, Submodule.mem_top⟩, equation⟩ index
    exact ⟨⟨sectorPreimage.val, sectorPreimage.property.2⟩, sectorEquation⟩
  · intro sectorPreimages
    obtain ⟨preimage, equation⟩ := comparison.mpr (fun index => by
      obtain ⟨sectorPreimage, sectorEquation⟩ := sectorPreimages index
      exact ⟨⟨sectorPreimage.val, Submodule.mem_top, sectorPreimage.property⟩, sectorEquation⟩)
    exact ⟨preimage.val, equation⟩

def zeroReduction : absoluteCohomology D H hHG hGH hcritical →ₗ[ℂ]
    zeroCohomology D H hHG hGH hcritical :=
  homologyMap D H hHG hGH hcritical ⊤ (zeroSpace D H) (top_stable D H)
    (zero_stable D H hHG hGH) (P0 D) (fun state _ => P0_mem D H hHG hGH state)
    (P0_Q D H hHG hGH)

def zeroInclude : zeroCohomology D H hHG hGH hcritical →ₗ[ℂ]
    absoluteCohomology D H hHG hGH hcritical :=
  homologyMap D H hHG hGH hcritical (zeroSpace D H) ⊤ (zero_stable D H hHG hGH)
    (top_stable D H) LinearMap.id (fun _ _ => Submodule.mem_top) (by simp)

theorem zeroInclude_reduction (state : absoluteCohomology D H hHG hGH hcritical) :
    zeroInclude D H hHG hGH hcritical (zeroReduction D H hHG hGH hcritical state) = state := by
  obtain ⟨representative, rfl⟩ :=
    (boundaries D H hHG hGH hcritical ⊤ (top_stable D H)).mkQ_surjective state
  change (boundaries D H hHG hGH hcritical ⊤ (top_stable D H)).mkQ
    ⟨P0 D representative.val, Submodule.mem_top,
      (cyclesMap D H ⊤ (zeroSpace D H) (P0 D)
        (fun state _ => P0_mem D H hHG hGH state) (P0_Q D H hHG hGH)
          representative).property.2⟩ =
    (boundaries D H hHG hGH hcritical ⊤ (top_stable D H)).mkQ representative
  apply (Submodule.Quotient.eq _).mpr
  apply (boundary_iff D H hHG hGH hcritical ⊤ (top_stable D H) _).mpr
  refine ⟨⟨P0 D (h D representative.val) - h D representative.val, Submodule.mem_top⟩, ?_⟩
  obtain ⟨zeroRepresentative, zeroMember, _zeroCycle, difference⟩ :=
    cycle_to_zero D H hHG hGH representative.val representative.property.2
  change representative.val - zeroRepresentative = Q D H (h D representative.val)
    at difference
  have filtered := congrArg (P0 D) difference
  rw [map_sub, P0_fixed D H hHG hGH zeroMember] at filtered
  have blocked := LinearMap.congr_fun (P0_Q D H hHG hGH) (h D representative.val)
  change P0 D (Q D H (h D representative.val)) =
    Q D H (P0 D (h D representative.val)) at blocked
  rw [blocked] at filtered
  change Q D H (P0 D (h D representative.val) - h D representative.val) =
    P0 D representative.val - representative.val
  rw [map_sub, ← filtered, ← difference]
  abel

theorem zeroReduction_include (state : zeroCohomology D H hHG hGH hcritical) :
    zeroReduction D H hHG hGH hcritical (zeroInclude D H hHG hGH hcritical state) = state := by
  obtain ⟨representative, rfl⟩ :=
    (boundaries D H hHG hGH hcritical (zeroSpace D H)
      (zero_stable D H hHG hGH)).mkQ_surjective state
  change (boundaries D H hHG hGH hcritical (zeroSpace D H)
    (zero_stable D H hHG hGH)).mkQ
      (cyclesMap D H ⊤ (zeroSpace D H) (P0 D)
        (fun state _ => P0_mem D H hHG hGH state) (P0_Q D H hHG hGH)
        (cyclesMap D H (zeroSpace D H) ⊤ LinearMap.id
          (fun _ _ => Submodule.mem_top) (by simp) representative)) =
    (boundaries D H hHG hGH hcritical (zeroSpace D H)
      (zero_stable D H hHG hGH)).mkQ representative
  congr 1
  apply Subtype.ext
  exact P0_fixed D H hHG hGH representative.property.1

def zeroReductionEquiv : absoluteCohomology D H hHG hGH hcritical ≃ₗ[ℂ]
    zeroCohomology D H hHG hGH hcritical :=
  { zeroReduction D H hHG hGH hcritical with
    invFun := zeroInclude D H hHG hGH hcritical
    left_inv := zeroInclude_reduction D H hHG hGH hcritical
    right_inv := zeroReduction_include D H hHG hGH hcritical }

def absoluteZeroChargeEquiv : absoluteCohomology D H hHG hGH hcritical ≃ₗ[ℂ]
    ⨁ charge : Charge D, zeroChargeCohomology D H hHG hGH hcritical charge :=
  (zeroReductionEquiv D H hHG hGH hcritical).trans
    (cohomologyReassembly D H hHG hGH hcritical (chargeTag D) (zeroSpace D H)
      (zero_stable D H hHG hGH) (zero_projected D H hHG hGH (chargeTag D))
      (chargeProjection_Q D H))

def relativeChargeEquiv : relativeCohomology D H hHG hGH hcritical ≃ₗ[ℂ]
    ⨁ charge : Charge D, relativeChargeCohomology D H hHG hGH hcritical charge :=
  cohomologyReassembly D H hHG hGH hcritical (chargeTag D) (relativeSpace D H)
    (relative_stable D H hHG hGH) (relative_projected D H hHG hGH)
    (chargeProjection_Q D H)

include hHG hGH in
theorem zero_charge_full_image (charge : Charge D) (state : State D)
    (member : state ∈ zeroSpace D H ⊓ part D (chargeTag D) charge) :
    (∃ preimage : State D, Q D H preimage = state) ↔
      ∃ preimage : ↥(zeroSpace D H ⊓ part D (chargeTag D) charge),
        Q D H preimage.val = state := by
  constructor
  · rintro ⟨preimage, equation⟩
    refine ⟨⟨projection D (chargeTag D) charge (P0 D preimage),
      zero_projected D H hHG hGH (chargeTag D) charge _ (P0_mem D H hHG hGH preimage),
      projection_mem D (chargeTag D) charge _⟩, ?_⟩
    have chargeEquation := LinearMap.congr_fun (chargeProjection_Q D H charge) (P0 D preimage)
    have energyEquation := LinearMap.congr_fun (P0_Q D H hHG hGH) preimage
    change projection D (chargeTag D) charge (Q D H (P0 D preimage)) =
      Q D H (projection D (chargeTag D) charge (P0 D preimage)) at chargeEquation
    change P0 D (Q D H preimage) = Q D H (P0 D preimage) at energyEquation
    rw [← chargeEquation, ← energyEquation, equation, P0_fixed D H hHG hGH member.1,
      projection_fixed D (chargeTag D) charge member.2]
  · rintro ⟨preimage, equation⟩
    exact ⟨preimage.val, equation⟩

include hHG hGH in
theorem relative_image_iff_finite_boundaries (state : relativeSpace D H) :
    (∃ preimage : relativeSpace D H, Q D H preimage.val = state.val) ↔
      ∀ charge : Charge D,
        ∃ preimage : ↥(relativeSpace D H ⊓ part D (chargeTag D) charge),
          Q D H preimage.val = projection D (chargeTag D) charge state.val :=
  original_image_iff_sector_images D H (chargeTag D) (relativeSpace D H)
    (relative_projected D H hHG hGH) (chargeProjection_Q D H) state

theorem joint_nonzero_P0 (index : Charge D × ℤ) (nonzero : index.2 ≠ 0)
    (state : State D) (member : state ∈ part D (jointTag D) index) : P0 D state = 0 := by
  apply (fullBasis D).repr.injective
  ext label
  change (fullBasis D).repr
    (energyWeight D (fun energy => if energy = 0 then 1 else 0) state) label = 0
  rw [energyWeight_coeff]
  by_cases energyZero : totalEnergy D label = 0
  · have outside : jointTag D label ≠ index := by
      intro same
      exact nonzero ((congrArg Prod.snd same).symm.trans energyZero)
    rw [(mem_part D (jointTag D) index state).mp member label outside, mul_zero]
  · rw [if_neg energyZero, zero_mul]

theorem nonzero_joint_cohomology_zero (index : Charge D × ℤ) (nonzero : index.2 ≠ 0)
    (state : jointCohomology D H hHG hGH hcritical index) : state = 0 := by
  obtain ⟨representative, rfl⟩ :=
    (boundaries D H hHG hGH hcritical (subspaceParts D (jointTag D) ⊤ index)
      (sector_stable D H (jointTag D) ⊤ (top_stable D H)
        (jointProjection_Q D H hHG hGH) index)).mkQ_surjective state
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  apply (boundary_iff D H hHG hGH hcritical (subspaceParts D (jointTag D) ⊤ index)
    (sector_stable D H (jointTag D) ⊤ (top_stable D H)
      (jointProjection_Q D H hHG hGH) index) representative).mpr
  refine ⟨⟨projection D (jointTag D) index (h D representative.val),
    Submodule.mem_top, projection_mem D (jointTag D) index _⟩, ?_⟩
  have identity := LinearMap.congr_fun (homotopy_identity D H hHG hGH) representative.val
  change Q D H (h D representative.val) + h D (Q D H representative.val) =
    representative.val - P0 D representative.val at identity
  rw [representative.property.2, map_zero, add_zero,
    joint_nonzero_P0 D index nonzero representative.val representative.property.1.2,
    sub_zero] at identity
  have blocked := LinearMap.congr_fun (jointProjection_Q D H hHG hGH index)
    (h D representative.val)
  change projection D (jointTag D) index (Q D H (h D representative.val)) =
    Q D H (projection D (jointTag D) index (h D representative.val)) at blocked
  rw [← blocked, identity,
    projection_fixed D (jointTag D) index representative.property.1.2]

#print axioms absoluteJointEquiv
#print axioms full_image_iff_finite_boundaries
#print axioms absoluteZeroChargeEquiv
#print axioms relativeChargeEquiv
#print axioms zero_charge_full_image
#print axioms relative_image_iff_finite_boundaries
#print axioms nonzero_joint_cohomology_zero

end

end D5.S3.VertexAlgebra.OriginalBrstReassembly
