import D5.S3.VertexAlgebra.LatticeBcGhostCohomologyReassembly

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.OriginalBrstReassembly

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeBcGhostBrstCharge
open scoped BigOperators DirectSum Classical

noncomputable section

abbrev nativeJ (D : LatticeData) := LatticeBcGhostBrstGhostNumber.J D

variable (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)

theorem nativeJ_Q (state : State D) :
    nativeJ D (Q D H state) = Q D H (nativeJ D state + state) := by
  have equality := LinearMap.congr_fun (LatticeBcGhostBrstGhostNumber.J_Q_commutator D H) state
  change nativeJ D (Q D H state) - Q D H (nativeJ D state) = Q D H state at equality
  rw [map_add]
  simpa only [add_comm] using sub_eq_iff_eq_add.mp equality

theorem nativeJ_cycle (state : State D) (cycle : Q D H state = 0) :
    Q D H (nativeJ D state) = 0 := by
  have equality := LinearMap.congr_fun (LatticeBcGhostBrstGhostNumber.J_Q_commutator D H) state
  change nativeJ D (Q D H state) - Q D H (nativeJ D state) = Q D H state at equality
  simpa only [cycle, map_zero, zero_sub, neg_eq_zero] using equality

variable (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
  (hcritical : D.rank = 26)
  (space : Submodule ℂ (State D))
  (stable : ∀ state, state ∈ space → Q D H state ∈ space)
  (numberStable : ∀ state, state ∈ space → nativeJ D state ∈ space)

def cycleJ : Module.End ℂ (cycles D H space) :=
  ((nativeJ D).comp (cycles D H space).subtype).codRestrict (cycles D H space)
    (fun state => ⟨numberStable state.val state.property.1,
      nativeJ_cycle D H state.val state.property.2⟩)

def cohomologyJ : Module.End ℂ (Cohomology D H hHG hGH hcritical space stable) :=
  (boundaries D H hHG hGH hcritical space stable).mapQ
    (boundaries D H hHG hGH hcritical space stable) (cycleJ D H space numberStable) (by
      intro state member
      obtain ⟨preimage, equation⟩ :=
        (boundary_iff D H hHG hGH hcritical space stable state).mp member
      apply (boundary_iff D H hHG hGH hcritical space stable _).mpr
      refine ⟨⟨nativeJ D preimage.val + preimage.val,
        space.add_mem (numberStable preimage.val preimage.property) preimage.property⟩, ?_⟩
      change Q D H (nativeJ D preimage.val + preimage.val) = nativeJ D state.val
      rw [← nativeJ_Q, equation])

variable {Index : Type*} (tag : FullLabel D → Index)
  (projected : ∀ index state, state ∈ space → projection D tag index state ∈ space)
  (commutes : ∀ index, (projection D tag index).comp (Q D H) =
    (Q D H).comp (projection D tag index))

include numberStable in
theorem sector_number_stable (index : Index) (state : State D)
    (member : state ∈ subspaceParts D tag space index) :
    nativeJ D state ∈ subspaceParts D tag space index := by
  refine ⟨numberStable state member.1, ?_⟩
  have equality := LinearMap.congr_fun (projection_J D tag index) state
  change projection D tag index (nativeJ D state) =
    nativeJ D (projection D tag index state) at equality
  rw [projection_fixed D tag index member.2] at equality
  rw [← equality]
  exact projection_mem D tag index (nativeJ D state)

def sectorJ (index : Index) : Module.End ℂ
    (sectorCohomology D H hHG hGH hcritical tag space stable commutes index) :=
  cohomologyJ D H hHG hGH hcritical (subspaceParts D tag space index)
    (sector_stable D H tag space stable commutes index)
    (sector_number_stable D space numberStable tag index)

theorem cohomologyReassembly_J (state : Cohomology D H hHG hGH hcritical space stable) :
    cohomologyReassembly D H hHG hGH hcritical tag space stable projected commutes
      (cohomologyJ D H hHG hGH hcritical space stable numberStable state) =
    DirectSum.lmap (sectorJ D H hHG hGH hcritical space stable numberStable tag commutes)
      (cohomologyReassembly D H hHG hGH hcritical tag space stable projected commutes state) := by
  obtain ⟨representative, rfl⟩ :=
    (boundaries D H hHG hGH hcritical space stable).mkQ_surjective state
  apply DFinsupp.ext
  intro index
  change (boundaries D H hHG hGH hcritical (subspaceParts D tag space index)
    (sector_stable D H tag space stable commutes index)).mkQ
      (cycleReassembly D H tag space projected commutes
        (cycleJ D H space numberStable representative) index) =
    (boundaries D H hHG hGH hcritical (subspaceParts D tag space index)
      (sector_stable D H tag space stable commutes index)).mkQ
        (cycleJ D H (subspaceParts D tag space index)
          (sector_number_stable D space numberStable tag index)
          (cycleReassembly D H tag space projected commutes representative index))
  congr 1
  apply Subtype.ext
  rw [cycleReassembly_component]
  change projection D tag index (nativeJ D representative.val) =
    nativeJ D (cycleReassembly D H tag space projected commutes representative index).val
  rw [cycleReassembly_component]
  exact LinearMap.congr_fun (projection_J D tag index) representative.val

include hHG hGH in
theorem J_T0 : (nativeJ D).comp (M D H 0 + G D 0) =
    (M D H 0 + G D 0).comp (nativeJ D) := by
  apply (fullBasis D).ext
  intro label
  simp only [LinearMap.comp_apply, totalZero_basis D H hHG hGH, J_basis,
    map_smul, smul_smul]
  rw [mul_comm]

theorem J_B0 : nativeJ D * B D 0 - B D 0 * nativeJ D = -B D 0 := by
  have lifted := congrArg (LinearMap.lTensorHom (Carrier D))
    (BcGhostNumber.J_b_commutator (K := ℂ) 0)
  simp only [map_sub, map_neg, LinearMap.coe_lTensorHom, LinearMap.lTensor_mul] at lifted
  simpa only [nativeJ, LatticeBcGhostBrstGhostNumber.J, B, LinearMap.lTensor_def] using lifted

include hHG hGH in
theorem zero_number_stable (state : State D) (member : state ∈ zeroSpace D H) :
    nativeJ D state ∈ zeroSpace D H := by
  have equality := LinearMap.congr_fun (J_T0 D H hHG hGH) state
  change nativeJ D ((M D H 0 + G D 0) state) =
    (M D H 0 + G D 0) (nativeJ D state) at equality
  rw [member, map_zero] at equality
  exact equality.symm

include hHG hGH in
theorem relative_number_stable (state : State D) (member : state ∈ relativeSpace D H) :
    nativeJ D state ∈ relativeSpace D H := by
  refine ⟨zero_number_stable D H hHG hGH state member.1, ?_⟩
  have equality := LinearMap.congr_fun (J_B0 D) state
  change nativeJ D (B D 0 state) - B D 0 (nativeJ D state) = -(B D 0 state) at equality
  have killed : B D 0 state = 0 := member.2
  change B D 0 (nativeJ D state) = 0
  simpa only [killed, map_zero, zero_sub, neg_zero, neg_eq_zero] using equality

theorem P0_J : (P0 D).comp (nativeJ D) = (nativeJ D).comp (P0 D) := by
  apply (fullBasis D).ext
  intro label
  change energyWeight D (fun energy => if energy = 0 then 1 else 0)
    (nativeJ D (fullBasis D label)) =
    nativeJ D (energyWeight D (fun energy => if energy = 0 then 1 else 0) (fullBasis D label))
  rw [J_basis, map_smul, energyWeight_basis, map_smul, J_basis]
  simp only [smul_smul]
  rw [mul_comm]

def absoluteJ : Module.End ℂ (absoluteCohomology D H hHG hGH hcritical) :=
  cohomologyJ D H hHG hGH hcritical ⊤ (top_stable D H) (fun _ _ => Submodule.mem_top)

def zeroJ : Module.End ℂ (zeroCohomology D H hHG hGH hcritical) :=
  cohomologyJ D H hHG hGH hcritical (zeroSpace D H) (zero_stable D H hHG hGH)
    (zero_number_stable D H hHG hGH)

def relativeJ : Module.End ℂ (relativeCohomology D H hHG hGH hcritical) :=
  cohomologyJ D H hHG hGH hcritical (relativeSpace D H) (relative_stable D H hHG hGH)
    (relative_number_stable D H hHG hGH)

def jointSectorJ (index : Charge D × ℤ) : Module.End ℂ
    (jointCohomology D H hHG hGH hcritical index) :=
  sectorJ D H hHG hGH hcritical ⊤ (top_stable D H) (fun _ _ => Submodule.mem_top)
    (jointTag D) (jointProjection_Q D H hHG hGH) index

def zeroSectorJ (charge : Charge D) : Module.End ℂ
    (zeroChargeCohomology D H hHG hGH hcritical charge) :=
  sectorJ D H hHG hGH hcritical (zeroSpace D H) (zero_stable D H hHG hGH)
    (zero_number_stable D H hHG hGH) (chargeTag D) (chargeProjection_Q D H) charge

def relativeSectorJ (charge : Charge D) : Module.End ℂ
    (relativeChargeCohomology D H hHG hGH hcritical charge) :=
  sectorJ D H hHG hGH hcritical (relativeSpace D H) (relative_stable D H hHG hGH)
    (relative_number_stable D H hHG hGH) (chargeTag D) (chargeProjection_Q D H) charge

theorem zeroReduction_J (state : absoluteCohomology D H hHG hGH hcritical) :
    zeroReduction D H hHG hGH hcritical (absoluteJ D H hHG hGH hcritical state) =
      zeroJ D H hHG hGH hcritical (zeroReduction D H hHG hGH hcritical state) := by
  obtain ⟨representative, rfl⟩ :=
    (boundaries D H hHG hGH hcritical ⊤ (top_stable D H)).mkQ_surjective state
  change (boundaries D H hHG hGH hcritical (zeroSpace D H)
    (zero_stable D H hHG hGH)).mkQ _ =
    (boundaries D H hHG hGH hcritical (zeroSpace D H)
      (zero_stable D H hHG hGH)).mkQ _
  congr 1
  apply Subtype.ext
  exact LinearMap.congr_fun (P0_J D) representative.val

theorem absoluteJointEquiv_J (state : absoluteCohomology D H hHG hGH hcritical) :
    absoluteJointEquiv D H hHG hGH hcritical (absoluteJ D H hHG hGH hcritical state) =
    DirectSum.lmap (jointSectorJ D H hHG hGH hcritical)
      (absoluteJointEquiv D H hHG hGH hcritical state) :=
  cohomologyReassembly_J D H hHG hGH hcritical ⊤ (top_stable D H)
    (fun _ _ => Submodule.mem_top) (jointTag D) (fun _ _ _ => Submodule.mem_top)
    (jointProjection_Q D H hHG hGH) state

theorem absoluteZeroChargeEquiv_J (state : absoluteCohomology D H hHG hGH hcritical) :
    absoluteZeroChargeEquiv D H hHG hGH hcritical (absoluteJ D H hHG hGH hcritical state) =
    DirectSum.lmap (zeroSectorJ D H hHG hGH hcritical)
      (absoluteZeroChargeEquiv D H hHG hGH hcritical state) := by
  change cohomologyReassembly D H hHG hGH hcritical (chargeTag D) (zeroSpace D H)
    (zero_stable D H hHG hGH) (zero_projected D H hHG hGH (chargeTag D))
    (chargeProjection_Q D H) (zeroReduction D H hHG hGH hcritical
      (absoluteJ D H hHG hGH hcritical state)) = _
  rw [zeroReduction_J]
  exact cohomologyReassembly_J D H hHG hGH hcritical (zeroSpace D H)
    (zero_stable D H hHG hGH) (zero_number_stable D H hHG hGH) (chargeTag D)
    (zero_projected D H hHG hGH (chargeTag D)) (chargeProjection_Q D H)
    (zeroReduction D H hHG hGH hcritical state)

theorem relativeChargeEquiv_J (state : relativeCohomology D H hHG hGH hcritical) :
    relativeChargeEquiv D H hHG hGH hcritical (relativeJ D H hHG hGH hcritical state) =
    DirectSum.lmap (relativeSectorJ D H hHG hGH hcritical)
      (relativeChargeEquiv D H hHG hGH hcritical state) :=
  cohomologyReassembly_J D H hHG hGH hcritical (relativeSpace D H)
    (relative_stable D H hHG hGH) (relative_number_stable D H hHG hGH) (chargeTag D)
    (relative_projected D H hHG hGH) (chargeProjection_Q D H) state

theorem absolute_ghost_degree_transport (degree : ℤ)
    (state : absoluteCohomology D H hHG hGH hcritical)
    (homogeneous : absoluteJ D H hHG hGH hcritical state = (degree : ℂ) • state) :
    DirectSum.lmap (zeroSectorJ D H hHG hGH hcritical)
      (absoluteZeroChargeEquiv D H hHG hGH hcritical state) =
      (degree : ℂ) • absoluteZeroChargeEquiv D H hHG hGH hcritical state := by
  rw [← absoluteZeroChargeEquiv_J, homogeneous, map_smul]

theorem relative_ghost_degree_transport (degree : ℤ)
    (state : relativeCohomology D H hHG hGH hcritical)
    (homogeneous : relativeJ D H hHG hGH hcritical state = (degree : ℂ) • state) :
    DirectSum.lmap (relativeSectorJ D H hHG hGH hcritical)
      (relativeChargeEquiv D H hHG hGH hcritical state) =
      (degree : ℂ) • relativeChargeEquiv D H hHG hGH hcritical state := by
  rw [← relativeChargeEquiv_J, homogeneous, map_smul]

#print axioms absoluteJointEquiv_J
#print axioms absoluteZeroChargeEquiv_J
#print axioms relativeChargeEquiv_J
#print axioms absolute_ghost_degree_transport
#print axioms relative_ghost_degree_transport

end

end D5.S3.VertexAlgebra.OriginalBrstReassembly
