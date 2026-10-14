import D5.S3.VertexAlgebra.LatticeBcGhostCohomologyCarrier

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.OriginalBrstReassembly

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeBcGhostBrstCharge
open scoped BigOperators DirectSum Classical

noncomputable section

variable (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
  (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
  (hcritical : D.rank = 26) {Index : Type*} (tag : FullLabel D → Index)
  (space : Submodule ℂ (State D))
  (stable : ∀ state, state ∈ space → Q D H state ∈ space)
  (projected : ∀ index state, state ∈ space → projection D tag index state ∈ space)
  (commutes : ∀ index, (projection D tag index).comp (Q D H) =
    (Q D H).comp (projection D tag index))

include stable commutes in
theorem sector_stable (index : Index) (state : State D)
    (member : state ∈ subspaceParts D tag space index) :
    Q D H state ∈ subspaceParts D tag space index := by
  refine ⟨stable state member.1, ?_⟩
  have equality := LinearMap.congr_fun (commutes index) state
  change projection D tag index (Q D H state) = Q D H (projection D tag index state)
    at equality
  rw [projection_fixed D tag index member.2] at equality
  rw [← equality]
  exact projection_mem D tag index (Q D H state)

include projected commutes in
theorem cycles_projected (index : Index) (state : State D)
    (member : state ∈ cycles D H space) :
    projection D tag index state ∈ cycles D H space := by
  refine ⟨projected index state member.1, ?_⟩
  have equality := LinearMap.congr_fun (commutes index) state
  change projection D tag index (Q D H state) = Q D H (projection D tag index state)
    at equality
  rw [member.2, map_zero] at equality
  exact equality.symm

def cycleSectorEquiv (index : Index) :
    subspaceParts D tag (cycles D H space) index ≃ₗ[ℂ]
      cycles D H (subspaceParts D tag space index) :=
  LinearEquiv.ofEq _ _ (by
    ext state
    simp only [subspaceParts, cycles, Submodule.mem_inf]
    tauto)

def cycleReassembly : cycles D H space ≃ₗ[ℂ]
    ⨁ index, cycles D H (subspaceParts D tag space index) :=
  (subspaceEquiv D tag (cycles D H space)
    (cycles_projected D H tag space projected commutes)).trans
      (DirectSum.congrLinearEquiv (cycleSectorEquiv D H tag space))

theorem cycleReassembly_component (state : cycles D H space) (index : Index) :
    (cycleReassembly D H tag space projected commutes state index : State D) =
      projection D tag index state.val := by
  exact subspaceSplitFun_component D tag (cycles D H space)
    (cycles_projected D H tag space projected commutes) state index

theorem cycleReassembly_inverse_lof (index : Index)
    (state : cycles D H (subspaceParts D tag space index)) :
    (cycleReassembly D H tag space projected commutes).symm
      (DirectSum.lof ℂ Index (fun index => cycles D H (subspaceParts D tag space index))
        index state) = ⟨state.val, state.property.1.1, state.property.2⟩ := by
  apply Subtype.ext
  apply (stateEquiv D tag).injective
  apply DFinsupp.ext
  intro other
  apply Subtype.ext
  rw [stateEquiv_component, stateEquiv_component]
  have inverseEquation := (cycleReassembly D H tag space projected commutes).apply_symm_apply
    (DirectSum.lof ℂ Index (fun index => cycles D H (subspaceParts D tag space index))
      index state)
  have componentEquation := congrArg (fun pieces =>
    (pieces other : State D)) inverseEquation
  rw [cycleReassembly_component] at componentEquation
  rw [componentEquation]
  by_cases same : index = other
  · subst other
    rw [DirectSum.lof_apply]
    exact (projection_fixed D tag index state.property.1.2).symm
  · rw [DirectSum.lof_eq_of, DirectSum.of_apply, dif_neg same]
    change (0 : State D) = projection D tag other state.val
    exact (projection_other D tag other index same state.property.1.2).symm

abbrev sectorCohomology (index : Index) :=
  Cohomology D H hHG hGH hcritical (subspaceParts D tag space index)
    (sector_stable D H tag space stable commutes index)

def cycleClassSplit : cycles D H space →ₗ[ℂ] ⨁ index,
    sectorCohomology D H hHG hGH hcritical tag space stable commutes index :=
  (DirectSum.lmap (fun index =>
    (boundaries D H hHG hGH hcritical (subspaceParts D tag space index)
      (sector_stable D H tag space stable commutes index)).mkQ)).comp
        (cycleReassembly D H tag space projected commutes).toLinearMap

theorem cycleClassSplit_boundary (state : cycles D H space)
    (member : state ∈ boundaries D H hHG hGH hcritical space stable) :
    cycleClassSplit D H hHG hGH hcritical tag space stable projected commutes state = 0 := by
  obtain ⟨preimage, equality⟩ :=
    (boundary_iff D H hHG hGH hcritical space stable state).mp member
  apply DFinsupp.ext
  intro index
  change (boundaries D H hHG hGH hcritical (subspaceParts D tag space index)
    (sector_stable D H tag space stable commutes index)).mkQ
      (cycleReassembly D H tag space projected commutes state index) = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  apply (boundary_iff D H hHG hGH hcritical (subspaceParts D tag space index)
    (sector_stable D H tag space stable commutes index) _).mpr
  refine ⟨⟨projection D tag index preimage.val,
    projected index preimage.val preimage.property,
    projection_mem D tag index preimage.val⟩, ?_⟩
  rw [cycleReassembly_component]
  have blocked := LinearMap.congr_fun (commutes index) preimage.val
  change projection D tag index (Q D H preimage.val) =
    Q D H (projection D tag index preimage.val) at blocked
  rw [← blocked, equality]

def classSplit : Cohomology D H hHG hGH hcritical space stable →ₗ[ℂ]
    ⨁ index, sectorCohomology D H hHG hGH hcritical tag space stable commutes index where
  toFun := Quotient.lift
    (fun state => cycleClassSplit D H hHG hGH hcritical tag space stable projected commutes state)
    (fun left right related => by
      letI : ∀ index, AddCommGroup
          (sectorCohomology D H hHG hGH hcritical tag space stable commutes index) :=
        fun index => inferInstanceAs (AddCommGroup
          (cycles D H (subspaceParts D tag space index) ⧸
            boundaries D H hHG hGH hcritical (subspaceParts D tag space index)
              (sector_stable D H tag space stable commutes index)))
      apply sub_eq_zero.mp
      rw [← map_sub]
      exact cycleClassSplit_boundary D H hHG hGH hcritical tag space stable projected commutes
        (left - right) ((Submodule.quotientRel_def _).mp related))
  map_add' := by
    rintro ⟨left⟩ ⟨right⟩
    exact (cycleClassSplit D H hHG hGH hcritical tag space stable projected commutes).map_add
      left right
  map_smul' := by
    rintro scalar ⟨state⟩
    exact (cycleClassSplit D H hHG hGH hcritical tag space stable projected commutes).map_smul
      scalar state

def sectorClassInclude (index : Index) :
    sectorCohomology D H hHG hGH hcritical tag space stable commutes index →ₗ[ℂ]
      Cohomology D H hHG hGH hcritical space stable :=
  homologyMap D H hHG hGH hcritical (subspaceParts D tag space index) space
    (sector_stable D H tag space stable commutes index) stable LinearMap.id
    (fun _ member => member.1) (by simp)

def classAssemble : (⨁ index,
    sectorCohomology D H hHG hGH hcritical tag space stable commutes index) →ₗ[ℂ]
      Cohomology D H hHG hGH hcritical space stable :=
  DirectSum.toModule ℂ Index _
    (sectorClassInclude D H hHG hGH hcritical tag space stable commutes)

theorem classAssemble_cycleClasses (pieces : ⨁ index,
    cycles D H (subspaceParts D tag space index)) :
    classAssemble D H hHG hGH hcritical tag space stable commutes
      (DirectSum.lmap (fun index =>
        (boundaries D H hHG hGH hcritical (subspaceParts D tag space index)
          (sector_stable D H tag space stable commutes index)).mkQ) pieces) =
    (boundaries D H hHG hGH hcritical space stable).mkQ
      ((cycleReassembly D H tag space projected commutes).symm pieces) := by
  have identity :
      (classAssemble D H hHG hGH hcritical tag space stable commutes).comp
        (DirectSum.lmap (fun index =>
          (boundaries D H hHG hGH hcritical (subspaceParts D tag space index)
            (sector_stable D H tag space stable commutes index)).mkQ)) =
      (boundaries D H hHG hGH hcritical space stable).mkQ.comp
        (cycleReassembly D H tag space projected commutes).symm.toLinearMap := by
    apply DirectSum.linearMap_ext
    intro index
    apply LinearMap.ext
    intro state
    simp only [LinearMap.comp_apply, DirectSum.lmap_lof, classAssemble,
      DirectSum.toModule_lof]
    change (sectorClassInclude D H hHG hGH hcritical tag space stable commutes index)
      ((boundaries D H hHG hGH hcritical (subspaceParts D tag space index)
        (sector_stable D H tag space stable commutes index)).mkQ state) =
      (boundaries D H hHG hGH hcritical space stable).mkQ
        ((cycleReassembly D H tag space projected commutes).symm
          (DirectSum.lof ℂ Index (fun index => cycles D H (subspaceParts D tag space index))
            index state))
    rw [cycleReassembly_inverse_lof]
    rfl
  exact LinearMap.congr_fun identity pieces

theorem classAssemble_split (state : Cohomology D H hHG hGH hcritical space stable) :
    classAssemble D H hHG hGH hcritical tag space stable commutes
      (classSplit D H hHG hGH hcritical tag space stable projected commutes state) = state := by
  obtain ⟨representative, rfl⟩ :=
    (boundaries D H hHG hGH hcritical space stable).mkQ_surjective state
  change classAssemble D H hHG hGH hcritical tag space stable commutes
    (DirectSum.lmap (fun index =>
      (boundaries D H hHG hGH hcritical (subspaceParts D tag space index)
        (sector_stable D H tag space stable commutes index)).mkQ)
          (cycleReassembly D H tag space projected commutes representative)) = _
  rw [classAssemble_cycleClasses D H hHG hGH hcritical tag space stable projected commutes,
    LinearEquiv.symm_apply_apply]

theorem classSplit_assemble (pieces : ⨁ index,
    sectorCohomology D H hHG hGH hcritical tag space stable commutes index) :
    classSplit D H hHG hGH hcritical tag space stable projected commutes
      (classAssemble D H hHG hGH hcritical tag space stable commutes pieces) = pieces := by
  obtain ⟨representatives, rfl⟩ :=
    ((DirectSum.lmap_surjective _).mpr (fun index =>
      (boundaries D H hHG hGH hcritical (subspaceParts D tag space index)
        (sector_stable D H tag space stable commutes index)).mkQ_surjective)) pieces
  rw [classAssemble_cycleClasses D H hHG hGH hcritical tag space stable projected commutes]
  change DirectSum.lmap (fun index =>
    (boundaries D H hHG hGH hcritical (subspaceParts D tag space index)
      (sector_stable D H tag space stable commutes index)).mkQ)
    (cycleReassembly D H tag space projected commutes
      ((cycleReassembly D H tag space projected commutes).symm representatives)) = _
  rw [LinearEquiv.apply_symm_apply]

def cohomologyReassembly : Cohomology D H hHG hGH hcritical space stable ≃ₗ[ℂ]
    ⨁ index, sectorCohomology D H hHG hGH hcritical tag space stable commutes index :=
  { classSplit D H hHG hGH hcritical tag space stable projected commutes with
    invFun := classAssemble D H hHG hGH hcritical tag space stable commutes
    left_inv := classAssemble_split D H hHG hGH hcritical tag space stable projected commutes
    right_inv := classSplit_assemble D H hHG hGH hcritical tag space stable projected commutes }

include projected commutes in
theorem original_image_iff_sector_images (state : space) :
    (∃ preimage : space, Q D H preimage.val = state.val) ↔
    ∀ index, ∃ preimage : subspaceParts D tag space index,
      Q D H preimage.val = projection D tag index state.val := by
  constructor
  · rintro ⟨preimage, equality⟩ index
    refine ⟨⟨projection D tag index preimage.val,
      projected index preimage.val preimage.property,
      projection_mem D tag index preimage.val⟩, ?_⟩
    have blocked := LinearMap.congr_fun (commutes index) preimage.val
    change projection D tag index (Q D H preimage.val) =
      Q D H (projection D tag index preimage.val) at blocked
    rw [← blocked, equality]
  · intro sectorPreimages
    choose preimage preimageEquation using sectorPreimages
    let witness : space :=
      ∑ index ∈ (stateEquiv D tag state.val).support,
        (subspaceParts D tag space index).inclusion inf_le_left (preimage index)
    refine ⟨witness, ?_⟩
    simp only [witness, Submodule.coe_sum, Submodule.inclusion_apply]
    rw [map_sum]
    simp_rw [preimageEquation]
    exact finite_reconstruction D tag state.val

end

end D5.S3.VertexAlgebra.OriginalBrstReassembly
