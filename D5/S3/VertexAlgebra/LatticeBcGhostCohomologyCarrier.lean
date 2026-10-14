import D5.S3.VertexAlgebra.LatticeBcGhostCohomologyPartition

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.OriginalBrstReassembly

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeBcGhostBrstCharge
open scoped BigOperators DirectSum Classical

noncomputable section

variable (D : LatticeData) {Index : Type*} (tag : FullLabel D → Index)
  (space : Submodule ℂ (State D))
  (projected : ∀ index state, state ∈ space → projection D tag index state ∈ space)

def subspaceParts (index : Index) : Submodule ℂ (State D) := space ⊓ part D tag index

def subspaceSplitFun (state : space) : ⨁ index, subspaceParts D tag space index :=
  DFinsupp.mk (stateEquiv D tag state.val).support (fun index =>
    ⟨projection D tag index.val state.val,
      projected index.val state.val state.property, projection_mem D tag index.val state.val⟩)

theorem subspaceSplitFun_component (state : space) (index : Index) :
    (subspaceSplitFun D tag space projected state index : State D) =
      projection D tag index state.val := by
  unfold subspaceSplitFun
  rw [DFinsupp.mk_apply]
  split_ifs with present
  · rfl
  · have vanished := DFinsupp.notMem_support_iff.mp present
    have equality := congrArg (fun value : part D tag index => (value : State D)) vanished
    change (0 : State D) = projection D tag index state.val
    change (stateEquiv D tag state.val index : State D) = 0 at equality
    rw [stateEquiv_component] at equality
    exact equality.symm

def subspaceSplit : space →ₗ[ℂ] ⨁ index, subspaceParts D tag space index where
  toFun := subspaceSplitFun D tag space projected
  map_add' left right := by
    apply DFinsupp.ext
    intro index
    apply Subtype.ext
    change (subspaceSplitFun D tag space projected (left + right) index : State D) =
      (subspaceSplitFun D tag space projected left index : State D) +
        (subspaceSplitFun D tag space projected right index : State D)
    rw [subspaceSplitFun_component, subspaceSplitFun_component, subspaceSplitFun_component]
    exact map_add (projection D tag index) left.val right.val
  map_smul' scalar state := by
    apply DFinsupp.ext
    intro index
    apply Subtype.ext
    change (subspaceSplitFun D tag space projected (scalar • state) index : State D) =
      scalar • (subspaceSplitFun D tag space projected state index : State D)
    rw [subspaceSplitFun_component, subspaceSplitFun_component]
    exact map_smul (projection D tag index) scalar state.val

def subspaceAssemble : (⨁ index, subspaceParts D tag space index) →ₗ[ℂ] space :=
  DirectSum.toModule ℂ Index space (fun index =>
    (subspaceParts D tag space index).inclusion inf_le_left)

theorem subspaceAssemble_projection (index : Index)
    (pieces : ⨁ other, subspaceParts D tag space other) :
    projection D tag index (subspaceAssemble D tag space pieces).val =
      (pieces index : State D) := by
  have identity : (projection D tag index).comp
      (space.subtype.comp (subspaceAssemble D tag space)) =
      (subspaceParts D tag space index).subtype.comp
        (DirectSum.component ℂ Index (fun index => subspaceParts D tag space index) index) := by
    apply DirectSum.linearMap_ext
    intro other
    apply LinearMap.ext
    intro state
    by_cases same : other = index
    · subst other
      simp only [LinearMap.comp_apply, subspaceAssemble, DirectSum.toModule_lof,
        DirectSum.component.lof_self, Submodule.subtype_apply, Submodule.inclusion_apply]
      exact projection_fixed D tag index state.property.2
    · simp only [LinearMap.comp_apply, subspaceAssemble, DirectSum.toModule_lof,
        DirectSum.component.of, dif_neg same, map_zero, Submodule.inclusion_apply]
      exact projection_other D tag index other same state.property.2
  exact LinearMap.congr_fun identity pieces

theorem subspaceAssemble_split (state : space) :
    subspaceAssemble D tag space (subspaceSplit D tag space projected state) = state := by
  apply Subtype.ext
  apply (stateEquiv D tag).injective
  apply DFinsupp.ext
  intro index
  apply Subtype.ext
  rw [stateEquiv_component, stateEquiv_component,
    subspaceAssemble_projection]
  exact subspaceSplitFun_component D tag space projected state index

theorem subspaceSplit_assemble (pieces : ⨁ index, subspaceParts D tag space index) :
    subspaceSplit D tag space projected (subspaceAssemble D tag space pieces) = pieces := by
  apply DFinsupp.ext
  intro index
  apply Subtype.ext
  rw [show (subspaceSplit D tag space projected
    (subspaceAssemble D tag space pieces) index : State D) =
      projection D tag index (subspaceAssemble D tag space pieces).val from
        subspaceSplitFun_component D tag space projected _ index,
    subspaceAssemble_projection]

def subspaceEquiv : space ≃ₗ[ℂ] ⨁ index, subspaceParts D tag space index :=
  { subspaceSplit D tag space projected with
    invFun := subspaceAssemble D tag space
    left_inv := subspaceAssemble_split D tag space projected
    right_inv := subspaceSplit_assemble D tag space projected }

variable (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)

def cycles (space : Submodule ℂ (State D)) : Submodule ℂ (State D) :=
  space ⊓ LinearMap.ker (Q D H)

variable (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
  (hcritical : D.rank = 26)

include hHG hGH hcritical in
theorem actual_square_zero (state : State D) : Q D H (Q D H state) = 0 := by
  exact LinearMap.congr_fun
    (LatticeBcGhostBrstNilpotence.nilpotent D H hHG hGH hcritical) state

def boundaryMap (space : Submodule ℂ (State D))
    (stable : ∀ state, state ∈ space → Q D H state ∈ space) :
    space →ₗ[ℂ] cycles D H space :=
  ((Q D H).comp space.subtype).codRestrict (cycles D H space) (fun state =>
    ⟨stable state.val state.property, actual_square_zero D H hHG hGH hcritical state.val⟩)

def boundaries (space : Submodule ℂ (State D))
    (stable : ∀ state, state ∈ space → Q D H state ∈ space) :
    Submodule ℂ (cycles D H space) :=
  LinearMap.range (boundaryMap D H hHG hGH hcritical space stable)

abbrev Cohomology (space : Submodule ℂ (State D))
    (stable : ∀ state, state ∈ space → Q D H state ∈ space) :=
  cycles D H space ⧸ boundaries D H hHG hGH hcritical space stable

theorem boundary_iff (space : Submodule ℂ (State D))
    (stable : ∀ state, state ∈ space → Q D H state ∈ space)
    (state : cycles D H space) :
    state ∈ boundaries D H hHG hGH hcritical space stable ↔
      ∃ preimage : space, Q D H preimage.val = state.val := by
  constructor
  · rintro ⟨preimage, equality⟩
    exact ⟨preimage, congrArg Subtype.val equality⟩
  · rintro ⟨preimage, equality⟩
    exact ⟨preimage, Subtype.ext equality⟩

def cyclesMap (source target : Submodule ℂ (State D))
    (operator : Module.End ℂ (State D))
    (maps : ∀ state, state ∈ source → operator state ∈ target)
    (commutes : operator.comp (Q D H) = (Q D H).comp operator) :
    cycles D H source →ₗ[ℂ] cycles D H target :=
  (operator.comp (cycles D H source).subtype).codRestrict (cycles D H target) (fun state => by
    refine ⟨maps state.val state.property.1, ?_⟩
    change Q D H (operator state.val) = 0
    have equality := LinearMap.congr_fun commutes state.val
    change operator (Q D H state.val) = Q D H (operator state.val) at equality
    rw [state.property.2, map_zero] at equality
    exact equality.symm)

def homologyMap (source target : Submodule ℂ (State D))
    (sourceStable : ∀ state, state ∈ source → Q D H state ∈ source)
    (targetStable : ∀ state, state ∈ target → Q D H state ∈ target)
    (operator : Module.End ℂ (State D))
    (maps : ∀ state, state ∈ source → operator state ∈ target)
    (commutes : operator.comp (Q D H) = (Q D H).comp operator) :
    Cohomology D H hHG hGH hcritical source sourceStable →ₗ[ℂ]
      Cohomology D H hHG hGH hcritical target targetStable :=
  (boundaries D H hHG hGH hcritical source sourceStable).mapQ
    (boundaries D H hHG hGH hcritical target targetStable)
    (cyclesMap D H source target operator maps commutes) (by
      intro state member
      obtain ⟨preimage, equality⟩ :=
        (boundary_iff D H hHG hGH hcritical source sourceStable state).mp member
      apply (boundary_iff D H hHG hGH hcritical target targetStable _).mpr
      refine ⟨⟨operator preimage.val, maps preimage.val preimage.property⟩, ?_⟩
      change Q D H (operator preimage.val) = operator state.val
      have blocked := LinearMap.congr_fun commutes preimage.val
      change operator (Q D H preimage.val) = Q D H (operator preimage.val) at blocked
      rw [← blocked, equality])

theorem homologyMap_mk (source target : Submodule ℂ (State D))
    (sourceStable : ∀ state, state ∈ source → Q D H state ∈ source)
    (targetStable : ∀ state, state ∈ target → Q D H state ∈ target)
    (operator : Module.End ℂ (State D))
    (maps : ∀ state, state ∈ source → operator state ∈ target)
    (commutes : operator.comp (Q D H) = (Q D H).comp operator)
    (state : cycles D H source) :
    homologyMap D H hHG hGH hcritical source target sourceStable targetStable operator
      maps commutes ((boundaries D H hHG hGH hcritical source sourceStable).mkQ state) =
    (boundaries D H hHG hGH hcritical target targetStable).mkQ
      (cyclesMap D H source target operator maps commutes state) := rfl

end

end D5.S3.VertexAlgebra.OriginalBrstReassembly
