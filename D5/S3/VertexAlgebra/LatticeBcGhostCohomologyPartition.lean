import D5.S3.VertexAlgebra.LatticeBcGhostCohomologyReassemblySupport
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Quotient.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.OriginalBrstReassembly

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeBcGhostBrstCharge
  BcGhostFockSupport
open scoped BigOperators TensorProduct DirectSum Classical

noncomputable section

variable (D : LatticeData) {Index : Type*} (tag : FullLabel D → Index)

def part (index : Index) : Submodule ℂ (State D) :=
  (Finsupp.supported ℂ ℂ {label | tag label = index}).comap
    (fullBasis D).repr.toLinearMap

def projection (index : Index) : Module.End ℂ (State D) :=
  (fullBasis D).repr.symm.toLinearMap.comp
    ((Finsupp.supported ℂ ℂ {label | tag label = index}).subtype.comp
      ((Finsupp.restrictDom ℂ ℂ {label | tag label = index}).comp
        (fullBasis D).repr.toLinearMap))

theorem projection_coeff (index : Index) (state : State D) (label : FullLabel D) :
    (fullBasis D).repr (projection D tag index state) label =
      if tag label = index then (fullBasis D).repr state label else 0 := by
  simp [projection, Finsupp.restrictDom_apply, Finsupp.filter_apply]

theorem mem_part (index : Index) (state : State D) :
    state ∈ part D tag index ↔
      ∀ label, tag label ≠ index → (fullBasis D).repr state label = 0 := by
  exact Finsupp.mem_supported' ℂ ((fullBasis D).repr state)

theorem projection_mem (index : Index) (state : State D) :
    projection D tag index state ∈ part D tag index := by
  rw [mem_part]
  intro label outside
  rw [projection_coeff, if_neg outside]

theorem projection_fixed (index : Index) {state : State D}
    (member : state ∈ part D tag index) : projection D tag index state = state := by
  apply (fullBasis D).repr.injective
  ext label
  rw [projection_coeff]
  by_cases inside : tag label = index
  · rw [if_pos inside]
  · rw [if_neg inside, (mem_part D tag index state).mp member label inside]

theorem projection_other (index other : Index) (different : other ≠ index)
    {state : State D} (member : state ∈ part D tag other) :
    projection D tag index state = 0 := by
  apply (fullBasis D).repr.injective
  ext label
  rw [projection_coeff]
  by_cases inside : tag label = index
  · rw [if_pos inside, (mem_part D tag other state).mp member label (by
      intro equality
      exact different (equality.symm.trans inside))]
    rfl
  · rw [if_neg inside]
    rfl

theorem projection_orthogonal (index other : Index) :
    (projection D tag index).comp (projection D tag other) =
      if index = other then projection D tag index else 0 := by
  apply LinearMap.ext
  intro state
  by_cases same : index = other
  · subst other
    simp only [if_pos rfl, LinearMap.comp_apply]
    exact projection_fixed D tag index (projection_mem D tag index state)
  · simp only [if_neg same, LinearMap.comp_apply, LinearMap.zero_apply]
    exact projection_other D tag index other (Ne.symm same)
      (projection_mem D tag other state)

theorem basis_mem_part (label : FullLabel D) :
    fullBasis D label ∈ part D tag (tag label) := by
  rw [mem_part]
  intro output different
  rw [(fullBasis D).repr_self]
  simp only [Finsupp.single_apply]
  split_ifs with equal
  · subst output
    exact (different rfl).elim
  · rfl

def basisSplit : State D →ₗ[ℂ] ⨁ index, part D tag index :=
  (fullBasis D).constr ℂ (fun label =>
    DirectSum.lof ℂ Index (fun index => part D tag index) (tag label)
      ⟨fullBasis D label, basis_mem_part D tag label⟩)

theorem assemble_basisSplit :
    (DirectSum.coeLinearMap (part D tag)).comp (basisSplit D tag) = LinearMap.id := by
  apply (fullBasis D).ext
  intro label
  simp [basisSplit, Module.Basis.constr_basis]

theorem projection_assemble (index : Index) (pieces : ⨁ other, part D tag other) :
    projection D tag index (DirectSum.coeLinearMap (part D tag) pieces) =
      (pieces index : State D) := by
  have identity : (projection D tag index).comp (DirectSum.coeLinearMap (part D tag)) =
      (part D tag index).subtype.comp
        (DirectSum.component ℂ Index (fun index => part D tag index) index) := by
    apply DirectSum.linearMap_ext
    intro other
    apply LinearMap.ext
    intro state
    by_cases same : other = index
    · subst other
      simp only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof,
        DirectSum.component.lof_self, Submodule.subtype_apply]
      exact projection_fixed D tag index state.property
    · simp only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof,
        DirectSum.component.of, dif_neg same, map_zero]
      exact projection_other D tag index other same state.property
  exact LinearMap.congr_fun identity pieces

theorem parts_internal : DirectSum.IsInternal (part D tag) := by
  constructor
  · intro left right equal
    change DirectSum.coeLinearMap (part D tag) left =
      DirectSum.coeLinearMap (part D tag) right at equal
    apply DFinsupp.ext
    intro index
    apply Subtype.ext
    rw [← projection_assemble D tag index left, ← projection_assemble D tag index right,
      equal]
  · intro state
    refine ⟨basisSplit D tag state, ?_⟩
    exact LinearMap.congr_fun (assemble_basisSplit D tag) state

def stateEquiv : State D ≃ₗ[ℂ] ⨁ index, part D tag index :=
  (LinearEquiv.ofBijective (DirectSum.coeLinearMap (part D tag))
    (parts_internal D tag)).symm

theorem stateEquiv_component (state : State D) (index : Index) :
    (stateEquiv D tag state index : State D) = projection D tag index state := by
  rw [← projection_assemble D tag index (stateEquiv D tag state)]
  congr 1
  exact (stateEquiv D tag).symm_apply_apply state

theorem finite_reconstruction (state : State D) :
    ∑ index ∈ (stateEquiv D tag state).support,
      projection D tag index state = state := by
  have equality := congrArg (fun pieces => DirectSum.coeLinearMap (part D tag) pieces)
    (DirectSum.sum_support_of (stateEquiv D tag state))
  simp only [map_sum, DirectSum.coeLinearMap_of, stateEquiv_component] at equality
  change (∑ index ∈ (stateEquiv D tag state).support,
    projection D tag index state) =
    (stateEquiv D tag).symm (stateEquiv D tag state) at equality
  simpa only [LinearEquiv.symm_apply_apply] using equality

theorem support_from_basis (state : State D) :
    (stateEquiv D tag state).support ⊆ ((fullBasis D).repr state).support.image tag := by
  intro index member
  by_contra absent
  have zeroProjection : projection D tag index state = 0 := by
    apply (fullBasis D).repr.injective
    ext label
    rw [projection_coeff]
    by_cases same : tag label = index
    · rw [if_pos same]
      have outside : label ∉ ((fullBasis D).repr state).support := by
        intro present
        exact absent (Finset.mem_image.mpr ⟨label, present, same⟩)
      exact Finsupp.notMem_support_iff.mp outside
    · rw [if_neg same]
      rfl
  have zeroComponent : stateEquiv D tag state index = 0 := by
    apply Subtype.ext
    rw [stateEquiv_component, zeroProjection]
    rfl
  exact (DFinsupp.mem_support_iff.mp member) zeroComponent

theorem projection_commutes (operator : Module.End ℂ (State D))
    (blocks : ∀ input output, tag output ≠ tag input →
      (fullBasis D).repr (operator (fullBasis D input)) output = 0)
    (index : Index) :
    (projection D tag index).comp operator = operator.comp (projection D tag index) := by
  apply (fullBasis D).ext
  intro input
  apply (fullBasis D).repr.injective
  ext output
  have basisProjection : projection D tag index (fullBasis D input) =
      if tag input = index then fullBasis D input else 0 := by
    by_cases same : tag input = index
    · rw [if_pos same]
      exact projection_fixed D tag index (same ▸ basis_mem_part D tag input)
    · rw [if_neg same]
      exact projection_other D tag index (tag input) same (basis_mem_part D tag input)
  simp only [LinearMap.comp_apply, projection_coeff, basisProjection]
  by_cases same : tag output = tag input
  · rw [same]
    split_ifs <;> first | rfl | simp
  · rw [blocks input output same]
    split_ifs <;> first | rfl | simp [blocks input output same]

def jointTag (label : FullLabel D) : Charge D × ℤ :=
  (label.1.1, totalEnergy D label)

def chargeTag (label : FullLabel D) : Charge D := label.1.1

theorem jointProjection_Q (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (index : Charge D × ℤ) :
    (projection D (jointTag D) index).comp (Q D H) =
      (Q D H).comp (projection D (jointTag D) index) := by
  apply projection_commutes
  intro input output different
  by_contra nonzero
  obtain ⟨chargeEqual, energyEqual⟩ := Q_coefficient_blocks D H hHG hGH input output nonzero
  exact different (Prod.ext chargeEqual energyEqual)

theorem chargeProjection_Q (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (index : Charge D) :
    (projection D (chargeTag D) index).comp (Q D H) =
      (Q D H).comp (projection D (chargeTag D) index) := by
  apply projection_commutes
  exact Q_charge_coeff_zero D H

theorem chargeProjection_B (index : Charge D) :
    (projection D (chargeTag D) index).comp (B D 0) =
      (B D 0).comp (projection D (chargeTag D) index) := by
  apply projection_commutes
  intro input output different
  rw [fullBasis_apply, LatticePositiveEnergy.carrierBasis_apply]
  change (fullBasis D).repr (TensorProduct.map LinearMap.id (b 0)
    (Finsupp.single input.1.1 (MvPolynomial.monomial input.1.2 1) ⊗ₜ[ℂ]
      Finsupp.single input.2 1)) output = 0
  rw [TensorProduct.map_tmul, LinearMap.id_apply]
  exact single_charge_coeff_zero D _ _ _ output different

theorem projection_T0 (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (index : Index) :
    (projection D tag index).comp (M D H 0 + G D 0) =
      (M D H 0 + G D 0).comp (projection D tag index) := by
  apply projection_commutes
  intro input output different
  rw [totalZero_basis D H hHG hGH, map_smul, Finsupp.smul_apply, (fullBasis D).repr_self]
  have notEqual : input ≠ output := by
    intro same
    subst output
    exact different rfl
  simp [Finsupp.single_apply, notEqual]

theorem J_basis (label : FullLabel D) :
    LatticeBcGhostBrstGhostNumber.J D (fullBasis D label) =
      (BcGhostNumber.degree label.2 : ℂ) • fullBasis D label := by
  have ghost : BcGhostNumber.J (K := ℂ) (Finsupp.single label.2 1) =
      (BcGhostNumber.degree label.2 : ℂ) • Finsupp.single label.2 1 := by
    simp [BcGhostNumber.J]
  rw [fullBasis_apply]
  change TensorProduct.map LinearMap.id BcGhostNumber.J
    (LatticePositiveEnergy.carrierBasis D label.1 ⊗ₜ[ℂ] Finsupp.single label.2 1) = _
  rw [TensorProduct.map_tmul, LinearMap.id_apply, ghost, TensorProduct.tmul_smul]

theorem projection_J (index : Index) :
    (projection D tag index).comp (LatticeBcGhostBrstGhostNumber.J D) =
      (LatticeBcGhostBrstGhostNumber.J D).comp (projection D tag index) := by
  apply projection_commutes
  intro input output different
  rw [J_basis, map_smul, Finsupp.smul_apply, (fullBasis D).repr_self]
  have notEqual : input ≠ output := by
    intro same
    subst output
    exact different rfl
  simp [Finsupp.single_apply, notEqual]

end

end D5.S3.VertexAlgebra.OriginalBrstReassembly
