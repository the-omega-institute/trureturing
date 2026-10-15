/- GID: D5/S3/VertexAlgebra/OriginalZeroChargeBrstComplex
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/OriginalZeroChargeBrstComplex
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native exceptional BRST restriction, cycles, and boundaries of finite superpositions. -/

import D5.S3.VertexAlgebra.OriginalZeroChargeBrstDifferential
import Mathlib.LinearAlgebra.Isomorphisms

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace D5.S3.VertexAlgebra.OriginalZeroChargeBrstComplex

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeBcGhostBrstCharge
  OriginalZeroChargeEnergyBasis OriginalZeroChargeBrstDifferential
open scoped BigOperators

noncomputable section

instance sectorAddCommGroup (D : LatticeData) : AddCommGroup (sector D) :=
  Module.addCommMonoidToAddCommGroup ℂ

def differential (D : LatticeData) : Module.End ℂ (sector D) :=
  (sectorBasis D).constr ℂ (fun index =>
    if index = .inl .zeroMode then (2 : ℂ) • sectorBasis D (.inl .pair) else 0)

theorem differential_basis (D : LatticeData) (index : BasisIndex D) :
    differential D (sectorBasis D index) =
      if index = .inl .zeroMode then (2 : ℂ) • sectorBasis D (.inl .pair) else 0 := by
  simp [differential]

theorem differential_native (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftInverse : H * gramComplex D = 1) (rightInverse : gramComplex D * H = 1)
    (state : sector D) :
    (differential D state : State D) = Q D H (state : State D) := by
  have operators : (sector D).subtype.comp (differential D) =
      (Q D H).comp (sector D).subtype := by
    apply (sectorBasis D).ext
    intro index
    simp only [LinearMap.comp_apply, Submodule.subtype_apply,
      differential_basis, Q_sectorBasis D H leftInverse rightInverse]
    split_ifs <;> rfl
  exact congrArg (fun operator : sector D →ₗ[ℂ] State D => operator state) operators

theorem differential_squared (D : LatticeData) : differential D * differential D = 0 := by
  apply (sectorBasis D).ext
  intro index
  by_cases exceptional : index = .inl .zeroMode
  · subst index
    simp [Module.End.mul_apply, differential_basis]
  · simp [Module.End.mul_apply, differential_basis, exceptional]

theorem original_Q_squared_on_sector (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftInverse : H * gramComplex D = 1) (rightInverse : gramComplex D * H = 1)
    (state : sector D) : Q D H (Q D H (state : State D)) = 0 := by
  rw [← differential_native D H leftInverse rightInverse,
    ← differential_native D H leftInverse rightInverse]
  have square := congrArg (fun operator : Module.End ℂ (sector D) => operator state)
    (differential_squared D)
  simpa only [Module.End.mul_apply, LinearMap.zero_apply, Submodule.coe_zero]
    using congrArg Subtype.val square

theorem differential_formula (D : LatticeData) (state : sector D) :
    differential D state =
      ((2 : ℂ) * (sectorBasis D).repr state (.inl .zeroMode)) • sectorBasis D (.inl .pair) := by
  classical
  calc
    differential D state = differential D
        (∑ index, (sectorBasis D).repr state index • sectorBasis D index) := by
      rw [(sectorBasis D).sum_repr]
    _ = ∑ index, (sectorBasis D).repr state index •
        (if index = .inl .zeroMode then (2 : ℂ) • sectorBasis D (.inl .pair) else 0) := by
      simp only [map_sum, map_smul, differential_basis]
    _ = _ := by simp [smul_smul, mul_comm]

abbrev cycles (D : LatticeData) : Submodule ℂ (sector D) := LinearMap.ker (differential D)

abbrev boundaries (D : LatticeData) : Submodule ℂ (sector D) := LinearMap.range (differential D)

theorem cycles_iff (D : LatticeData) (state : sector D) :
    state ∈ cycles D ↔ (sectorBasis D).repr state (.inl .zeroMode) = 0 := by
  rw [cycles, LinearMap.mem_ker, differential_formula]
  simp [(sectorBasis D).ne_zero (.inl .pair)]

theorem boundaries_eq_span (D : LatticeData) :
    boundaries D = Submodule.span ℂ {sectorBasis D (.inl .pair)} := by
  ext state
  constructor
  · rintro ⟨preimage, rfl⟩
    rw [differential_formula]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · intro member
    obtain ⟨scalar, rfl⟩ := Submodule.mem_span_singleton.mp member
    refine ⟨(scalar / 2) • sectorBasis D (.inl .zeroMode), ?_⟩
    simp [differential_basis, smul_smul]

theorem boundaries_le_cycles (D : LatticeData) : boundaries D ≤ cycles D := by
  rintro state ⟨preimage, rfl⟩
  rw [cycles_iff, differential_formula]
  simp

set_option backward.isDefEq.respectTransparency false in
abbrev Cohomology (D : LatticeData) :=
  cycles D ⧸ (boundaries D).comap (cycles D).subtype

#print axioms differential_native
#print axioms original_Q_squared_on_sector
#print axioms cycles_iff
#print axioms boundaries_eq_span

end
end D5.S3.VertexAlgebra.OriginalZeroChargeBrstComplex
