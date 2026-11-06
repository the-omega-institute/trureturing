/- GID: D5/S3/VertexAlgebra/Lattice/LatticeAbsoluteZeroFullCohomology
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LatticeAbsoluteZeroFullCohomology
   mirror-E: none(waiver:algebraic-original-absolute-full-retract)
   anchors: []
   utility: none
   digest: Original charge and energy projection reflects arbitrary ambient BRST primitives and splits absolute-zero classes into the full quotient. -/

/- The original lattice, ghost, BRST and absolute-zero constructions retain
their suppliers' authorship. The projection route uses the supplied Pro
proposal; the original-operator and arbitrary-primitive proofs are native
Lean constructions. Mathlib quotient and basis machinery is Apache 2.0.
No literature novelty or full-quotient finite-dimensionality is asserted. -/

import D5.S3.VertexAlgebra.Lattice.LatticeOriginalAbsoluteZeroCohomology
import D5.S3.VertexAlgebra.Lattice.LatticeBRSTZeroEnergyReduction
import D5.S3.VertexAlgebra.Lattice.LatticeRelativeBRSTGround
import Mathlib.LinearAlgebra.Basis.Prod

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped TensorProduct Classical

namespace D5.S3.VertexAlgebra.LatticeAbsoluteZeroFullCohomology

open LatticeGeneratingFieldLocality (LatticeData)
open LatticeSugawaraCurrents (gramComplex)
open LatticeMatterGhostCoupling (State)
open LatticeBRST (totalCharge)
open LatticeRelativeMassShell (Charge TensorLabel tensorBasis tensorCoeffEquiv coeff
  fixedMomentum mem_fixedMomentum_iff totalCharge_mem_fixedMomentum totalL0 totalL0_basis)
open LatticeQuartetContraction (chargeProject)
open LatticeOriginalAbsoluteZeroCohomology
open private chargeProject_original_basis chargeProject_original_coeff
  mem_fixedMomentum_iff_chargeProject
  from D5.S3.VertexAlgebra.Lattice.LatticeRelativeBRSTGround

variable (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)

private theorem project_fixed (p : Charge D) (x : State D) :
    chargeProject p x ∈ fixedMomentum D p := by
  apply (mem_fixedMomentum_iff D p _).mpr
  intro i hi
  rw [chargeProject_original_coeff, if_neg hi]

private theorem project_other (p q : Charge D) (hpq : p ≠ q)
    (x : State D) (hx : x ∈ fixedMomentum D q) : chargeProject p x = 0 := by
  apply (tensorCoeffEquiv D).injective
  ext i
  change coeff D (chargeProject p x) i = coeff D 0 i
  rw [chargeProject_original_coeff]
  by_cases hi : i.1.1 = p
  · rw [if_pos hi, (mem_fixedMomentum_iff D q x).mp hx i (hi ▸ hpq)]
    rfl
  · rw [if_neg hi]
    rfl

private theorem chargeProject_Q (p : Charge D) :
    chargeProject p * totalCharge D H = totalCharge D H * chargeProject p := by
  apply (tensorBasis D).ext
  intro i
  have hi : tensorBasis D i ∈ fixedMomentum D i.1.1 :=
    (mem_fixedMomentum_iff_chargeProject i.1.1 _).mpr (by
      rw [chargeProject_original_basis, if_pos rfl, one_smul])
  have hQi := totalCharge_mem_fixedMomentum D H i.1.1 hi
  change chargeProject p (totalCharge D H (tensorBasis D i)) =
    totalCharge D H (chargeProject p (tensorBasis D i))
  rw [chargeProject_original_basis, map_smul]
  by_cases hp : i.1.1 = p
  · rw [if_pos hp, one_smul]
    exact (mem_fixedMomentum_iff_chargeProject p _).mp (hp ▸ hQi)
  · rw [if_neg hp, zero_smul, project_other D p i.1.1 (Ne.symm hp) _ hQi]

private theorem chargeProject_L0
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (p : Charge D) :
    totalL0 D H * chargeProject p = chargeProject p * totalL0 D H := by
  apply (tensorBasis D).ext
  intro i
  simp only [Module.End.mul_apply, chargeProject_original_basis,
    totalL0_basis D H hHG hGH, map_smul, smul_smul]
  rw [mul_comm]

/-- Actual original charge projection after the actual total-energy projector. -/
def rho : Module.End ℂ (State D) :=
  (chargeProject (0 : Charge D)).comp (LatticeBRSTZeroEnergyReduction.P0 D)

variable (h26 : D.rank = 26)
variable (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)

theorem rho_chain : rho D * totalCharge D H = totalCharge D H * rho D := by
  change (chargeProject (0 : Charge D) * LatticeBRSTZeroEnergyReduction.P0 D) *
      totalCharge D H = totalCharge D H *
        (chargeProject (0 : Charge D) * LatticeBRSTZeroEnergyReduction.P0 D)
  rw [mul_assoc, LatticeBRSTZeroEnergyReduction.P0_commutes D H h26 hHG hGH,
    ← mul_assoc, chargeProject_Q D H, mul_assoc]

private theorem rho_mem (x : State D) : rho D x ∈ E0 D H := by
  refine ⟨project_fixed D 0 _, ?_⟩
  change totalL0 D H (chargeProject 0 (LatticeBRSTZeroEnergyReduction.P0 D x)) = 0
  have hc := LinearMap.congr_fun (chargeProject_L0 D H hHG hGH 0)
    (LatticeBRSTZeroEnergyReduction.P0 D x)
  change totalL0 D H (chargeProject 0 _) = chargeProject 0 (totalL0 D H _) at hc
  rw [hc, show totalL0 D H (LatticeBRSTZeroEnergyReduction.P0 D x) = 0 from
    LatticeBRSTZeroEnergyReduction.totalL0_P0 D H hHG hGH x, map_zero]

/-- The retraction is constructed on every original state, including primitives. -/
def retractState : State D →ₗ[ℂ] E0 D H :=
  (rho D).codRestrict _ (rho_mem D H hHG hGH)

private theorem retractState_fixed (x : E0 D H) :
    retractState D H hHG hGH x = x := by
  apply Subtype.ext
  change chargeProject 0 (LatticeBRSTZeroEnergyReduction.P0 D (x : State D)) = x
  rw [(LatticeBRSTZeroEnergyReduction.P0_fixed_iff D H hHG hGH _).mpr x.2.2]
  exact (mem_fixedMomentum_iff_chargeProject 0 _).mp x.2.1

private theorem retractState_chain (y : State D) :
    Q0 D H hHG hGH (retractState D H hHG hGH y) =
      retractState D H hHG hGH (totalCharge D H y) := by
  apply Subtype.ext
  exact (LinearMap.congr_fun (rho_chain D H h26 hHG hGH) y).symm

/-- No restriction is imposed on the original full-state boundary primitive y. -/
theorem ambient_primitive (x : E0 D H) (y : State D)
    (hy : totalCharge D H y = (x : State D)) :
    Q0 D H hHG hGH (retractState D H hHG hGH y) = x := by
  rw [retractState_chain D H h26 hHG hGH, hy,
    retractState_fixed D H hHG hGH]

theorem range_Q0_eq_comap : LinearMap.range (Q0 D H hHG hGH) =
    (LinearMap.range (totalCharge D H)).comap (E0 D H).subtype := by
  ext x
  constructor
  · rintro ⟨y,hy⟩
    exact ⟨(y : State D), congrArg Subtype.val hy⟩
  · rintro ⟨y,hy⟩
    exact ⟨retractState D H hHG hGH y, ambient_primitive D H h26 hHG hGH x y hy⟩

def includeCycle : Cycles D H hHG hGH →ₗ[ℂ] LatticeBRSTCohomologyField.cycles D H :=
  ((E0 D H).subtype.comp (Cycles D H hHG hGH).subtype).codRestrict _
    (fun x => congrArg Subtype.val x.property)

def retractCycle : LatticeBRSTCohomologyField.cycles D H →ₗ[ℂ] Cycles D H hHG hGH :=
  ((retractState D H hHG hGH).comp
    (LatticeBRSTCohomologyField.cycles D H).subtype).codRestrict _ (by
      intro x
      change Q0 D H hHG hGH (retractState D H hHG hGH x) = 0
      rw [retractState_chain D H h26 hHG hGH, x.property, map_zero])

private theorem include_boundary : Boundaries D H hHG hGH ≤
    (LatticeBRSTCohomologyField.boundaries D H h26 hHG hGH).comap
      (includeCycle D H hHG hGH) := by
  rintro x ⟨y, rfl⟩
  exact (LatticeBRSTCohomologyField.mem_boundaries D H h26 hHG hGH _).mpr
    ⟨(y : State D), rfl⟩

private theorem retract_boundary : LatticeBRSTCohomologyField.boundaries D H h26 hHG hGH ≤
    (Boundaries D H hHG hGH).comap (retractCycle D H h26 hHG hGH) := by
  intro x hx
  obtain ⟨y,hy⟩ := (LatticeBRSTCohomologyField.mem_boundaries D H h26 hHG hGH x).mp hx
  refine ⟨retractState D H hHG hGH y, ?_⟩
  apply Subtype.ext
  change Q0 D H hHG hGH (retractState D H hHG hGH y) =
    retractState D H hHG hGH (x : State D)
  rw [retractState_chain D H h26 hHG hGH, hy]

/-- Literal inclusion, descended through the two different incoming boundary ranges. -/
def inclusion : Cohomology D H hHG hGH →ₗ[ℂ]
    LatticeBRSTCohomologyField.Cohomology D H h26 hHG hGH :=
  (Boundaries D H hHG hGH).mapQ
    (LatticeBRSTCohomologyField.boundaries D H h26 hHG hGH)
    (includeCycle D H hHG hGH) (include_boundary D H h26 hHG hGH)

/-- Actual rho on cycles, descended using arbitrary original-state primitives. -/
def retraction : LatticeBRSTCohomologyField.Cohomology D H h26 hHG hGH →ₗ[ℂ]
    Cohomology D H hHG hGH :=
  (LatticeBRSTCohomologyField.boundaries D H h26 hHG hGH).mapQ
    (Boundaries D H hHG hGH) (retractCycle D H h26 hHG hGH)
    (retract_boundary D H h26 hHG hGH)

theorem retraction_inclusion (c : Cohomology D H hHG hGH) :
    retraction D H h26 hHG hGH (inclusion D H h26 hHG hGH c) = c := by
  obtain ⟨x, rfl⟩ := (Boundaries D H hHG hGH).mkQ_surjective c
  change (Boundaries D H hHG hGH).mkQ
    (retractCycle D H h26 hHG hGH (includeCycle D H hHG hGH x)) =
      (Boundaries D H hHG hGH).mkQ x
  congr 1
  apply Subtype.ext
  exact retractState_fixed D H hHG hGH x.1

private theorem include_boundary_iff (x : Cycles D H hHG hGH) :
    LatticeBRSTCohomologyField.classOf D H h26 hHG hGH
      (includeCycle D H hHG hGH x) = 0 ↔ x ∈ Boundaries D H hHG hGH := by
  rw [LatticeBRSTCohomologyField.classOf_eq_zero]
  constructor
  · intro hx
    have hr : x.1 ∈ LinearMap.range (Q0 D H hHG hGH) := by
      rw [range_Q0_eq_comap D H h26 hHG hGH]
      exact hx
    obtain ⟨y,hy⟩ := hr
    exact ⟨y,Subtype.ext hy⟩
  · rintro ⟨y,hy⟩
    exact ⟨(y : State D), congrArg (fun z : Cycles D H hHG hGH =>
      ((z : E0 D H) : State D)) hy⟩

/-- The four-slot map has the original representative, now in the full quotient. -/
def fullClass : ClassCoordinates D →ₗ[ℂ]
    LatticeBRSTCohomologyField.Cohomology D H h26 hHG hGH :=
  (inclusion D H h26 hHG hGH).comp (classOf D H hHG hGH)

private theorem fullClass_injective : Function.Injective (fullClass D H h26 hHG hGH) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro t ht
  have hb : representative D H hHG hGH t ∈ Boundaries D H hHG hGH :=
    (include_boundary_iff D H h26 hHG hGH _).mp ht
  have hz : classOf D H hHG hGH t = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hb
  have := congrArg (cohomologyEquiv D H hHG hGH) hz
  simpa only [cohomologyEquiv_classOf, map_zero] using this

/-- Scalar, first vector, second vector, scalar: the original four slots. -/
abbrev ClassIndex := Unit ⊕ (Fin D.rank ⊕ (Fin D.rank ⊕ Unit))

private def coordinateBasis : Module.Basis (ClassIndex D) ℂ (ClassCoordinates D) :=
  (Module.Basis.singleton Unit ℂ).prod
    ((Pi.basisFun ℂ (Fin D.rank)).prod
      ((Pi.basisFun ℂ (Fin D.rank)).prod (Module.Basis.singleton Unit ℂ)))

def fullClasses : ClassIndex D →
    LatticeBRSTCohomologyField.Cohomology D H h26 hHG hGH :=
  fun i => fullClass D H h26 hHG hGH (coordinateBasis D i)

/-- A finite independent family in the full quotient, without a dimension claim. -/
theorem fullClasses_independent :
    LinearIndependent ℂ (fullClasses D H h26 hHG hGH) ∧
      Fintype.card (ClassIndex D) = 2 + 2 * D.rank ∧
      Fintype.card (ClassIndex D) = 54 := by
  refine ⟨(coordinateBasis D).linearIndependent.map'
    (fullClass D H h26 hHG hGH)
    (LinearMap.ker_eq_bot.mpr (fullClass_injective D H h26 hHG hGH)), ?_, ?_⟩
  · simp [ClassIndex]; omega
  · simp [ClassIndex, h26]

end D5.S3.VertexAlgebra.LatticeAbsoluteZeroFullCohomology
