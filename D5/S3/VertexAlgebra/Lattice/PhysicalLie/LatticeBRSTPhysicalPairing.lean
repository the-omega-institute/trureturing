/-
The form below is the literal inserted-c0
form for the current ordinary tensor Hermitian form and current original Q.

Attribution: original BRST (Becchi--Rouet--Stora--Tyutin), Kato--Ogawa,
Lian--Zuckerman; the saved physical-descent mechanism, identified in inputs.json
as historical only. The proof here derives the ordinary Hermitian signs anew.
No historical rotated form or graded sign is imported. Supplier attribution
to Bakalov--Kac, Scott Carnahan, Kalle Kytölä, Mathlib and Batteries, and their
Apache 2.0 notices, is retained without modification of supplier bytes.
-/

import D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian
import D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTRelativeAmbientPreimage
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Batteries.Tactic.OpenPrivate

/-! Inserted-c0 Hermitian pairing on the original physical quotient and its image. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators TensorProduct

open private ghostR_b_zero from
  D5.S3.VertexAlgebra.Lattice.LatticeBRSTRelativeZeroMode

namespace D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalPairing

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents
open LatticeMatterGhostCoupling D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian LatticeBRST
open LatticeLightConeCoordinates LatticeLightConeCoordinates.NullFrame
open D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPerturbationFiltration
open LatticeRelativeBRSTCohomology.Number (N)

variable {D : LatticeData}

/-- The literal inserted-c0 value, initially only a form on original states.
No claim of descent on all unrestricted global cycles is made. -/
def inserted (x y : State D) : ℂ := Hmg x (ghostC D 0 y)

@[simp] theorem inserted_zero_left (y : State D) : inserted (0 : State D) y = 0 := by
  simp [inserted]

@[simp] theorem inserted_zero_right (x : State D) : inserted x 0 = 0 := by
  simp [inserted]

theorem inserted_add_left (x z y : State D) :
    inserted (x + z) y = inserted x y + inserted z y :=
  Hmg_add_left x z (ghostC D 0 y)

theorem inserted_add_right (x y z : State D) :
    inserted x (y + z) = inserted x y + inserted x z := by
  simp only [inserted, map_add, Hmg_add_right]

theorem inserted_smul_left (a : ℂ) (x y : State D) :
    inserted (a • x) y = star a * inserted x y :=
  Hmg_smul_left a x (ghostC D 0 y)

theorem inserted_smul_right (a : ℂ) (x y : State D) :
    inserted x (a • y) = a * inserted x y := by
  simp only [inserted, map_smul, Hmg_smul_right]

theorem inserted_sub_left (x z y : State D) :
    inserted (x - z) y = inserted x y - inserted z y :=
  Hmg_sub_left x z (ghostC D 0 y)

theorem inserted_sub_right (x y z : State D) :
    inserted x (y - z) = inserted x y - inserted x z := by
  simp only [inserted, map_sub, Hmg_sub_right]

/-- Since c0 is self-adjoint for the CURRENT ordinary Hg, this is ordinary
Hermitian symmetry, with no parity twist and no factor of i. -/
theorem inserted_hermitian (x y : State D) :
    inserted x y = star (inserted y x) := by
  calc
    inserted x y = Hmg (ghostC D 0 x) y := by
      simpa only [inserted, neg_zero] using (Hmg_ghostC 0 x y).symm
    _ = star (inserted y x) := Hmg_hermitian _ _

/-- Actual relative isotropy follows from CAR and the actual b0 adjoint. -/
theorem relative_isotropy (x y : State D)
    (hx : ghostB D 0 x = 0) (hy : ghostB D 0 y = 0) : Hmg x y = 0 := by
  have fix : ghostB D 0 (ghostC D 0 x) = x :=
    LatticeBRSTRelativeZeroMode.bZeroProjector_fix_of_ker D x hx
  calc
    Hmg x y = Hmg (ghostB D 0 (ghostC D 0 x)) y := by rw [fix]
    _ = Hmg (ghostC D 0 x) (ghostB D 0 y) := by
      simpa only [neg_zero] using Hmg_ghostB 0 (ghostC D 0 x) y
    _ = 0 := by rw [hy, Hmg_zero_right]

/-- Reuse of the actual finite R0/b0 commutator. R0 is even and preserves
the literal kernel; this is a proved property, not a supplied hypothesis. -/
theorem ghostR0_preserves_relative (y : State D) (hy : ghostB D 0 y = 0) :
    ghostB D 0 (ghostR D 0 y) = 0 := by
  have commute := LinearMap.congr_fun (sub_eq_zero.mp (ghostR_b_zero D)) y
  change ghostR D 0 (ghostB D 0 y) = ghostB D 0 (ghostR D 0 y) at commute
  rw [← commute, hy, map_zero]

variable (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)

include hHG hGH in
/-- Relative original-Q boundaries annihilate relative cycles in the left slot.
The Ward term R0 y is killed by DERIVED relative isotropy. -/
theorem inserted_boundary_left (u y : State D)
    (hu : ghostB D 0 u = 0) (hy : ghostB D 0 y = 0)
    (qy : totalCharge D H y = 0) : inserted (totalCharge D H u) y = 0 := by
  have ward := LinearMap.congr_fun (total_ward_c D H 0) y
  change totalCharge D H (ghostC D 0 y) +
    ghostC D 0 (totalCharge D H y) = ghostR D 0 y at ward
  have qc : totalCharge D H (ghostC D 0 y) = ghostR D 0 y := by
    simpa only [qy, map_zero, add_zero] using ward
  change Hmg (totalCharge D H u) (ghostC D 0 y) = 0
  rw [Hmg_totalCharge H hHG hGH, qc]
  exact relative_isotropy u (ghostR D 0 y) hu (ghostR0_preserves_relative y hy)

include hHG hGH in
/-- The genuine second-slot annihilation follows from ordinary Hermitian
symmetry, not an assumed projection or parity cancellation. -/
theorem inserted_boundary_right (x u : State D)
    (hx : ghostB D 0 x = 0) (hu : ghostB D 0 u = 0)
    (qx : totalCharge D H x = 0) : inserted x (totalCharge D H u) = 0 := by
  rw [inserted_hermitian, inserted_boundary_left H hHG hGH u x hu hx qx,
    star_zero]

end D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalPairing

namespace D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalPairing

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents
open LatticeMatterGhostCoupling D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian LatticeBRST
open LatticeLightConeCoordinates LatticeLightConeCoordinates.NullFrame
open D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPerturbationFiltration
open LatticeRelativeBRSTCohomology.Number (N)

variable {D : LatticeData}

/-- Actual degree-one relative cycles in the existing fixed sector.
The ambient space, charge, zero mode and integer number are unchanged. -/
def physicalCycles (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (beta : Charge D) (level : ℤ) : Submodule ℂ (fixedSector H beta level) where
  carrier := {x | totalCharge D H x.val = 0 ∧ ghostB D 0 x.val = 0 ∧
    N D x.val = x.val}
  zero_mem' := by
    change totalCharge D H (0 : State D) = 0 ∧ ghostB D 0 (0 : State D) = 0 ∧
      N D (0 : State D) = 0
    exact ⟨map_zero _, map_zero _, map_zero _⟩
  add_mem' := by
    rintro x y ⟨qx, bx, nx⟩ ⟨qy, by0, ny⟩
    exact ⟨by simpa only [Submodule.coe_add, map_add, qx, qy, add_zero],
      by simpa only [Submodule.coe_add, map_add, bx, by0, add_zero],
      by simpa only [Submodule.coe_add, map_add, nx, ny]⟩
  smul_mem' := by
    rintro a x ⟨qx, bx, nx⟩
    exact ⟨by simpa only [Submodule.coe_smul, map_smul, qx, smul_zero],
      by simpa only [Submodule.coe_smul, map_smul, bx, smul_zero],
      by simpa only [Submodule.coe_smul, map_smul, nx]⟩

-- Pin the inherited structures before quotient elaboration. Searching for
-- them through the nested fixed-sector carrier unfolds large proof data.
local instance physicalCyclesAddCommGroup
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (beta : Charge D) (level : ℤ) : AddCommGroup (physicalCycles H beta level) :=
  Submodule.addCommGroup _

local instance physicalCyclesModule
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (beta : Charge D) (level : ℤ) : Module ℂ (physicalCycles H beta level) :=
  Submodule.module _

/-- Inclusion in the existing unrestricted global original-Q kernel. -/
def cycleInclusion (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (beta : Charge D) (level : ℤ) :
    physicalCycles H beta level →ₗ[ℂ] LatticeBRSTCohomologyField.cycles D H where
  toFun x := ⟨x.val.val, x.property.1⟩
  map_add' x y := rfl
  map_smul' a x := rfl

/-- The original inserted form restricted to the actual physical cycles. -/
def physicalCycleForm (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (beta : Charge D) (level : ℤ) :
    physicalCycles H beta level →ₛₗ[starRingEnd ℂ]
      physicalCycles H beta level →ₗ[ℂ] ℂ where
  toFun x := {
    toFun y := inserted x.val.val y.val.val
    map_add' y z := inserted_add_right x.val.val y.val.val z.val.val
    map_smul' a y := inserted_smul_right a x.val.val y.val.val }
  map_add' x z := by
    apply LinearMap.ext
    intro y
    exact inserted_add_left x.val.val z.val.val y.val.val
  map_smul' a x := by
    apply LinearMap.ext
    intro y
    exact inserted_smul_left a x.val.val y.val.val

def physicalClass (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (beta : Charge D) (level : ℤ) (critical : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    physicalCycles H beta level →ₗ[ℂ]
      LatticeBRSTCohomologyField.Cohomology D H critical hHG hGH :=
  (LatticeBRSTCohomologyField.classOf D H critical hHG hGH).comp
    (cycleInclusion H beta level)

/-- COMAP of the EXISTING global boundaries. Its incoming original-Q
primitive is unrestricted: no relative, sector, or degree condition is added. -/
def physicalBoundaries (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (beta : Charge D) (level : ℤ) (critical : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    Submodule ℂ (physicalCycles H beta level) :=
  (LatticeBRSTCohomologyField.boundaries D H critical hHG hGH).comap
    (cycleInclusion H beta level)

theorem mem_physicalBoundaries
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (beta : Charge D) (level : ℤ) (critical : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (x : physicalCycles H beta level) :
    x ∈ physicalBoundaries H beta level critical hHG hGH ↔
      ∃ u : State D, totalCharge D H u = x.val.val :=
  LatticeBRSTCohomologyField.mem_boundaries D H critical hHG hGH
    (cycleInclusion H beta level x)

abbrev PhysicalQuotient (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (beta : Charge D) (level : ℤ) (critical : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :=
  @HasQuotient.Quotient (physicalCycles H beta level)
    (Submodule ℂ (physicalCycles H beta level))
    (Submodule.hasQuotient (R := ℂ) (M := physicalCycles H beta level))
    (physicalBoundaries H beta level critical hHG hGH)

local instance physicalQuotientAddCommGroup
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (beta : Charge D) (level : ℤ) (critical : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    AddCommGroup (PhysicalQuotient H beta level critical hHG hGH) :=
  Submodule.Quotient.addCommGroup _

local instance physicalQuotientModule
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (beta : Charge D) (level : ℤ) (critical : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    Module ℂ (PhysicalQuotient H beta level critical hHG hGH) :=
  Submodule.Quotient.module _

/-- The actual physical subquotient maps into the original global quotient. -/
def quotientToGlobal (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (beta : Charge D) (level : ℤ) (critical : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    PhysicalQuotient H beta level critical hHG hGH →ₗ[ℂ]
      LatticeBRSTCohomologyField.Cohomology D H critical hHG hGH :=
  (physicalBoundaries H beta level critical hHG hGH).liftQ
    (R := ℂ) (M := physicalCycles H beta level)
    (physicalClass H beta level critical hHG hGH) (by
      intro x hx
      apply LinearMap.mem_ker.mpr
      exact (Submodule.Quotient.mk_eq_zero
        (LatticeBRSTCohomologyField.boundaries D H critical hHG hGH)).mpr hx)

theorem quotientToGlobal_injective
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (beta : Charge D) (level : ℤ) (critical : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    Function.Injective (quotientToGlobal H beta level critical hHG hGH) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := (physicalBoundaries H beta level critical hHG hGH).mkQ_surjective x
  obtain ⟨b, rfl⟩ := (physicalBoundaries H beta level critical hHG hGH).mkQ_surjective y
  apply (Submodule.Quotient.eq (physicalBoundaries H beta level critical hHG hGH)).mpr
  change cycleInclusion H beta level (a - b) ∈
    LatticeBRSTCohomologyField.boundaries D H critical hHG hGH
  rw [map_sub]
  exact (Submodule.Quotient.eq
    (LatticeBRSTCohomologyField.boundaries D H critical hHG hGH)).mp hxy

/-- The literal image of physical cycles INSIDE the existing global quotient. -/
def physicalImage (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (beta : Charge D) (level : ℤ) (critical : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    Submodule ℂ (LatticeBRSTCohomologyField.Cohomology D H critical hHG hGH) :=
  LinearMap.range (physicalClass H beta level critical hHG hGH)

def imageClass (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (beta : Charge D) (level : ℤ) (critical : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    physicalCycles H beta level →ₗ[ℂ] physicalImage H beta level critical hHG hGH :=
  (physicalClass H beta level critical hHG hGH).rangeRestrict

def quotientToImage (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (beta : Charge D) (level : ℤ) (critical : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    PhysicalQuotient H beta level critical hHG hGH →ₗ[ℂ]
      physicalImage H beta level critical hHG hGH :=
  (quotientToGlobal H beta level critical hHG hGH).codRestrict
    (physicalImage H beta level critical hHG hGH) (by
      intro x
      obtain ⟨a, rfl⟩ :=
        (physicalBoundaries H beta level critical hHG hGH).mkQ_surjective x
      exact ⟨a, rfl⟩)

def physicalImageEquiv (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (beta : Charge D) (level : ℤ) (critical : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    PhysicalQuotient H beta level critical hHG hGH ≃ₗ[ℂ]
      physicalImage H beta level critical hHG hGH :=
  LinearEquiv.ofBijective (quotientToImage H beta level critical hHG hGH) (by
    constructor
    · intro x y hxy
      exact quotientToGlobal_injective H beta level critical hHG hGH
        (congrArg Subtype.val hxy)
    · rintro ⟨z, a, ha⟩
      refine ⟨(physicalBoundaries H beta level critical hHG hGH).mkQ a, ?_⟩
      exact Subtype.ext ha)

@[simp] theorem physicalImageEquiv_mk
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (beta : Charge D) (level : ℤ) (critical : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a : physicalCycles H beta level) :
    physicalImageEquiv H beta level critical hHG hGH
        ((physicalBoundaries H beta level critical hHG hGH).mkQ a) =
      imageClass H beta level critical hHG hGH a := rfl

section Descent

variable (F : NullFrame D) {t : ℕ} (B : Module.Basis (Fin t) ℂ F.K)
variable (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
variable (beta : Charge D) (level : ℤ) (hp : F.pPlus beta ≠ 0)
variable (critical : D.rank = 26)
variable (shell : groundEnergy beta + (level : ℂ) - 1 = 0)

include F B hp shell in
private theorem equal_class_left
    (a a' b : physicalCycles H beta level)
    (ha : physicalClass H beta level critical hHG hGH a =
      physicalClass H beta level critical hHG hGH a') :
    inserted a.val.val b.val.val = inserted a'.val.val b.val.val := by
  obtain ⟨u, huB, _huN, huQ⟩ :=
    (D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTRelativeAmbientPreimage.literal_physical_equality_iff_relative_preimage
      F B H hHG hGH beta level hp critical shell a.val a'.val
      a.property.1 a'.property.1 a.property.2.1 a'.property.2.1
      a.property.2.2 a'.property.2.2).mp ha
  have relative : ghostB D 0 u.val = 0 := huB
  have zero : inserted (a.val.val - a'.val.val) b.val.val = 0 := by
    rw [← huQ]
    exact inserted_boundary_left H hHG hGH u.val b.val.val relative
      b.property.2.1 b.property.1
  rw [inserted_sub_left] at zero
  exact sub_eq_zero.mp zero

include F B hp shell in
private theorem equal_class_right
    (a b b' : physicalCycles H beta level)
    (hb : physicalClass H beta level critical hHG hGH b =
      physicalClass H beta level critical hHG hGH b') :
    inserted a.val.val b.val.val = inserted a.val.val b'.val.val := by
  obtain ⟨u, huB, _huN, huQ⟩ :=
    (D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTRelativeAmbientPreimage.literal_physical_equality_iff_relative_preimage
      F B H hHG hGH beta level hp critical shell b.val b'.val
      b.property.1 b'.property.1 b.property.2.1 b'.property.2.1
      b.property.2.2 b'.property.2.2).mp hb
  have relative : ghostB D 0 u.val = 0 := huB
  have zero : inserted a.val.val (b.val.val - b'.val.val) = 0 := by
    rw [← huQ]
    exact inserted_boundary_right H hHG hGH a.val.val u.val a.property.2.1
      relative a.property.1
  rw [inserted_sub_right] at zero
  exact sub_eq_zero.mp zero

include F B hp shell in
/-- Two-slot representative independence for literal physical cycles whose
classes agree in the EXISTING unrestricted original-Q quotient. The relative
primitive is DERIVED by the pinned candidate for each class equality. -/
theorem inserted_representatives
    (a a' b b' : physicalCycles H beta level)
    (ha : physicalClass H beta level critical hHG hGH a =
      physicalClass H beta level critical hHG hGH a')
    (hb : physicalClass H beta level critical hHG hGH b =
      physicalClass H beta level critical hHG hGH b') :
    inserted a.val.val b.val.val = inserted a'.val.val b'.val.val := by
  calc
    inserted a.val.val b.val.val = inserted a'.val.val b.val.val :=
      equal_class_left F B H hHG hGH beta level hp critical shell a a' b ha
    _ = inserted a'.val.val b'.val.val :=
      equal_class_right F B H hHG hGH beta level hp critical shell a' b b' hb

end Descent

/-- The actual inserted-c0 sesquilinear form on the COMAP quotient. Both
kernel conditions required by liftQ₂ are proved using the literal global
class-equality criterion, retaining arbitrary ambient incoming boundaries. -/
def physicalQuotientForm
    (F : NullFrame D) {t : ℕ} (B : Module.Basis (Fin t) ℂ F.K)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (beta : Charge D) (level : ℤ) (hp : F.pPlus beta ≠ 0)
    (critical : D.rank = 26) (shell : groundEnergy beta + (level : ℂ) - 1 = 0) :
    PhysicalQuotient H beta level critical hHG hGH →ₛₗ[starRingEnd ℂ]
      PhysicalQuotient H beta level critical hHG hGH →ₗ[ℂ] ℂ :=
  LinearMap.liftQ₂ (R := ℂ) (R₂ := ℂ) (S := ℂ) (S₂ := ℂ)
    (M := physicalCycles H beta level) (N := physicalCycles H beta level) (P := ℂ)
    (ρ := starRingEnd ℂ) (σ := RingHom.id ℂ)
    (physicalBoundaries H beta level critical hHG hGH)
    (physicalBoundaries H beta level critical hHG hGH)
    (physicalCycleForm H beta level)
    (by
      intro a ha
      apply LinearMap.mem_ker.mpr
      apply LinearMap.ext
      intro b
      change inserted a.val.val b.val.val = 0
      have ha0 : physicalClass H beta level critical hHG hGH a = 0 :=
        (Submodule.Quotient.mk_eq_zero
          (LatticeBRSTCohomologyField.boundaries D H critical hHG hGH)).mpr ha
      have eq := inserted_representatives F B H hHG hGH beta level hp critical shell
        a 0 b b (by simpa only [map_zero] using ha0) rfl
      simpa only [Submodule.coe_zero, inserted_zero_left] using eq)
    (by
      intro b hb
      apply LinearMap.mem_ker.mpr
      apply LinearMap.ext
      intro a
      change inserted a.val.val b.val.val = 0
      have hb0 : physicalClass H beta level critical hHG hGH b = 0 :=
        (Submodule.Quotient.mk_eq_zero
          (LatticeBRSTCohomologyField.boundaries D H critical hHG hGH)).mpr hb
      have eq := inserted_representatives F B H hHG hGH beta level hp critical shell
        a a b 0 rfl (by simpa only [map_zero] using hb0)
      simpa only [Submodule.coe_zero, inserted_zero_right] using eq)

theorem physicalQuotientForm_hermitian
    (F : NullFrame D) {t : ℕ} (B : Module.Basis (Fin t) ℂ F.K)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (beta : Charge D) (level : ℤ) (hp : F.pPlus beta ≠ 0)
    (critical : D.rank = 26) (shell : groundEnergy beta + (level : ℂ) - 1 = 0)
    (x y : PhysicalQuotient H beta level critical hHG hGH) :
    physicalQuotientForm F B H hHG hGH beta level hp critical shell x y =
      star (physicalQuotientForm F B H hHG hGH beta level hp critical shell y x) := by
  obtain ⟨a, rfl⟩ := (physicalBoundaries H beta level critical hHG hGH).mkQ_surjective x
  obtain ⟨b, rfl⟩ := (physicalBoundaries H beta level critical hHG hGH).mkQ_surjective y
  exact inserted_hermitian a.val.val b.val.val

/-- The descended Hermitian form on the literal injective physical image
inside the existing global Cohomology, transported by the proved equivalence. -/
def physicalImageForm
    (F : NullFrame D) {t : ℕ} (B : Module.Basis (Fin t) ℂ F.K)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (beta : Charge D) (level : ℤ) (hp : F.pPlus beta ≠ 0)
    (critical : D.rank = 26) (shell : groundEnergy beta + (level : ℂ) - 1 = 0) :
    physicalImage H beta level critical hHG hGH →ₛₗ[starRingEnd ℂ]
      physicalImage H beta level critical hHG hGH →ₗ[ℂ] ℂ := by
  let e := physicalImageEquiv H beta level critical hHG hGH
  let q := physicalQuotientForm F B H hHG hGH beta level hp critical shell
  exact (q.comp e.symm.toLinearMap).compl₂ e.symm.toLinearMap

@[simp] theorem physicalImageForm_imageClass
    (F : NullFrame D) {t : ℕ} (B : Module.Basis (Fin t) ℂ F.K)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (beta : Charge D) (level : ℤ) (hp : F.pPlus beta ≠ 0)
    (critical : D.rank = 26) (shell : groundEnergy beta + (level : ℂ) - 1 = 0)
    (a b : physicalCycles H beta level) :
    physicalImageForm F B H hHG hGH beta level hp critical shell
        (imageClass H beta level critical hHG hGH a)
        (imageClass H beta level critical hHG hGH b) =
      Hmg a.val.val (ghostC D 0 b.val.val) := by
  let e := physicalImageEquiv H beta level critical hHG hGH
  have recover (c : physicalCycles H beta level) :
      e.symm (imageClass H beta level critical hHG hGH c) =
        (physicalBoundaries H beta level critical hHG hGH).mkQ c := by
    rw [← physicalImageEquiv_mk]
    exact e.symm_apply_apply _
  change physicalQuotientForm F B H hHG hGH beta level hp critical shell
    (e.symm (imageClass H beta level critical hHG hGH a))
    (e.symm (imageClass H beta level critical hHG hGH b)) = _
  rw [recover a, recover b]
  rfl


/-- Recovery from ANY two actual physical representatives of two image
elements; the representative equalities are equalities in the original
global quotient and place no conditions on their ambient incoming witnesses. -/
theorem physicalImageForm_recovery
    (F : NullFrame D) {t : ℕ} (B : Module.Basis (Fin t) ℂ F.K)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (beta : Charge D) (level : ℤ) (hp : F.pPlus beta ≠ 0)
    (critical : D.rank = 26) (shell : groundEnergy beta + (level : ℂ) - 1 = 0)
    (x y : physicalImage H beta level critical hHG hGH)
    (a b : physicalCycles H beta level)
    (ha : physicalClass H beta level critical hHG hGH a = x.val)
    (hb : physicalClass H beta level critical hHG hGH b = y.val) :
    physicalImageForm F B H hHG hGH beta level hp critical shell x y =
      Hmg a.val.val (ghostC D 0 b.val.val) := by
  have hx : x = imageClass H beta level critical hHG hGH a := Subtype.ext ha.symm
  have hy : y = imageClass H beta level critical hHG hGH b := Subtype.ext hb.symm
  rw [hx, hy, physicalImageForm_imageClass]

end D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalPairing
