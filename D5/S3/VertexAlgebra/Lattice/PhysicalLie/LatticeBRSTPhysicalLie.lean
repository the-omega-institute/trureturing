/- GID: D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalLie
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalLie
   mirror-E: none(waiver:original-global-physical-lie)
   anchors: []
   utility: none
   digest: Actual unsigned degree-one current and literal relative image in global cohomology. -/

/- Original source proof on the original critical Q quotient. The frozen BV
defect, global boundary descent, ghost grading and field suppliers retain
their original author attributions. No pairing, positivity, no-ghost theorem,
kernel verification or full string-theory completion is claimed here.
proof_shape: current_grade, current_skew, current_leftLeibniz,
  physicalImage_closed, physicalLieSubalgebra: content
admission_basis: escape-witness
escape_witness: Original N covariance fixes the degree, an exact vector
zero-mode calculation proves Jacobi, and actual CAR closes each literal
relative representative before the unrestricted global quotient is taken.
-/

import D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostNumberCovariance
import D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTCurrentIdentities
import Mathlib.Algebra.Lie.Subalgebra

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalLie

open LatticeGeneratingFieldLocality (LatticeData)
open LatticeMatterGhostCoupling (State ghostB)
open LatticeMatterGhostDegree (tensorNumber)
open LatticeBRSTCohomologyField
open LatticeBRSTCohomologyBVSecondOrder (descentCurrent cohomologyCurrent Delta_product_defect)
open LatticeBRSTZeroEnergyReduction (Delta cycleDelta totalL0 P0 fullBasis FullLabel)
open LatticeBRSTCohomologyGhostGrading (number grade cycleNumber)
open LatticeMatterGhostNumberCovariance (current_number number_one_parity)
open D5.S3.Quantum.Fermionic.CountableOccupationFock (ket)
open private current_cycle cycleCurrent current_classOf b_parity
  current_left_boundary current_right_boundary from
  D5.S3.VertexAlgebra.Lattice.LatticeBRSTCohomologyBVSecondOrder
open private number_classOf from
  D5.S3.VertexAlgebra.Lattice.LatticeBRSTCohomologyGhostGrading
open private fullBasis_apply energyWeight_basis from
  D5.S3.VertexAlgebra.Lattice.LatticeBRSTZeroEnergyReduction
open private parity_ket from D5.S3.Quantum.Fermionic.CountableOccupationFock

noncomputable section

variable (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
  (h26 : D.rank = 26)
  (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
  (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1)

local notation "C" => Cohomology D H h26 hHG hGH
local notation "J" => cohomologyCurrent D H h26 hHG hGH
local notation "P" => product D H h26 hHG hGH
local notation "δ" => Delta D H h26 hHG hGH
local notation "π" => parity D H h26 hHG hGH
local notation "cl" => classOf D H h26 hHG hGH

/-- The exact original native integer degree, on the EXISTING global quotient. -/
theorem current_grade (a b : C) (p q : ℤ)
    (ha : a ∈ grade D H h26 hHG hGH p) (hb : b ∈ grade D H h26 hHG hGH q) :
    J a b ∈ grade D H h26 hHG hGH (p+q-1) := by
  obtain ⟨x, rfl, hx⟩ :=
    LatticeBRSTCohomologyGhostGrading.homogeneous_cycle_lift D H h26 hHG hGH p a ha
  obtain ⟨y, rfl, hy⟩ :=
    LatticeBRSTCohomologyGhostGrading.homogeneous_cycle_lift D H h26 hHG hGH q b hb
  rw [current_classOf, LatticeBRSTCohomologyGhostGrading.grade, Module.End.mem_eigenspace_iff, number_classOf, ← map_smul]
  apply congrArg cl
  apply Subtype.ext
  exact current_number D x y p q hx hy

private theorem grade_one_parity (a : C) (ha : a ∈ grade D H h26 hHG hGH 1) :
    π a = -a := by
  obtain ⟨x, rfl, hx⟩ :=
    LatticeBRSTCohomologyGhostGrading.homogeneous_cycle_lift D H h26 hHG hGH 1 a ha
  rw [parity_classOf, ← map_neg]
  apply congrArg cl
  apply Subtype.ext
  exact number_one_parity D x (by simpa only [Int.cast_one, one_smul] using hx)

private theorem parity_P0 (x : State D) :
    LatticeMatterGhostStateField.parity D (P0 D x) =
      P0 D (LatticeMatterGhostStateField.parity D x) := by
  have pb (i : FullLabel D) : LatticeMatterGhostStateField.parity D (fullBasis D i) =
      (-1:ℂ)^i.2.card • fullBasis D i := by
    simp [fullBasis_apply, LatticeMatterGhostStateField.parity,
      TensorProduct.map_tmul, parity_ket, TensorProduct.tmul_smul]
  have comm : LatticeMatterGhostStateField.parity D * P0 D =
      P0 D * LatticeMatterGhostStateField.parity D := by
    apply (fullBasis D).ext
    intro i
    simp only [Module.End.mul_apply, P0, energyWeight_basis, pb, map_smul, smul_smul]
    rw [mul_comm]
  exact LinearMap.congr_fun comm x

private theorem delta_parity (a : C) : π (δ a) = -δ (π a) := by
  obtain ⟨x, rfl⟩ := classOf_surjective D H h26 hHG hGH a
  change cl (cycleParity D H (cycleDelta D H h26 hHG hGH x)) =
    -cl (cycleDelta D H h26 hHG hGH (cycleParity D H x))
  rw [← map_neg]
  apply congrArg cl
  apply Subtype.ext
  change LatticeMatterGhostStateField.parity D (ghostB D 0 (P0 D x)) =
    -ghostB D 0 (P0 D (LatticeMatterGhostStateField.parity D x))
  rw [b_parity, parity_P0]

private theorem odd_defect (a b : C) (ha : π a = -a) :
    J a b = δ (P a b) - P (δ a) b + P a (δ b) := by
  have h := Delta_product_defect D H h26 hHG hGH a b
  rw [ha, map_neg, LinearMap.neg_apply, sub_neg_eq_add] at h
  exact h.symm

/-- Antisymmetry of the literal UNSIGNED current, on odd classes. -/
theorem current_skew (a b : C) (ha : π a = -a) (hb : π b = -b) :
    J a b = -J b a := by
  have da : π (δ a) = δ a := by rw [delta_parity, ha, map_neg, neg_neg]
  have db : π (δ b) = δ b := by rw [delta_parity, hb, map_neg, neg_neg]
  have ab : P a b = -P b a := by
    simpa only [pow_one, Nat.one_mul, neg_one_smul] using
      product_supercomm D H h26 hHG hGH a b 1 1
        (by simpa only [pow_one, neg_one_smul] using ha)
        (by simpa only [pow_one, neg_one_smul] using hb)
  have adb : P a (δ b) = P (δ b) a := by
    simpa only [Nat.mul_zero, pow_zero, one_smul] using
      product_supercomm D H h26 hHG hGH a (δ b) 1 0
        (by simpa only [pow_one, neg_one_smul] using ha)
        (by simpa only [pow_zero, one_smul] using db)
  have bda : P b (δ a) = P (δ a) b := by
    simpa only [Nat.mul_zero, pow_zero, one_smul] using
      product_supercomm D H h26 hHG hGH b (δ a) 1 0
        (by simpa only [pow_one, neg_one_smul] using hb)
        (by simpa only [pow_zero, one_smul] using da)
  rw [odd_defect D H h26 hHG hGH a b ha, odd_defect D H h26 hHG hGH b a hb,
    ab, map_neg, adb, bda]
  abel

/-- Full vector left-Leibniz; the third class need not be homogeneous. -/
theorem current_leftLeibniz (a b c : C) (ha : π a = -a) (hb : π b = -b) :
    J a (J b c) = J (J a b) c + J b (J a c) := by
  obtain ⟨x, rfl, hx⟩ := LatticeBRSTCohomologyField.homogeneous_cycle_lift
    D H h26 hHG hGH a 1 (by simpa only [pow_one, neg_one_smul] using ha)
  obtain ⟨y, rfl, hy⟩ := LatticeBRSTCohomologyField.homogeneous_cycle_lift
    D H h26 hHG hGH b 1 (by simpa only [pow_one, neg_one_smul] using hb)
  obtain ⟨z, rfl⟩ := classOf_surjective D H h26 hHG hGH c
  have hc : cycleCurrent D H hHG hGH x (cycleCurrent D H hHG hGH y z) =
      cycleCurrent D H hHG hGH (cycleCurrent D H hHG hGH x y) z +
        cycleCurrent D H hHG hGH y (cycleCurrent D H hHG hGH x z) := by
    apply Subtype.ext
    exact LatticeBRSTCurrentIdentities.current_leftLeibniz D x y z
      (by simpa only [pow_one, neg_one_smul] using hx)
      (by simpa only [pow_one, neg_one_smul] using hy)
  simp only [current_classOf]
  rw [← map_add]
  exact congrArg cl hc

/-- Ghost-one cohomology is the native eigenspace INSIDE the original global quotient. -/
abbrev DegreeOne := grade D H h26 hHG hGH 1

instance degreeOneLieRing : LieRing (DegreeOne D H h26 hHG hGH) where
  bracket a b := ⟨J a b, by
    simpa only [show (1+1-1:ℤ) = 1 by omega] using
      current_grade D H h26 hHG hGH a b 1 1 a.property b.property⟩
  add_lie a b c := by
    apply Subtype.ext
    exact LinearMap.congr_fun (map_add J (a:C) (b:C)) c
  lie_add a b c := by
    apply Subtype.ext
    exact map_add (J a) (b:C) (c:C)
  lie_self a := by
    apply Subtype.ext
    have h := current_skew D H h26 hHG hGH a a
      (grade_one_parity D H h26 hHG hGH a a.property)
      (grade_one_parity D H h26 hHG hGH a a.property)
    have hz : (2:ℂ) • J a a = 0 := by rw [two_smul]; exact eq_neg_iff_add_eq_zero.mp h
    exact (smul_eq_zero.mp hz).resolve_left (by norm_num)
  leibniz_lie a b c := by
    apply Subtype.ext
    exact current_leftLeibniz D H h26 hHG hGH a b c
      (grade_one_parity D H h26 hHG hGH a a.property)
      (grade_one_parity D H h26 hHG hGH b b.property)

instance degreeOneLieAlgebra : LieAlgebra ℂ (DegreeOne D H h26 hHG hGH) where
  lie_smul t a b := by
    apply Subtype.ext
    exact map_smul (J a) t (b:C)

/-- A full vector cyclic Jacobi equality in the global quotient. -/
theorem current_jacobi (a b c : C)
    (ha : a ∈ grade D H h26 hHG hGH 1)
    (hb : b ∈ grade D H h26 hHG hGH 1)
    (hc : c ∈ grade D H h26 hHG hGH 1) :
    J a (J b c) + J b (J c a) + J c (J a b) = 0 := by
  have h := current_leftLeibniz D H h26 hHG hGH a b c
    (grade_one_parity D H h26 hHG hGH a ha)
    (grade_one_parity D H h26 hHG hGH b hb)
  have bc := current_skew D H h26 hHG hGH c a
    (grade_one_parity D H h26 hHG hGH c hc)
    (grade_one_parity D H h26 hHG hGH a ha)
  have hab : J a b ∈ grade D H h26 hHG hGH 1 := by
    simpa using current_grade D H h26 hHG hGH a b 1 1 ha hb
  have ca := current_skew D H h26 hHG hGH c (J a b)
    (grade_one_parity D H h26 hHG hGH c hc)
    (grade_one_parity D H h26 hHG hGH (J a b) hab)
  rw [h, bc, map_neg, ca]
  abel

/-- Literal original states, all original charges, with EACH physical equation. -/
def physicalStates : Submodule ℂ (State D) where
  carrier := {x | LatticeBRST.totalCharge D H x = 0 ∧ ghostB D 0 x = 0 ∧
    tensorNumber D x = x ∧ totalL0 D H x = 0}
  zero_mem' := by exact ⟨map_zero _, map_zero _, map_zero _, map_zero _⟩
  add_mem' := by
    rintro x y ⟨qx,bx,nx,lx⟩ ⟨qy,by0,ny,ly⟩
    simp only [Set.mem_setOf_eq, map_add, qx, qy, bx, by0, nx, ny, lx, ly, add_zero,
      and_self]
  smul_mem' := by
    rintro t x ⟨qx,bx,nx,lx⟩
    simp only [Set.mem_setOf_eq, map_smul, qx, bx, nx, lx, smul_zero, and_self]

include hHG hGH in
/-- Closure is proved for the literal representative, before any quotient. -/
theorem physicalStates_current (x y : physicalStates D H) :
    descentCurrent D x y ∈ physicalStates D H := by
  let xc : cycles D H := ⟨x,x.property.1⟩
  let yc : cycles D H := ⟨y,y.property.1⟩
  refine ⟨current_cycle D H hHG hGH xc yc,
    LatticeBRSTCurrentIdentities.current_b0 D x y x.property.2.1 y.property.2.1, ?_, ?_⟩
  · simpa only [show (1+1-1:ℤ) = 1 by omega, Int.cast_one, one_smul] using
      current_number D x y 1 1
        (by simpa only [Int.cast_one, one_smul] using x.property.2.2.1)
        (by simpa only [Int.cast_one, one_smul] using y.property.2.2.1)
  · rw [LatticeBRSTCurrentIdentities.current_L0 D H hHG hGH,
      x.property.2.2.2, y.property.2.2.2]
    simp

private def physicalCycleInclusion : physicalStates D H →ₗ[ℂ] cycles D H where
  toFun x := ⟨x,x.property.1⟩
  map_add' x y := rfl
  map_smul' t x := rfl

def physicalClass : physicalStates D H →ₗ[ℂ] C :=
  (cl).comp (physicalCycleInclusion D H)

/-- LITERAL image under the existing classOf; incoming boundaries remain ALL State D. -/
def physicalImage : Submodule ℂ C := LinearMap.range (physicalClass D H h26 hHG hGH)

private theorem physicalImage_grade : physicalImage D H h26 hHG hGH ≤ grade D H h26 hHG hGH 1 := by
  rintro a ⟨x,rfl⟩
  change cl (physicalCycleInclusion D H x) ∈ grade D H h26 hHG hGH 1
  rw [LatticeBRSTCohomologyGhostGrading.grade, Module.End.mem_eigenspace_iff, number_classOf]
  simp only [Int.cast_one, one_smul]
  apply congrArg cl
  apply Subtype.ext
  exact x.property.2.2.1

/-- Restriction of the ALREADY descended current to the literal image. -/
theorem physicalImage_closed (a b : C)
    (ha : a ∈ physicalImage D H h26 hHG hGH)
    (hb : b ∈ physicalImage D H h26 hHG hGH) :
    J a b ∈ physicalImage D H h26 hHG hGH := by
  obtain ⟨x,rfl⟩ := ha
  obtain ⟨y,rfl⟩ := hb
  refine ⟨⟨descentCurrent D x y, physicalStates_current D H hHG hGH x y⟩, ?_⟩
  rfl

/-- The literal image subtype itself carries the restricted ORIGINAL current.
No operation is transported along an equivalence or through a new quotient. -/
instance physicalImageLieRing : LieRing (physicalImage D H h26 hHG hGH) where
  bracket a b := ⟨J a b,physicalImage_closed D H h26 hHG hGH a b a.property b.property⟩
  add_lie a b c := by
    apply Subtype.ext
    exact LinearMap.congr_fun (map_add J (a:C) (b:C)) c
  lie_add a b c := by
    apply Subtype.ext
    exact map_add (J a) (b:C) (c:C)
  lie_self a := by
    apply Subtype.ext
    let a1 : DegreeOne D H h26 hHG hGH :=
      ⟨a,physicalImage_grade D H h26 hHG hGH a.property⟩
    exact congrArg (fun z : DegreeOne D H h26 hHG hGH => (z:C)) (LieRing.lie_self a1)
  leibniz_lie a b c := by
    apply Subtype.ext
    let a1 : DegreeOne D H h26 hHG hGH :=
      ⟨a,physicalImage_grade D H h26 hHG hGH a.property⟩
    let b1 : DegreeOne D H h26 hHG hGH :=
      ⟨b,physicalImage_grade D H h26 hHG hGH b.property⟩
    let c1 : DegreeOne D H h26 hHG hGH :=
      ⟨c,physicalImage_grade D H h26 hHG hGH c.property⟩
    exact congrArg (fun z : DegreeOne D H h26 hHG hGH => (z:C))
      (LieRing.leibniz_lie a1 b1 c1)

instance physicalImageLieAlgebra : LieAlgebra ℂ (physicalImage D H h26 hHG hGH) where
  lie_smul t a b := by
    apply Subtype.ext
    exact map_smul (J a) t (b:C)

/-- This Lie subalgebra has exactly the literal global-image predicate.
The ambient Lie algebra is native grade ONE in the original GLOBAL quotient. -/
def physicalLieSubalgebra : LieSubalgebra ℂ (DegreeOne D H h26 hHG hGH) where
  toSubmodule := (physicalImage D H h26 hHG hGH).comap (grade D H h26 hHG hGH 1).subtype
  lie_mem' := by
    intro a b ha hb
    exact physicalImage_closed D H h26 hHG hGH a b ha hb

end
end D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalLie
