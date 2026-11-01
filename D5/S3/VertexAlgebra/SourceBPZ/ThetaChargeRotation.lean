/- GID: D5/S3/VertexAlgebra/SourceBPZ/ThetaChargeRotation
   generality: I
   mirror-B: none(waiver:no-B-plane-mirror-for-source-module)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A finite charge character produces a genuine ZMod-three representation on every energy grade and is inverted by the lattice reflection. -/

import D5.S3.VertexAlgebra.SourceBPZ.ThetaGradeRepresentation
import Mathlib.Algebra.Group.AddChar
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.SourceBPZ.ThetaChargeRotation

open D5.S3.VertexAlgebra.SourceBPZ
open LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeInvolution
open LatticeAllStateField
open ThetaReflectionAction
open ThetaGradeTraceSplit
open ThetaGradeIntertwiner
open ThetaGradeRepresentation
open Representation

/-- A multiplicative realization of the additive third roots of unity. -/
abbrev ChargePhase := Multiplicative (ZMod 3) →* ℂˣ

/-- The scalar by which a charge character acts on a lattice basis vector. -/
def chargePhaseScalar (phase : ChargePhase) (z : ZMod 3) : ℂ :=
  (phase (Multiplicative.ofAdd z) : ℂ)

@[simp] theorem chargePhaseScalar_zero (phase : ChargePhase) :
    chargePhaseScalar phase 0 = 1 := by
  simp [chargePhaseScalar]

theorem chargePhaseScalar_add (phase : ChargePhase) (x y : ZMod 3) :
    chargePhaseScalar phase (x + y) =
      chargePhaseScalar phase x * chargePhaseScalar phase y := by
  simp only [chargePhaseScalar, ← Units.val_mul]
  rw [← phase.map_mul]
  rfl

theorem chargePhaseScalar_neg (phase : ChargePhase) (x : ZMod 3) :
    chargePhaseScalar phase (-x) = (chargePhaseScalar phase x)⁻¹ := by
  simp only [chargePhaseScalar]
  rw [show Multiplicative.ofAdd (-x) = (Multiplicative.ofAdd x)⁻¹ by rfl,
    phase.map_inv]
  exact Units.val_inv_eq_inv_val _

/-- The charge rotation on the full lattice carrier. -/
def chargeRotation (D : LatticeData) (ell : Charge D →+ ZMod 3)
    (phase : ChargePhase) (g : Multiplicative (ZMod 3)) : Module.End ℂ (Carrier D) :=
  (carrierBasis D).constr ℂ (fun a =>
    chargePhaseScalar phase (g.toAdd * ell a.1) • carrierBasis D a)

@[simp] theorem chargeRotation_on_basis (D : LatticeData) (ell : Charge D →+ ZMod 3)
    (phase : ChargePhase) (g : Multiplicative (ZMod 3)) (a : Label D) :
    chargeRotation D ell phase g (carrierBasis D a) =
      chargePhaseScalar phase (g.toAdd * ell a.1) • carrierBasis D a := by
  exact Module.Basis.constr_basis (carrierBasis D) ℂ _ a

/-- Charge rotation preserves every energy grade. -/
theorem chargeRotation_preserves_grade (D : LatticeData) (ell : Charge D →+ ZMod 3)
    (phase : ChargePhase) (g : Multiplicative (ZMod 3)) (n : ℤ)
    (v : Carrier D) (hv : v ∈ grade D n) :
    chargeRotation D ell phase g v ∈ grade D n := by
  rw [grade_eq_span] at hv
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
  · rintro x ⟨a, ha, rfl⟩
    rw [chargeRotation_on_basis]
    have ha' : carrierBasis D a ∈ grade D n := by
      rw [grade_eq_span]
      exact Submodule.subset_span ⟨a, ha, rfl⟩
    exact (grade D n).smul_mem _ ha'
  · exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    simpa only [map_add] using (grade D n).add_mem hx hy
  · intro c x _ hx
    simpa only [map_smul] using (grade D n).smul_mem c hx

private theorem chargeRotation_one (D : LatticeData) (ell : Charge D →+ ZMod 3)
    (phase : ChargePhase) :
    chargeRotation D ell phase 1 = LinearMap.id := by
  apply (carrierBasis D).ext
  intro a
  rw [chargeRotation_on_basis]
  simp [chargePhaseScalar]

private theorem chargeRotation_mul (D : LatticeData) (ell : Charge D →+ ZMod 3)
    (phase : ChargePhase) (g h : Multiplicative (ZMod 3)) :
    chargeRotation D ell phase (g * h) =
      (chargeRotation D ell phase g).comp (chargeRotation D ell phase h) := by
  apply (carrierBasis D).ext
  intro a
  simp only [chargeRotation_on_basis, LinearMap.comp_apply, map_smul,
    smul_smul]
  congr 1
  change chargePhaseScalar phase ((g.toAdd + h.toAdd) * ell a.1) = _
  rw [← chargePhaseScalar_add]
  congr 1
  simp [add_mul, add_comm]

private theorem theta_on_basis (D : LatticeData) (a : Label D) :
    theta D (carrierBasis D a) =
      ((-1 : ℂ) ^ (occurrences D a.2).length) •
        carrierBasis D (-a.1, a.2) := by
  change thetaLinear D (carrierBasis D a) = _
  rw [carrierBasis_apply, theta_single, sigma_monomial, carrierBasis_apply,
    ← Finsupp.smul_single]

theorem chargeRotation_theta_conj (D : LatticeData) (ell : Charge D →+ ZMod 3)
    (phase : ChargePhase) (g : Multiplicative (ZMod 3)) :
    ((theta D).toLinearMap.comp (chargeRotation D ell phase g)).comp
        (theta D).toLinearMap =
      chargeRotation D ell phase g⁻¹ := by
  apply (carrierBasis D).ext
  intro a
  change theta D (chargeRotation D ell phase g (theta D (carrierBasis D a))) = _
  rw [theta_on_basis, (chargeRotation D ell phase g).map_smul,
    chargeRotation_on_basis, (theta D).map_smul, (theta D).map_smul,
    theta_on_basis]
  rw [smul_smul, smul_smul]
  have hocc : (occurrences D a.2).length =
      (occurrences D a.2).length := rfl
  have hphase :
      chargePhaseScalar phase (g.toAdd * ell a.1 * -1) =
        (chargePhaseScalar phase (g.toAdd * ell a.1))⁻¹ := by
    simpa using (chargePhaseScalar_neg phase (g.toAdd * ell a.1))
  have harg :
      (g⁻¹).toAdd * ell a.1 = g.toAdd * ell a.1 * -1 := by
    simp [mul_neg, neg_mul, mul_comm]
  rw [chargeRotation_on_basis]
  simp only [Prod.fst, Prod.snd, neg_neg]
  rw [map_neg]
  simp only [mul_neg]
  rw [harg]
  have hphase' :
      chargePhaseScalar phase (-(g.toAdd * ell a.1)) =
        (chargePhaseScalar phase (g.toAdd * ell a.1))⁻¹ := by
    simpa using hphase
  rw [hphase']
  have hs : ((-1 : ℂ) ^ (occurrences D a.2).length) *
      ((-1 : ℂ) ^ (occurrences D a.2).length) = 1 := by
    rw [← mul_pow]
    simp
  congr 1
  calc
    (-1 : ℂ) ^ (occurrences D a.2).length *
        (chargePhaseScalar phase (g.toAdd * ell a.1))⁻¹ *
          (-1 : ℂ) ^ (occurrences D a.2).length =
      (chargePhaseScalar phase (g.toAdd * ell a.1))⁻¹ *
        (((-1 : ℂ) ^ (occurrences D a.2).length) *
          ((-1 : ℂ) ^ (occurrences D a.2).length)) := by ring
    _ = (chargePhaseScalar phase (g.toAdd * ell a.1))⁻¹ := by rw [hs, mul_one]
    _ = chargePhaseScalar phase (g.toAdd * ell a.1 * -1) := hphase.symm

/-- The charge rotation restricted to one finite energy grade. -/
def gradeChargeRotation (D : LatticeData) (ell : Charge D →+ ZMod 3)
    (phase : ChargePhase) (n : ℤ) (g : Multiplicative (ZMod 3)) :
    Module.End ℂ (grade D n) :=
  (chargeRotation D ell phase g).domRestrict (grade D n) |>.codRestrict
    (grade D n) (fun v => chargeRotation_preserves_grade D ell phase g n v.1 v.2)

@[simp] theorem gradeChargeRotation_val (D : LatticeData) (ell : Charge D →+ ZMod 3)
    (phase : ChargePhase) (n : ℤ) (g : Multiplicative (ZMod 3)) (v : grade D n) :
    (gradeChargeRotation D ell phase n g v).1 =
      chargeRotation D ell phase g v.1 := rfl

theorem gradeChargeRotation_theta_conj (D : LatticeData)
    (ell : Charge D →+ ZMod 3) (phase : ChargePhase) (n : ℤ)
    (g : Multiplicative (ZMod 3)) :
    ((gradeTheta D n).comp (gradeChargeRotation D ell phase n g)).comp
        (gradeTheta D n) =
      gradeChargeRotation D ell phase n g⁻¹ := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  change theta D (chargeRotation D ell phase g
      (theta D v.1)) = chargeRotation D ell phase g⁻¹ v.1
  exact congrArg (fun f : Carrier D →ₗ[ℂ] Carrier D => f v.1)
    (chargeRotation_theta_conj D ell phase g)


/-- The charge rotations form a representation of the third-root group. -/
def gradeChargeRotationRepresentation (D : LatticeData) (ell : Charge D →+ ZMod 3)
    (phase : ChargePhase) (n : ℤ) :
    Representation ℂ (Multiplicative (ZMod 3)) (grade D n) where
  toFun g := gradeChargeRotation D ell phase n g
  map_one' := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change chargeRotation D ell phase 1 v.1 = v.1
    rw [chargeRotation_one]
    rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change chargeRotation D ell phase (g * h) v.1 =
      ((chargeRotation D ell phase g).comp
        (chargeRotation D ell phase h)) v.1
    rw [chargeRotation_mul]

private theorem gradeChargeRotation_add (D : LatticeData)
    (ell : Charge D →+ ZMod 3) (phase : ChargePhase) (n : ℤ)
    (i j : ZMod 3) :
    gradeChargeRotation D ell phase n (Multiplicative.ofAdd (i + j)) =
      (gradeChargeRotation D ell phase n (Multiplicative.ofAdd i)).comp
        (gradeChargeRotation D ell phase n (Multiplicative.ofAdd j)) := by
  change gradeChargeRotation D ell phase n
      (Multiplicative.ofAdd i * Multiplicative.ofAdd j) = _
  exact (gradeChargeRotationRepresentation D ell phase n).map_mul _ _

private theorem gradeChargeRotation_zero (D : LatticeData)
    (ell : Charge D →+ ZMod 3) (phase : ChargePhase) (n : ℤ) :
    gradeChargeRotation D ell phase n (Multiplicative.ofAdd 0) = LinearMap.id := by
  change gradeChargeRotation D ell phase n 1 = LinearMap.id
  exact (gradeChargeRotationRepresentation D ell phase n).map_one

private theorem gradeChargeRotation_theta_move (D : LatticeData)
    (ell : Charge D →+ ZMod 3) (phase : ChargePhase) (n : ℤ)
    (i : ZMod 3) :
    (gradeTheta D n).comp
        (gradeChargeRotation D ell phase n (Multiplicative.ofAdd i)) =
      (gradeChargeRotation D ell phase n (Multiplicative.ofAdd (-i))).comp
        (gradeTheta D n) := by
  apply LinearMap.ext
  intro v
  have h := congrArg
    (fun q : grade D n →ₗ[ℂ] grade D n => q (gradeTheta D n v))
    (gradeChargeRotation_theta_conj D ell phase n
      (Multiplicative.ofAdd i))
  simpa [LinearMap.comp_apply, gradeTheta_sq] using h

private theorem gradeChargeRotation_apply_add (D : LatticeData)
    (ell : Charge D →+ ZMod 3) (phase : ChargePhase) (n : ℤ)
    (i j : ZMod 3) (v : grade D n) :
    gradeChargeRotation D ell phase n (Multiplicative.ofAdd (i + j)) v =
      gradeChargeRotation D ell phase n (Multiplicative.ofAdd i)
        (gradeChargeRotation D ell phase n (Multiplicative.ofAdd j) v) := by
  have h := congrArg (fun f : grade D n →ₗ[ℂ] grade D n => f v)
    (gradeChargeRotation_add D ell phase n i j)
  simpa [LinearMap.comp_apply] using h

private theorem gradeChargeRotation_theta_move_apply (D : LatticeData)
    (ell : Charge D →+ ZMod 3) (phase : ChargePhase) (n : ℤ)
    (i : ZMod 3) (v : grade D n) :
    gradeTheta D n
        (gradeChargeRotation D ell phase n (Multiplicative.ofAdd i) v) =
      gradeChargeRotation D ell phase n (Multiplicative.ofAdd (-i))
        (gradeTheta D n v) := by
  have h := congrArg (fun f : grade D n →ₗ[ℂ] grade D n => f v)
    (gradeChargeRotation_theta_move D ell phase n i)
  simpa [LinearMap.comp_apply] using h

/-- The charge rotation and the lattice reflection assemble into a D₆-action. -/
def gradeChargeDihedralRepresentation (D : LatticeData)
    (ell : Charge D →+ ZMod 3) (phase : ChargePhase) (n : ℤ) :
    @Representation ℂ (DihedralGroup 3) (grade D n)
      CommRing.toCommSemiring.toSemiring
        (@DivInvMonoid.toMonoid (DihedralGroup 3)
          (@Group.toDivInvMonoid (DihedralGroup 3) DihedralGroup.instGroup))
      (@AddCommGroup.toAddCommMonoid (grade D n)
        (Submodule.addCommGroup (grade D n))) _ where
  toFun
  | DihedralGroup.r i =>
      gradeChargeRotation D ell phase n (Multiplicative.ofAdd i)
  | DihedralGroup.sr i =>
      (gradeChargeRotation D ell phase n (Multiplicative.ofAdd (-i))).comp
        (gradeTheta D n)
  map_one' := by
    rw [← DihedralGroup.r_zero]
    exact gradeChargeRotation_zero D ell phase n
  map_mul' g h := by
    cases g with
    | r i =>
      cases h with
      | r j =>
        simpa only [DihedralGroup.r_mul_r, Module.End.mul_eq_comp] using
          (gradeChargeRotation_add D ell phase n i j)
      | sr j =>
        apply LinearMap.ext
        intro v
        simp only [Module.End.mul_eq_comp]
        simp only [DihedralGroup.r_mul_sr, LinearMap.comp_apply]
        have hrot := gradeChargeRotation_apply_add D ell phase n i (-j)
          (gradeTheta D n v)
        rw [← hrot]
        have hidx : -(j - i) = i + (-j) := by ring
        rw [hidx]
    | sr i =>
      cases h with
      | r j =>
        apply LinearMap.ext
        intro v
        simp only [Module.End.mul_eq_comp]
        simp only [DihedralGroup.sr_mul_r, LinearMap.comp_apply]
        rw [gradeChargeRotation_theta_move_apply]
        have hrot := gradeChargeRotation_apply_add D ell phase n (-i) (-j)
          (gradeTheta D n v)
        rw [← hrot]
        have hidx : -(i + j) = (-i) + (-j) := by ring
        rw [hidx]
      | sr j =>
        apply LinearMap.ext
        intro v
        simp only [Module.End.mul_eq_comp]
        simp only [DihedralGroup.sr_mul_sr, LinearMap.comp_apply]
        rw [gradeChargeRotation_theta_move_apply]
        rw [gradeTheta_sq]
        simp only [neg_neg]
        have hrot := gradeChargeRotation_apply_add D ell phase n (-i) j v
        rw [← hrot]
        have hidx : j - i = (-i) + j := by ring
        rw [hidx]

theorem gradeChargeRotation_fixed_theta (D : LatticeData)
    (ell : Charge D →+ ZMod 3) (phase : ChargePhase) (n : ℤ)
    (v : grade D n)
    (hv : gradeChargeRotation D ell phase n (Multiplicative.ofAdd 1) v = v) :
    gradeChargeRotation D ell phase n (Multiplicative.ofAdd 1)
        (gradeTheta D n v) = gradeTheta D n v := by
  have hmove := gradeChargeRotation_theta_move_apply D ell phase n 1 v
  rw [hv] at hmove
  have hminus : gradeChargeRotation D ell phase n (Multiplicative.ofAdd (-1))
      (gradeTheta D n v) = gradeTheta D n v := hmove.symm
  have hcomp : gradeChargeRotation D ell phase n (Multiplicative.ofAdd 0)
      (gradeTheta D n v) =
      gradeChargeRotation D ell phase n (Multiplicative.ofAdd 1)
        (gradeChargeRotation D ell phase n (Multiplicative.ofAdd (-1))
          (gradeTheta D n v)) := by
    convert gradeChargeRotation_apply_add D ell phase n 1 (-1) (gradeTheta D n v)
      using 1 <;> norm_num
  rw [gradeChargeRotation_zero] at hcomp
  have hminus_inv : gradeChargeRotation D ell phase n (Multiplicative.ofAdd 1)⁻¹
      (gradeTheta D n v) = gradeTheta D n v := by
    change gradeChargeRotation D ell phase n (Multiplicative.ofAdd (-1))
      (gradeTheta D n v) = gradeTheta D n v
    exact hminus
  have hcomp' : gradeTheta D n v =
      gradeChargeRotation D ell phase n (Multiplicative.ofAdd 1)
        (gradeTheta D n v) := by
    simpa [hminus_inv] using hcomp
  exact hcomp'.symm

abbrev ChargeEnergyFiber (D : LatticeData) (ell : Charge D →+ ZMod 3)
    (n : ℤ) (j : ZMod 3) :=
  {a : EnergyFiber D n // ell a.1.1 = j}

def gradeChargeBasisVector (D : LatticeData) (n : ℤ) (a : EnergyFiber D n) : grade D n :=
  ⟨carrierBasis D a.1, by
    rw [grade_eq_span]
    exact Submodule.subset_span ⟨a.1, a.2, rfl⟩⟩

theorem gradeChargeRotation_on_gradeChargeBasisVector (D : LatticeData)
    (ell : Charge D →+ ZMod 3) (phase : ChargePhase) (n : ℤ)
    (g : Multiplicative (ZMod 3)) (a : EnergyFiber D n) :
    gradeChargeRotation D ell phase n g (gradeChargeBasisVector D n a) =
      chargePhaseScalar phase (g.toAdd * ell a.1.1) •
        gradeChargeBasisVector D n a := by
  apply Subtype.ext
  change chargeRotation D ell phase g (gradeChargeBasisVector D n a).1 = _
  change chargeRotation D ell phase g (carrierBasis D a.1) = _
  rw [chargeRotation_on_basis]
  rfl

theorem gradeChargeRotation_coeff (D : LatticeData) (ell : Charge D →+ ZMod 3)
    (phase : ChargePhase) (n : ℤ) (g : Multiplicative (ZMod 3))
    (v : grade D n) (a : EnergyFiber D n) :
    gradeCoeffEquiv D n (gradeChargeRotation D ell phase n g v) a =
      chargePhaseScalar phase (g.toAdd * ell a.1.1) * gradeCoeffEquiv D n v a := by
  change carrierCoeffEquiv D (gradeChargeRotation D ell phase n g v).1 a.1 =
    chargePhaseScalar phase (g.toAdd * ell a.1.1) * carrierCoeffEquiv D v.1 a.1
  have hc :
      ((Finsupp.lapply a.1).comp (carrierCoeffEquiv D).toLinearMap).comp
          (chargeRotation D ell phase g) =
        chargePhaseScalar phase (g.toAdd * ell a.1.1) •
          ((Finsupp.lapply a.1).comp (carrierCoeffEquiv D).toLinearMap) := by
    apply (carrierBasis D).ext
    intro b
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, Finsupp.lapply_apply,
      smul_eq_mul]
    rw [chargeRotation_on_basis, map_smul]
    simp only [Finsupp.smul_apply, smul_eq_mul]
    have hcoord : ((carrierCoeffEquiv D).toLinearMap (carrierBasis D b)) a.1 =
        if b = a.1 then 1 else 0 := by
      change ((carrierCoeffEquiv D).toLinearMap (carrierBasis D b)) a.1 = _
      have hbasis : (carrierCoeffEquiv D).toLinearMap (carrierBasis D b) =
          Finsupp.single b 1 := by
        exact (carrierBasis D).repr_self b
      rw [hbasis]
      simp [Finsupp.single_apply]
    rw [hcoord]
    by_cases h : b = a.1
    · subst b
      simp
    · simp [h]
  have hv := LinearMap.congr_fun hc v.1
  change carrierCoeffEquiv D (chargeRotation D ell phase g v.1) a.1 = _ at hv
  simpa [LinearMap.comp_apply, smul_eq_mul] using hv

theorem chargePhaseScalar_eq_one_iff (phase : ChargePhase)
    (hphase : phase (Multiplicative.ofAdd (1 : ZMod 3)) ≠ 1) (z : ZMod 3) :
    chargePhaseScalar phase z = 1 ↔ z = 0 := by
  constructor
  · intro hz
    fin_cases z
    · rfl
    · exfalso
      apply hphase
      apply Units.ext
      exact hz
    · change chargePhaseScalar phase (2 : ZMod 3) = 1 at hz
      have hzneg : chargePhaseScalar phase (-1) = 1 := by
        rw [show (-1 : ZMod 3) = 2 by decide]
        exact hz
      have hinv : (chargePhaseScalar phase (1 : ZMod 3))⁻¹ = 1 := by
        rw [← chargePhaseScalar_neg phase (1 : ZMod 3)]
        exact hzneg
      have hone : chargePhaseScalar phase (1 : ZMod 3) = 1 := inv_eq_one.mp hinv
      exfalso
      apply hphase
      apply Units.ext
      exact hone
  · intro hz
    simpa [hz]

theorem chargePhaseScalar_sum_mul (phase : ChargePhase)
    (hphase : phase (Multiplicative.ofAdd (1 : ZMod 3)) ≠ 1)
    (z : ZMod 3) :
    (∑ i : ZMod 3, chargePhaseScalar phase (i * z)) =
      if z = 0 then (3 : ℂ) else 0 := by
  classical
  let ψ : AddChar (ZMod 3) ℂ := {
    toFun := fun i => chargePhaseScalar phase (i * z)
    map_zero_eq_one' := by simp
    map_add_eq_mul' := by
      intro i j
      rw [add_mul, chargePhaseScalar_add] }
  have hψ : ψ = 0 ↔ z = 0 := by
    constructor
    · intro h
      have h1 := congrArg (fun f : AddChar (ZMod 3) ℂ => f 1) h
      have hs : chargePhaseScalar phase z = 1 := by
        simpa [ψ] using h1
      exact (chargePhaseScalar_eq_one_iff phase hphase z).mp hs
    · intro hz
      subst z
      ext i
      simp [ψ]
  rw [show (∑ i : ZMod 3, chargePhaseScalar phase (i * z)) = ∑ i, ψ i by rfl,
    AddChar.sum_eq_ite]
  simp [hψ]

def gradeChargeResidue (D : LatticeData) (ell : Charge D →+ ZMod 3)
    (n : ℤ) (r : ZMod 3) : Submodule ℂ (grade D n) :=
  (Finsupp.supported ℂ ℂ {a : EnergyFiber D n | ell a.1.1 = r}).comap
    (gradeCoeffEquiv D n).toLinearMap

/-- The residue sector has the expected coordinate description on the energy fiber. -/
def gradeChargeResidueEquiv (D : LatticeData) (ell : Charge D →+ ZMod 3)
    (n : ℤ) (r : ZMod 3) :
    gradeChargeResidue D ell n r ≃ₗ[ℂ] (ChargeEnergyFiber D ell n r →₀ ℂ) := by
  let S : Set (EnergyFiber D n) := {a : EnergyFiber D n | ell a.1.1 = r}
  let e : gradeChargeResidue D ell n r ≃ₗ[ℂ]
      (Finsupp.supported ℂ ℂ S).comap (gradeCoeffEquiv D n).toLinearMap :=
    LinearEquiv.ofEq _ _ rfl
  let e' := (LinearEquiv.ofSubmodule' (gradeCoeffEquiv D n)
    (Finsupp.supported ℂ ℂ S)).trans (Finsupp.supportedEquivFinsupp S)
  change gradeChargeResidue D ell n r ≃ₗ[ℂ] (S →₀ ℂ)
  exact e.trans e'

theorem gradeChargeResidue_finrank (D : LatticeData) (ell : Charge D →+ ZMod 3)
    (n : ℤ) (r : ZMod 3)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) :
    Module.finrank ℂ (gradeChargeResidue D ell n r) =
      Nat.card (ChargeEnergyFiber D ell n r) := by
  letI := grade_finiteDimensional D hD n
  letI := energyFiber_finite D hD n
  letI := Fintype.ofFinite (EnergyFiber D n)
  rw [(gradeChargeResidueEquiv D ell n r).finrank_eq]
  simpa using (Module.finrank_finsupp ℂ ℂ
    (ι := ChargeEnergyFiber D ell n r))

theorem gradeChargeRotation_fixed_iff_gradeChargeResidue_zero
    (D : LatticeData) (ell : Charge D →+ ZMod 3) (phase : ChargePhase)
    (hphase : phase (Multiplicative.ofAdd (1 : ZMod 3)) ≠ 1)
    (n : ℤ) (v : grade D n) :
    gradeChargeRotation D ell phase n (Multiplicative.ofAdd 1) v = v ↔
      v ∈ gradeChargeResidue D ell n 0 := by
  constructor
  · intro hv
    change gradeCoeffEquiv D n v ∈ Finsupp.supported ℂ ℂ
      {a : EnergyFiber D n | ell a.1.1 = 0}
    rw [Finsupp.mem_supported']
    intro a ha
    have hc := congrArg (fun w : grade D n => gradeCoeffEquiv D n w a) hv
    rw [gradeChargeRotation_coeff] at hc
    have hscalar : chargePhaseScalar phase (ell a.1.1) ≠ 1 := by
      intro hs
      apply ha
      exact (chargePhaseScalar_eq_one_iff phase hphase (ell a.1.1)).mp hs
    have hc' : chargePhaseScalar phase (ell a.1.1) *
        gradeCoeffEquiv D n v a = gradeCoeffEquiv D n v a := by
      simpa using hc
    have hzero : (chargePhaseScalar phase (ell a.1.1) - 1) *
        gradeCoeffEquiv D n v a = 0 := by
      rw [sub_mul, hc']
      ring
    exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hscalar)
  · intro hv
    apply (gradeCoeffEquiv D n).injective
    ext a
    rw [gradeChargeRotation_coeff]
    by_cases ha : ell a.1.1 = 0
    · have hs := (chargePhaseScalar_eq_one_iff phase hphase 0).mpr rfl
      simp [ha, hs]
    · have hcoeff := (Finsupp.mem_supported' ℂ (gradeCoeffEquiv D n v)).mp hv a ha
      simp [hcoeff]

theorem gradeTheta_mem_gradeChargeResidue_zero
    (D : LatticeData) (ell : Charge D →+ ZMod 3) (phase : ChargePhase)
    (hphase : phase (Multiplicative.ofAdd (1 : ZMod 3)) ≠ 1)
    (n : ℤ) (v : grade D n) (hv : v ∈ gradeChargeResidue D ell n 0) :
    gradeTheta D n v ∈ gradeChargeResidue D ell n 0 := by
  apply (gradeChargeRotation_fixed_iff_gradeChargeResidue_zero D ell phase
    hphase n (gradeTheta D n v)).mp
  exact gradeChargeRotation_fixed_theta D ell phase n v
    ((gradeChargeRotation_fixed_iff_gradeChargeResidue_zero D ell phase
      hphase n v).mpr hv)

def gradeChargeSector (D : LatticeData) (ell : Charge D →+ ZMod 3)
    (n : ℤ) (j : ZMod 3) : Submodule ℂ (grade D n) :=
  Submodule.span ℂ (Set.range (fun a : ChargeEnergyFiber D ell n j =>
    gradeChargeBasisVector D n a.1))

theorem gradeChargeRotation_mem_gradeChargeSector (D : LatticeData)
    (ell : Charge D →+ ZMod 3) (phase : ChargePhase) (n : ℤ)
    (g : Multiplicative (ZMod 3)) (j : ZMod 3)
    (v : grade D n) (hv : v ∈ gradeChargeSector D ell n j) :
    gradeChargeRotation D ell phase n g v ∈ gradeChargeSector D ell n j := by
  rw [gradeChargeSector] at hv ⊢
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
  · rintro x ⟨a, rfl⟩
    rw [gradeChargeRotation_on_gradeChargeBasisVector]
    refine (Submodule.span ℂ (Set.range (fun a : ChargeEnergyFiber D ell n j =>
      gradeChargeBasisVector D n a.1))).smul_mem _ ?_
    exact Submodule.subset_span (Set.mem_range.mpr ⟨a, rfl⟩)
  · exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    simpa only [map_add] using
      (Submodule.span ℂ (Set.range (fun a : ChargeEnergyFiber D ell n j =>
        gradeChargeBasisVector D n a.1))).add_mem hx hy
  · intro c x _ hx
    simpa only [map_smul] using
      (Submodule.span ℂ (Set.range (fun a : ChargeEnergyFiber D ell n j =>
        gradeChargeBasisVector D n a.1))).smul_mem c hx

private theorem gradeChargeBasisVector_coeff (D : LatticeData) (n : ℤ)
    (a : EnergyFiber D n) :
    gradeCoeffEquiv D n (gradeChargeBasisVector D n a) = Finsupp.single a 1 := by
  apply Finsupp.ext
  intro b
  change (carrierCoeffEquiv D (gradeChargeBasisVector D n a).1) b.1 = _
  change (carrierBasis D).repr (carrierBasis D a.1) b.1 = _
  have h := congrArg (fun p : Label D →₀ ℂ => p b.1)
    ((carrierBasis D).repr_self a.1)
  simpa [Finsupp.single_apply, Subtype.ext_iff, Prod.ext_iff] using h

private theorem gradeChargeBasisVector_eq_gradeBasis (D : LatticeData) (n : ℤ)
    (a : EnergyFiber D n) :
    gradeChargeBasisVector D n a = gradeBasis D n a := by
  apply (gradeCoeffEquiv D n).injective
  rw [gradeChargeBasisVector_coeff]
  exact (gradeBasis D n).repr_self a |>.symm

theorem gradeChargeSector_eq_gradeChargeResidue (D : LatticeData)
    (ell : Charge D →+ ZMod 3) (n : ℤ) (r : ZMod 3)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) :
    gradeChargeSector D ell n r = gradeChargeResidue D ell n r := by
  letI := energyFiber_finite D hD n
  letI := Fintype.ofFinite (EnergyFiber D n)
  apply le_antisymm
  · rw [gradeChargeSector]
    refine Submodule.span_le.mpr ?_
    rintro x ⟨a, rfl⟩
    change gradeCoeffEquiv D n (gradeChargeBasisVector D n a.1) ∈
      Finsupp.supported ℂ ℂ {b : EnergyFiber D n | ell b.1.1 = r}
    rw [gradeChargeBasisVector_coeff]
    exact Finsupp.single_mem_supported ℂ 1 a.2
  · intro v hv
    have hv' : gradeCoeffEquiv D n v ∈
        Finsupp.supported ℂ ℂ {a : EnergyFiber D n | ell a.1.1 = r} := hv
    rw [gradeChargeSector]
    rw [← (gradeBasis D n).sum_repr v]
    apply Submodule.sum_mem
    intro a ha
    change gradeCoeffEquiv D n v a • gradeBasis D n a ∈ _
    by_cases has : a ∈ (gradeCoeffEquiv D n v).support
    · have har : ell a.1.1 = r :=
        (Finsupp.mem_supported ℂ (gradeCoeffEquiv D n v)).mp hv' has
      exact Submodule.smul_mem _ _ (Submodule.subset_span
        (Set.mem_range.mpr ⟨⟨a, har⟩,
          by simpa using (gradeChargeBasisVector_eq_gradeBasis D n a)⟩))
    · have hzero : gradeCoeffEquiv D n v a = 0 := by
        by_contra hzero
        exact has (Finsupp.mem_support_iff.mpr hzero)
      simp [hzero]

theorem gradeChargeRotation_trace_sum (D : LatticeData)
    (ell : Charge D →+ ZMod 3) (phase : ChargePhase)
    (hphase : phase (Multiplicative.ofAdd (1 : ZMod 3)) ≠ 1)
    (n : ℤ) (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) :
    (∑ i : ZMod 3, LinearMap.trace ℂ (grade D n)
      (gradeChargeRotation D ell phase n (Multiplicative.ofAdd i))) =
      (3 : ℂ) * (Nat.card (ChargeEnergyFiber D ell n 0) : ℂ) := by
  classical
  letI := energyFiber_finite D hD n
  letI := Fintype.ofFinite (EnergyFiber D n)
  have htrace (i : ZMod 3) :
      LinearMap.trace ℂ (grade D n)
          (gradeChargeRotation D ell phase n (Multiplicative.ofAdd i)) =
        ∑ a : EnergyFiber D n, chargePhaseScalar phase (i * ell a.1.1) := by
    rw [LinearMap.trace_eq_matrix_trace ℂ (gradeBasis D n)]
    unfold Matrix.trace
    apply Finset.sum_congr rfl
    intro a ha
    change (LinearMap.toMatrix (gradeBasis D n) (gradeBasis D n)
      (gradeChargeRotation D ell phase n (Multiplicative.ofAdd i))) a a = _
    rw [LinearMap.toMatrix_apply]
    change gradeCoeffEquiv D n
      (gradeChargeRotation D ell phase n (Multiplicative.ofAdd i) (gradeBasis D n a)) a = _
    rw [gradeChargeRotation_coeff]
    have h : gradeCoeffEquiv D n (gradeBasis D n a) = Finsupp.single a 1 :=
      (gradeBasis D n).repr_self a
    simp [h]
  simp_rw [htrace]
  rw [Finset.sum_comm]
  simp_rw [chargePhaseScalar_sum_mul phase hphase]
  have hcount : (∑ a : EnergyFiber D n, if ell a.1.1 = 0 then (1 : ℂ) else 0) =
      (Nat.card (ChargeEnergyFiber D ell n 0) : ℂ) := by
    rw [Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]
  calc
    _ = (3 : ℂ) * ∑ a : EnergyFiber D n, if ell a.1.1 = 0 then (1 : ℂ) else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      split_ifs <;> simp
    _ = _ := by rw [hcount]

theorem gradeTheta_mem_gradeChargeSector_neg (D : LatticeData)
    (ell : Charge D →+ ZMod 3) (n : ℤ) (j : ZMod 3)
    (v : grade D n) (hv : v ∈ gradeChargeSector D ell n j) :
    gradeTheta D n v ∈ gradeChargeSector D ell n (-j) := by
  rw [gradeChargeSector] at hv ⊢
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
  · rintro x ⟨a, rfl⟩
    let b : EnergyFiber D n := ⟨(-a.1.1.1, a.1.1.2), by
      simpa [energy, chargeEnergy, bilinear] using a.1.2⟩
    let b' : ChargeEnergyFiber D ell n (-j) := ⟨b, by
      dsimp [b]
      rw [map_neg]
      simpa using congrArg Neg.neg a.2⟩
    have htheta : gradeTheta D n (gradeChargeBasisVector D n a.1) =
        ((-1 : ℂ) ^ (occurrences D a.1.1.2).length) •
          gradeChargeBasisVector D n b := by
      apply Subtype.ext
      change theta D (carrierBasis D a.1.1) = _
      rw [theta_on_basis]
      rfl
    rw [htheta]
    refine (Submodule.span ℂ (Set.range (fun c : ChargeEnergyFiber D ell n (-j) =>
      gradeChargeBasisVector D n c.1))).smul_mem _ ?_
    exact Submodule.subset_span (Set.mem_range.mpr ⟨b', by
      apply Subtype.ext
      rfl⟩)
  · exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    simpa only [map_add] using
      (Submodule.span ℂ (Set.range (fun a : ChargeEnergyFiber D ell n (-j) =>
        gradeChargeBasisVector D n a.1))).add_mem hx hy
  · intro c x _ hx
    simpa only [map_smul] using
      (Submodule.span ℂ (Set.range (fun a : ChargeEnergyFiber D ell n (-j) =>
        gradeChargeBasisVector D n a.1))).smul_mem c hx

theorem gradeTheta_mem_gradeChargeResidue_neg (D : LatticeData)
    (ell : Charge D →+ ZMod 3) (n : ℤ) (r : ZMod 3)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (v : grade D n) (hv : v ∈ gradeChargeResidue D ell n r) :
    gradeTheta D n v ∈ gradeChargeResidue D ell n (-r) := by
  rw [← gradeChargeSector_eq_gradeChargeResidue D ell n (-r) hD]
  apply gradeTheta_mem_gradeChargeSector_neg D ell n r v
  rw [gradeChargeSector_eq_gradeChargeResidue D ell n r hD]
  exact hv

theorem gradeChargeDihedral_character_reflection (D : LatticeData)
    (ell : Charge D →+ ZMod 3) (phase : ChargePhase) (n : ℤ) (i : ZMod 3) :
    Representation.character (k := ℂ) (V := grade D n)
        (gradeChargeDihedralRepresentation D ell phase n) (DihedralGroup.sr i) =
      LinearMap.trace ℂ (grade D n) (gradeTheta D n) := by
  let ρ := gradeChargeDihedralRepresentation D ell phase n
  have hzero : ρ (DihedralGroup.sr 0) = gradeTheta D n := by
    apply LinearMap.ext
    intro v
    change gradeChargeRotation D ell phase n
      (Multiplicative.ofAdd (-0)) (gradeTheta D n v) = gradeTheta D n v
    rw [show (-0 : ZMod 3) = 0 by simp, gradeChargeRotation_zero]
    rfl
  have hc : (DihedralGroup.r i) * DihedralGroup.sr 0 *
      (DihedralGroup.r i)⁻¹ = DihedralGroup.sr i := by
    rw [DihedralGroup.r_mul_sr, DihedralGroup.inv_r, DihedralGroup.sr_mul_r]
    congr 1
    fin_cases i <;> decide
  have h := Representation.char_conj (k := ℂ) (V := grade D n) ρ
    (DihedralGroup.sr 0) (DihedralGroup.r i)
  rw [hc] at h
  simpa only [Representation.character, hzero] using h

/-- The fixed vectors of the dihedral action on a grade. -/
abbrev gradeChargeDihedralInvariants (D : LatticeData)
    (ell : Charge D →+ ZMod 3) (phase : ChargePhase) (n : ℤ) :
    Submodule ℂ (grade D n) :=
  @Representation.invariants ℂ (DihedralGroup 3) (grade D n)
    inferInstance inferInstance inferInstance inferInstance
    (gradeChargeDihedralRepresentation D ell phase n)

theorem mem_gradeChargeDihedralInvariants_iff (D : LatticeData)
    (ell : Charge D →+ ZMod 3) (phase : ChargePhase) (n : ℤ) (v : grade D n) :
    v ∈ gradeChargeDihedralInvariants D ell phase n ↔
      (gradeChargeRotation D ell phase n (Multiplicative.ofAdd 1) v = v ∧
        gradeTheta D n v = v) := by
  rw [Representation.mem_invariants]
  constructor
  · intro h
    constructor
    · have h1 := h (DihedralGroup.r 1)
      change gradeChargeRotation D ell phase n (Multiplicative.ofAdd 1) v = v at h1
      exact h1
    · have h0 := h (DihedralGroup.sr 0)
      change (gradeChargeRotation D ell phase n (Multiplicative.ofAdd (-0))).comp
        (gradeTheta D n) v = v at h0
      rw [show (-0 : ZMod 3) = 0 by simp, gradeChargeRotation_zero] at h0
      simpa only [LinearMap.comp_apply, LinearMap.id_apply] using h0
  · rintro ⟨hr, ht⟩ g
    cases g with
    | r i =>
      fin_cases i
      · change gradeChargeRotation D ell phase n (Multiplicative.ofAdd 0) v = v
        rw [gradeChargeRotation_zero]
        exact rfl
      · change gradeChargeRotation D ell phase n (Multiplicative.ofAdd 1) v = v
        exact hr
      · change gradeChargeRotation D ell phase n (Multiplicative.ofAdd 2) v = v
        have htwo : gradeChargeRotation D ell phase n (Multiplicative.ofAdd 2) v =
            gradeChargeRotation D ell phase n (Multiplicative.ofAdd 1)
              (gradeChargeRotation D ell phase n (Multiplicative.ofAdd 1) v) := by
          convert gradeChargeRotation_apply_add D ell phase n 1 1 v using 1 <;> norm_num
        calc
          _ = gradeChargeRotation D ell phase n (Multiplicative.ofAdd 1)
                (gradeChargeRotation D ell phase n (Multiplicative.ofAdd 1) v) := htwo
          _ = v := by rw [hr, hr]
    | sr i =>
      fin_cases i
      · change (gradeChargeRotation D ell phase n (Multiplicative.ofAdd (-0))).comp
          (gradeTheta D n) v = v
        rw [show (-0 : ZMod 3) = 0 by simp, gradeChargeRotation_zero]
        simpa only [LinearMap.comp_apply, LinearMap.id_apply] using ht
      · change gradeChargeRotation D ell phase n (Multiplicative.ofAdd (-1))
          (gradeTheta D n v) = v
        have htwo : gradeChargeRotation D ell phase n (Multiplicative.ofAdd 2)
            (gradeTheta D n v) =
              gradeChargeRotation D ell phase n (Multiplicative.ofAdd 1)
                (gradeChargeRotation D ell phase n (Multiplicative.ofAdd 1)
                  (gradeTheta D n v)) := by
          convert gradeChargeRotation_apply_add D ell phase n 1 1 (gradeTheta D n v)
            using 1 <;> norm_num
        have htwo' : gradeChargeRotation D ell phase n (Multiplicative.ofAdd 2)
            (gradeTheta D n v) = v := by
          calc
            gradeChargeRotation D ell phase n (Multiplicative.ofAdd 2)
                (gradeTheta D n v) =
                gradeChargeRotation D ell phase n (Multiplicative.ofAdd 1)
                  (gradeChargeRotation D ell phase n (Multiplicative.ofAdd 1)
                    (gradeTheta D n v)) := htwo
            _ = gradeChargeRotation D ell phase n (Multiplicative.ofAdd 1)
                  (gradeChargeRotation D ell phase n (Multiplicative.ofAdd 1) v) := by rw [ht]
            _ = gradeChargeRotation D ell phase n (Multiplicative.ofAdd 1) v := by
              exact congrArg (gradeChargeRotation D ell phase n (Multiplicative.ofAdd 1)) hr
            _ = v := hr
        have hneg : (-1 : ZMod 3) = 2 := by decide
        rw [hneg]
        exact htwo'
      · change gradeChargeRotation D ell phase n (Multiplicative.ofAdd (-2))
          (gradeTheta D n v) = v
        rw [ht]
        have hneg : (-2 : ZMod 3) = 1 := by decide
        rw [hneg]
        exact hr

theorem mem_gradeChargeDihedralInvariants_iff_gradeChargeResidue_zero_and_theta
    (D : LatticeData) (ell : Charge D →+ ZMod 3) (phase : ChargePhase)
    (hphase : phase (Multiplicative.ofAdd (1 : ZMod 3)) ≠ 1)
    (n : ℤ) (v : grade D n) :
    v ∈ gradeChargeDihedralInvariants D ell phase n ↔
      (v ∈ gradeChargeResidue D ell n 0 ∧ gradeTheta D n v = v) := by
  constructor
  · intro hv
    have hgen := (mem_gradeChargeDihedralInvariants_iff D ell phase n v).mp hv
    exact ⟨(gradeChargeRotation_fixed_iff_gradeChargeResidue_zero D ell phase
      hphase n v).mp hgen.1, hgen.2⟩
  · rintro ⟨hres, htheta⟩
    apply (mem_gradeChargeDihedralInvariants_iff D ell phase n v).mpr
    exact ⟨(gradeChargeRotation_fixed_iff_gradeChargeResidue_zero D ell phase
      hphase n v).mpr hres, htheta⟩

theorem gradeChargeDihedral_character_average_finrank (D : LatticeData)
    (ell : Charge D →+ ZMod 3) (phase : ChargePhase) (n : ℤ)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) :
    (Nat.card (DihedralGroup 3) : ℂ)⁻¹ *
        ∑ g : DihedralGroup 3,
          (gradeChargeDihedralRepresentation D ell phase n).character g =
      (Module.finrank ℂ
        (@Representation.invariants ℂ (DihedralGroup 3) (grade D n)
          inferInstance inferInstance inferInstance inferInstance
          (gradeChargeDihedralRepresentation D ell phase n)) : ℂ) := by
  letI : FiniteDimensional ℂ (grade D n) := grade_finiteDimensional D hD n
  letI : Invertible (Nat.card (DihedralGroup 3) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  rw [Representation.card_inv_mul_sum_char_eq_finrank]

/-- The dihedral average counts neutral-charge states and the signed reflection trace. -/
theorem gradeChargeDihedral_character_average_sharp (D : LatticeData)
    (ell : Charge D →+ ZMod 3) (phase : ChargePhase)
    (hphase : phase (Multiplicative.ofAdd (1 : ZMod 3)) ≠ 1)
    (n : ℤ) (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) :
    (Nat.card (DihedralGroup 3) : ℂ)⁻¹ *
        ∑ g : DihedralGroup 3,
          Representation.character (k := ℂ) (V := grade D n)
            (gradeChargeDihedralRepresentation D ell phase n) g =
      ((Nat.card (ChargeEnergyFiber D ell n 0) : ℂ) +
        LinearMap.trace ℂ (grade D n) (gradeTheta D n)) / 2 := by
  let χ := Representation.character (k := ℂ) (V := grade D n)
    (gradeChargeDihedralRepresentation D ell phase n)
  have hsum : (∑ g : DihedralGroup 3, χ g) =
      (3 : ℂ) * (Nat.card (ChargeEnergyFiber D ell n 0) : ℂ) +
        3 * LinearMap.trace ℂ (grade D n) (gradeTheta D n) := by
    rw [← (DihedralGroup.equivSum (n := 3)).symm.sum_comp χ, Fintype.sum_sum_type]
    change (∑ i : ZMod 3, LinearMap.trace ℂ (grade D n)
        (gradeChargeRotation D ell phase n (Multiplicative.ofAdd i))) +
      (∑ i : ZMod 3, χ (DihedralGroup.sr i)) = _
    rw [gradeChargeRotation_trace_sum D ell phase hphase n hD]
    simp only [χ, gradeChargeDihedral_character_reflection, Finset.sum_const,
      Finset.card_univ, ZMod.card, nsmul_eq_mul, Nat.cast_ofNat]
  change (Nat.card (DihedralGroup 3) : ℂ)⁻¹ * ∑ g, χ g = _
  rw [hsum, DihedralGroup.nat_card]
  norm_num
  ring

theorem gradeChargeDihedral_invariants_finrank_sharp (D : LatticeData)
    (ell : Charge D →+ ZMod 3) (phase : ChargePhase)
    (hphase : phase (Multiplicative.ofAdd (1 : ZMod 3)) ≠ 1)
    (n : ℤ) (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) :
    (Module.finrank ℂ (gradeChargeDihedralInvariants D ell phase n) : ℂ) =
      ((Nat.card (ChargeEnergyFiber D ell n 0) : ℂ) +
        LinearMap.trace ℂ (grade D n) (gradeTheta D n)) / 2 := by
  rw [← gradeChargeDihedral_character_average_finrank D ell phase n hD]
  exact gradeChargeDihedral_character_average_sharp D ell phase hphase n hD

end D5.S3.VertexAlgebra.SourceBPZ.ThetaChargeRotation
