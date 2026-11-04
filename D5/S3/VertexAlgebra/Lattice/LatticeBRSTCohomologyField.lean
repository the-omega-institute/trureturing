/- GID: D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyField
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyField
   mirror-E: none(waiver:algebraic-original-brst-cohomology)
   anchors: []
   utility: none
   digest: The original critical BRST kernel-image quotient carries descended integer fields and homogeneous cycle lifts. -/

/- Original tensor-state BRST cohomology. The supplier chain retains the
Bakalov--Kac lattice, Scott Carnahan field and residue calculus, Kalle Kytölä
Sugawara and Mathlib attribution. No literature novelty is asserted. -/

import D5.S3.VertexAlgebra.Lattice.LatticeBRSTSquare
import D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostBRSTDerivation
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Batteries.Tactic.OpenPrivate

/-! The actual critical kernel/image quotient and its bilinear descended fields. -/

set_option autoImplicit false

open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.LatticeBRSTCohomologyField

open LatticeGeneratingFieldLocality (LatticeData)
open LatticeMatterGhostCoupling (State)
open LatticeMatterGhostStateField
open FieldNormalProductLocality (delta)
open private parity_square current_odd from
  D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostBRSTDerivation

noncomputable section

variable (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)

/-- The actual kernel, without a chosen homogeneous-representative convention. -/
abbrev cycles := LinearMap.ker (LatticeBRST.totalCharge D H)

/-- Bilinear modes of the literal original tensor state-field map. -/
def originalMode (n : ℤ) : State D →ₗ[ℂ] Module.End ℂ (State D) :=
  (LinearMap.proj n).comp (VertexOperator.ncoeff.comp (Y D))

@[simp] theorem originalMode_apply (n : ℤ) (a b : State D) :
    originalMode D n a b = ((Y D a)[[n]]) b := rfl

private theorem charge_parity (x : State D) :
    LatticeBRST.totalCharge D H (parity D x) =
      -parity D (LatticeBRST.totalCharge D H x) := by
  have h := stateField_parity D (Jtot D H) 0
  rw [current_odd, map_smul] at h
  simp only [map_smul, Pi.smul_apply, LinearMap.smul_apply, pow_one,
    neg_one_smul, map_neg, Pi.neg_apply, current_zero_mode] at h
  have e := LinearMap.congr_fun h x
  change parity D (LatticeBRST.totalCharge D H x) =
    -LatticeBRST.totalCharge D H (parity D x) at e
  calc
    LatticeBRST.totalCharge D H (parity D x) =
        -(-LatticeBRST.totalCharge D H (parity D x)) :=
      (neg_neg (LatticeBRST.totalCharge D H (parity D x))).symm
    _ = -parity D (LatticeBRST.totalCharge D H x) :=
      congrArg (fun y : State D => -y) e.symm

/-- Actual spectral projections of the original ghost parity, for every natural degree. -/
def project (p : ℕ) : Module.End ℂ (State D) :=
  (2 : ℂ)⁻¹ • (LinearMap.id + (-1 : ℂ)^p • parity D)

@[simp] theorem project_apply (p : ℕ) (x : State D) :
    project D p x = (2 : ℂ)⁻¹ • (x + (-1 : ℂ)^p • parity D x) := rfl

theorem project_homogeneous (p : ℕ) (x : State D) :
    parity D (project D p x) = (-1 : ℂ)^p • project D p x := by
  have hs : (-1 : ℂ)^p * (-1 : ℂ)^p = 1 := by rw [← mul_pow]; norm_num
  simp only [project_apply, map_smul, map_add, parity_square]
  rw [smul_comm ((-1 : ℂ)^p) ((2 : ℂ)⁻¹)]
  congr 1
  rw [smul_add, smul_smul, hs, one_smul]
  exact add_comm _ _

theorem project_split (x : State D) : project D 0 x + project D 1 x = x := by
  simp only [project_apply, pow_zero, pow_one, one_smul, neg_one_smul]
  module

private theorem parity_split (x : State D) :
    project D 0 x - project D 1 x = parity D x := by
  simp only [project_apply, pow_zero, pow_one, one_smul, neg_one_smul]
  module

private theorem homogeneous_charge_mode (a b : State D) (p : ℕ)
    (ha : parity D a = (-1 : ℂ)^p • a) (n : ℤ) :
    LatticeBRST.totalCharge D H (originalMode D n a b) =
      originalMode D n (LatticeBRST.totalCharge D H a) b +
        (-1 : ℂ)^p • originalMode D n a (LatticeBRST.totalCharge D H b) := by
  have h := LinearMap.congr_fun
    (LatticeMatterGhostBRSTDerivation.totalCharge_field_superderivation D H a p ha n) b
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply] at h
  exact sub_eq_iff_eq_add.mp h

/-- The unrestricted Leibniz law. Both inputs may have mixed parity.
Its proof uses the actual two projections; it never chooses homogeneous representatives. -/
theorem charge_mode (a b : State D) (n : ℤ) :
    LatticeBRST.totalCharge D H (originalMode D n a b) =
      originalMode D n (LatticeBRST.totalCharge D H a) b +
        originalMode D n (parity D a) (LatticeBRST.totalCharge D H b) := by
  have h0 := homogeneous_charge_mode D H (project D 0 a) b 0
    (project_homogeneous D 0 a) n
  have h1 := homogeneous_charge_mode D H (project D 1 a) b 1
    (project_homogeneous D 1 a) n
  simp only [pow_zero, one_smul, pow_one, neg_one_smul] at h0 h1
  have qa : LatticeBRST.totalCharge D H a =
      LatticeBRST.totalCharge D H (project D 0 a) +
        LatticeBRST.totalCharge D H (project D 1 a) := by
    rw [← map_add, project_split]
  have pa : parity D a = project D 0 a - project D 1 a :=
    (parity_split D a).symm
  calc
    _ = LatticeBRST.totalCharge D H (originalMode D n (project D 0 a) b) +
        LatticeBRST.totalCharge D H (originalMode D n (project D 1 a) b) := by
      rw [← map_add, ← LinearMap.add_apply, ← map_add, project_split]
    _ = _ := by
      rw [h0, h1, qa, pa]
      simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
      abel

private theorem parity_cycle (a : cycles D H) :
    LatticeBRST.totalCharge D H (parity D a) = 0 := by
  rw [charge_parity, show LatticeBRST.totalCharge D H a = 0 from a.property,
    map_zero, neg_zero]

def cycleParity : Module.End ℂ (cycles D H) where
  toFun a := ⟨parity D a, parity_cycle D H a⟩
  map_add' a b := Subtype.ext (map_add (parity D) (a : State D) (b : State D))
  map_smul' z a := Subtype.ext (map_smul (parity D) z (a : State D))

def cycleProject (p : ℕ) : Module.End ℂ (cycles D H) :=
  (2 : ℂ)⁻¹ • (LinearMap.id + (-1 : ℂ)^p • cycleParity D H)

@[simp] theorem cycleProject_val (p : ℕ) (a : cycles D H) :
    (cycleProject D H p a : State D) = project D p a := rfl

private theorem cycle_mode_closed (a b : cycles D H) (n : ℤ) :
    LatticeBRST.totalCharge D H (originalMode D n a b) = 0 := by
  rw [charge_mode, show LatticeBRST.totalCharge D H a = 0 from a.property,
    show LatticeBRST.totalCharge D H b = 0 from b.property]
  simp

/-- The actual mode restricted to the actual kernel, bilinear in both cycles. -/
def cycleMode (n : ℤ) : cycles D H →ₗ[ℂ] Module.End ℂ (cycles D H) where
  toFun a := {
    toFun b := ⟨originalMode D n a b, cycle_mode_closed D H a b n⟩
    map_add' b c := Subtype.ext
      (map_add (originalMode D n (a : State D)) (b : State D) (c : State D))
    map_smul' z b := Subtype.ext
      (map_smul (originalMode D n (a : State D)) z (b : State D)) }
  map_add' a b := by
    apply LinearMap.ext; intro c; apply Subtype.ext
    exact LinearMap.congr_fun (map_add (originalMode D n) (a : State D) b) c
  map_smul' z a := by
    apply LinearMap.ext; intro b; apply Subtype.ext
    exact LinearMap.congr_fun (map_smul (originalMode D n) z (a : State D)) b

@[simp] theorem cycleMode_val (n : ℤ) (a b : cycles D H) :
    (cycleMode D H n a b : State D) = originalMode D n a b := rfl

variable (h26 : D.rank = 26)
  (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
  (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1)

include h26 hHG hGH in
private theorem charge_square_apply (x : State D) :
    LatticeBRST.totalCharge D H (LatticeBRST.totalCharge D H x) = 0 := by
  have h := LatticeBRST.total_square_anomaly D H hHG hGH
  rw [h26] at h
  norm_num at h
  have e := LinearMap.congr_fun h x
  simpa only [pow_two, Module.End.mul_apply, LinearMap.zero_apply] using e

/-- The ORIGINAL range is embedded into the kernel using the ACTUAL square anomaly. -/
def boundaryMap : State D →ₗ[ℂ] cycles D H :=
  (LatticeBRST.totalCharge D H).codRestrict (cycles D H)
    (charge_square_apply D H h26 hHG hGH)

/-- The range of the original Q, regarded as a submodule of the actual cycles. -/
def boundaries : Submodule ℂ (cycles D H) :=
  LinearMap.range (boundaryMap D H h26 hHG hGH)

theorem mem_boundaries (a : cycles D H) :
    a ∈ boundaries D H h26 hHG hGH ↔
      ∃ x : State D, LatticeBRST.totalCharge D H x = (a : State D) := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, congrArg Subtype.val hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, Subtype.ext hx⟩

/-- In particular the embedded boundaries are exactly range(original Q), not an intersection. -/
theorem boundaries_subtype_range :
    (boundaries D H h26 hHG hGH).map (cycles D H).subtype =
      LinearMap.range (LatticeBRST.totalCharge D H) := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (mem_boundaries D H h26 hHG hGH a).mp ha
  · rintro ⟨y, rfl⟩
    exact ⟨boundaryMap D H h26 hHG hGH y, ⟨y, rfl⟩, rfl⟩

abbrev Cohomology := cycles D H ⧸ boundaries D H h26 hHG hGH

def classOf : cycles D H →ₗ[ℂ] Cohomology D H h26 hHG hGH :=
  (boundaries D H h26 hHG hGH).mkQ

theorem classOf_surjective : Function.Surjective (classOf D H h26 hHG hGH) :=
  (boundaries D H h26 hHG hGH).mkQ_surjective

theorem classOf_eq_zero (a : cycles D H) :
    classOf D H h26 hHG hGH a = 0 ↔
      ∃ x : State D, LatticeBRST.totalCharge D H x = (a : State D) := by
  exact (Submodule.Quotient.mk_eq_zero _).trans (mem_boundaries D H h26 hHG hGH a)

private theorem left_boundary (n : ℤ) (a b : cycles D H)
    (ha : a ∈ boundaries D H h26 hHG hGH) :
    cycleMode D H n a b ∈ boundaries D H h26 hHG hGH := by
  obtain ⟨x, hx⟩ := (mem_boundaries D H h26 hHG hGH a).mp ha
  apply (mem_boundaries D H h26 hHG hGH _).mpr
  refine ⟨originalMode D n x b, ?_⟩
  rw [charge_mode, hx, show LatticeBRST.totalCharge D H b = 0 from b.property]
  simp

private theorem right_boundary (n : ℤ) (a b : cycles D H)
    (hb : b ∈ boundaries D H h26 hHG hGH) :
    cycleMode D H n a b ∈ boundaries D H h26 hHG hGH := by
  obtain ⟨x, hx⟩ := (mem_boundaries D H h26 hHG hGH b).mp hb
  apply (mem_boundaries D H h26 hHG hGH _).mpr
  refine ⟨originalMode D n (parity D a) x, ?_⟩
  rw [charge_mode, parity_cycle, parity_square, hx]
  simp

private def cycleClassMode (n : ℤ) :
    cycles D H →ₗ[ℂ] cycles D H →ₗ[ℂ] Cohomology D H h26 hHG hGH where
  toFun a := (classOf D H h26 hHG hGH).comp (cycleMode D H n a)
  map_add' a b := by
    apply LinearMap.ext; intro x
    simp only [LinearMap.comp_apply, map_add, LinearMap.add_apply]
  map_smul' z a := by
    apply LinearMap.ext; intro x
    simp only [LinearMap.comp_apply, map_smul, LinearMap.smul_apply,
      RingHom.id_apply]

/-- BOTH quotient arguments descend, for EVERY integer mode. -/
def mode (n : ℤ) : Cohomology D H h26 hHG hGH →ₗ[ℂ]
    Module.End ℂ (Cohomology D H h26 hHG hGH) :=
  LinearMap.liftQ₂ (R := ℂ) (R₂ := ℂ) (S := ℂ) (S₂ := ℂ)
    (M := cycles D H) (N := cycles D H) (P := Cohomology D H h26 hHG hGH)
    (ρ := RingHom.id ℂ) (σ := RingHom.id ℂ)
    (boundaries D H h26 hHG hGH) (boundaries D H h26 hHG hGH)
    (cycleClassMode D H h26 hHG hGH n)
    (by
      intro a ha
      apply LinearMap.mem_ker.mpr
      apply LinearMap.ext; intro b
      change classOf D H h26 hHG hGH (cycleMode D H n a b) = 0
      exact (Submodule.Quotient.mk_eq_zero (boundaries D H h26 hHG hGH)).mpr
        (left_boundary D H h26 hHG hGH n a b ha))
    (by
      intro b hb
      apply LinearMap.mem_ker.mpr
      apply LinearMap.ext; intro a
      change classOf D H h26 hHG hGH (cycleMode D H n a b) = 0
      exact (Submodule.Quotient.mk_eq_zero (boundaries D H h26 hHG hGH)).mpr
        (right_boundary D H h26 hHG hGH n a b hb))

@[simp] theorem mode_classOf (n : ℤ) (a b : cycles D H) :
    mode D H h26 hHG hGH n (classOf D H h26 hHG hGH a)
      (classOf D H h26 hHG hGH b) =
        classOf D H h26 hHG hGH (cycleMode D H n a b) := rfl

/-- Representative-independent formula, with arbitrary cycles on both sides. -/
theorem mode_representatives (n : ℤ) (a a' b b' : cycles D H)
    (ha : classOf D H h26 hHG hGH a = classOf D H h26 hHG hGH a')
    (hb : classOf D H h26 hHG hGH b = classOf D H h26 hHG hGH b') :
    classOf D H h26 hHG hGH (cycleMode D H n a b) =
      classOf D H h26 hHG hGH (cycleMode D H n a' b') := by
  rw [← mode_classOf, ← mode_classOf, ha, hb]

private theorem parity_boundary (a : cycles D H)
    (ha : a ∈ boundaries D H h26 hHG hGH) :
    cycleParity D H a ∈ boundaries D H h26 hHG hGH := by
  obtain ⟨x, hx⟩ := (mem_boundaries D H h26 hHG hGH a).mp ha
  apply (mem_boundaries D H h26 hHG hGH _).mpr
  refine ⟨-parity D x, ?_⟩
  change LatticeBRST.totalCharge D H (-LatticeMatterGhostStateField.parity D x) =
    LatticeMatterGhostStateField.parity D (a : State D)
  calc
    _ = -LatticeBRST.totalCharge D H (LatticeMatterGhostStateField.parity D x) :=
      (LatticeBRST.totalCharge D H).map_neg (LatticeMatterGhostStateField.parity D x)
    _ = -(-LatticeMatterGhostStateField.parity D (LatticeBRST.totalCharge D H x)) :=
      congrArg (fun z : State D => -z) (charge_parity D H x)
    _ = LatticeMatterGhostStateField.parity D (LatticeBRST.totalCharge D H x) :=
      neg_neg (LatticeMatterGhostStateField.parity D (LatticeBRST.totalCharge D H x))
    _ = _ := congrArg (LatticeMatterGhostStateField.parity D) hx

def parity : Module.End ℂ (Cohomology D H h26 hHG hGH) :=
  (boundaries D H h26 hHG hGH).mapQ (boundaries D H h26 hHG hGH)
    (cycleParity D H) (parity_boundary D H h26 hHG hGH)

@[simp] theorem parity_classOf (a : cycles D H) :
    parity D H h26 hHG hGH (classOf D H h26 hHG hGH a) =
      classOf D H h26 hHG hGH (cycleParity D H a) := rfl

theorem parity_involution (a : Cohomology D H h26 hHG hGH) :
    parity D H h26 hHG hGH (parity D H h26 hHG hGH a) = a := by
  obtain ⟨x, rfl⟩ := classOf_surjective D H h26 hHG hGH a
  rw [parity_classOf, parity_classOf]
  apply congrArg (classOf D H h26 hHG hGH)
  exact Subtype.ext (parity_square D (x : State D))

/-- A homogeneous CLASS has a homogeneous CYCLE lift, even when a given lift is mixed. -/
theorem homogeneous_cycle_lift (a : Cohomology D H h26 hHG hGH) (p : ℕ)
    (ha : parity D H h26 hHG hGH a = (-1 : ℂ)^p • a) :
    ∃ x : cycles D H, classOf D H h26 hHG hGH x = a ∧
      LatticeMatterGhostStateField.parity D (x : State D) = (-1 : ℂ)^p • (x : State D) := by
  obtain ⟨x, hx⟩ := classOf_surjective D H h26 hHG hGH a
  refine ⟨cycleProject D H p x, ?_, ?_⟩
  · change classOf D H h26 hHG hGH
      ((2 : ℂ)⁻¹ • (x + (-1 : ℂ)^p • cycleParity D H x)) = a
    rw [map_smul, map_add, map_smul,
      ← parity_classOf D H h26 hHG hGH x, hx, ha, smul_smul]
    have hs : (-1 : ℂ)^p * (-1 : ℂ)^p = 1 := by rw [← mul_pow]; norm_num
    rw [hs, one_smul]
    module
  · rw [cycleProject_val]
    exact project_homogeneous D p x

/-- The truncation bound depends on both chosen cycle representatives. -/
theorem mode_truncation (a b : Cohomology D H h26 hHG hGH) :
    ∃ N : ℤ, ∀ n : ℤ, N ≤ n → mode D H h26 hHG hGH n a b = 0 := by
  obtain ⟨x, rfl⟩ := classOf_surjective D H h26 hHG hGH a
  obtain ⟨y, rfl⟩ := classOf_surjective D H h26 hHG hGH b
  obtain ⟨N, hN⟩ := stateField_truncation D x y
  refine ⟨N, fun n hn => ?_⟩
  rw [mode_classOf]
  have hz : cycleMode D H n x y = 0 := by
    apply Subtype.ext
    simpa only [cycleMode_val, originalMode_apply, Submodule.coe_zero] using hN n hn
  rw [hz, map_zero]

private def field (a : Cohomology D H h26 hHG hGH) :
    VertexOperator ℂ (Cohomology D H h26 hHG hGH) :=
  VertexOperator.of_coeff (fun power => mode D H h26 hHG hGH (-power - 1) a) (by
    intro b
    obtain ⟨N, hN⟩ := mode_truncation D H h26 hHG hGH a b
    refine ⟨-N, ?_⟩
    intro power hp
    by_contra hn
    exact hp (hN (-power - 1) (by omega)))

private theorem field_modes (a : Cohomology D H h26 hHG hGH) (n : ℤ) :
    (field D H h26 hHG hGH a)[[n]] = mode D H h26 hHG hGH n a := by
  rw [field, VertexOperator.ncoeff_of_coeff, show -(-n - 1) - 1 = n by omega]

/-- The genuine quotient-linear state-field map into lower-truncated vertex operators. -/
def Y : Cohomology D H h26 hHG hGH →ₗ[ℂ]
    VertexOperator ℂ (Cohomology D H h26 hHG hGH) where
  toFun := field D H h26 hHG hGH
  map_add' a b := by
    apply HVertexOperator.coeff_inj (Γ := ℤ) (R := ℂ)
      (V := Cohomology D H h26 hHG hGH) (W := Cohomology D H h26 hHG hGH)
    funext power
    simp only [VertexOperator.coeff_eq_ncoeff, field_modes D H h26 hHG hGH,
      map_add, Pi.add_apply]
  map_smul' z a := by
    apply HVertexOperator.coeff_inj (Γ := ℤ) (R := ℂ)
      (V := Cohomology D H h26 hHG hGH) (W := Cohomology D H h26 hHG hGH)
    funext power
    simp only [VertexOperator.coeff_eq_ncoeff, field_modes D H h26 hHG hGH,
      map_smul, Pi.smul_apply, RingHom.id_apply]

@[simp] theorem Y_modes (a : Cohomology D H h26 hHG hGH) (n : ℤ) :
    (Y D H h26 hHG hGH a)[[n]] = mode D H h26 hHG hGH n a :=
  field_modes D H h26 hHG hGH a n

end
end D5.S3.VertexAlgebra.LatticeBRSTCohomologyField
