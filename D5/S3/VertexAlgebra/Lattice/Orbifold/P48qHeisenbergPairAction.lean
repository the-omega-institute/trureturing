import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargeMonodromy
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qHeisenbergCharged
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedFockIrreducibility
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring

/-!
Concrete operator relations for the P48q state in Bakalov–Kac,
arXiv:math/0402315v3, §4.3. The charge operators use the native normalized
multiplier and the existing Fock extension. The fixed torus acts through its
additive parameters, with the fixed integral periods acting trivially.

These identities give the generator relations on this carrier. A presentation
of the abstract group quotient and the reconstruction and equivalence of
categories in Proposition 4.2 are separate statements.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qHeisenbergPairAction

open LatticeGeneratingFieldLocality (Charge bilinear)
open LatticeActualGeneratorLocality (bilinear_add_right)
open LatticeFiniteNegativeGeneration (bilinear_symmetric)
open P48qTwistedChargeAction (lattice g g_cube g_isometry liftPhase Momentum Ground U U_zero U_comp)
open P48qMomentumEnergy (Fixed fixedGram physicalMomentum)
open P48qThirdTwistedField (Cartan Fock State chargeVector momentumExponent momentumExponent_eq)
open P48qTwistedHeisenberg (mode project projectAt project_action project_of_action)
open P48qTwistedFockIrreducibility (chargeOperator chargeOperator_single)
open P48qChargeMonodromy (momentumMonodromy momentumMonodromy_single U_monodromy)
open ThirdEigenspacePairing (p48qAction p48qForm)
open scoped TensorProduct

open private mem_fixed_iff pairing_physicalMomentum gram_on_charges from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qMomentumEnergy
open private action_chargeVector from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField
open private fixed_action pairing_project project_adjoint from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedHeisenberg
open private ofNat_succ_pos mode_at_pos mode_at_neg from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedHeisenberg
open private physicalMomentum_shift mode_zero_single from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qHeisenbergCharged

noncomputable section

local notation "N" => ThirdTwistedChargeAction.N lattice g
local notation "shift" => ThirdTwistedChargeAction.shift lattice g
local notation "bShift" => ThirdTwistedChargeAction.bShift lattice g
local notation "c₃" => ThirdTwistedChargeCocycle.c lattice g
local notation "ζ" => ThirdTwistedChargeCocycle.zeta
local notation "τ" => (2 * (Real.pi : ℂ) * Complex.I)

/-- The exponential of a fixed Cartan zero mode acts on each momentum
component by the exponential of its Gram pairing. -/
def torusExp (h : Fixed) : Module.End ℂ State :=
  Finsupp.lsum ℂ fun p => Complex.exp (fixedGram h (physicalMomentum p)) • Finsupp.lsingle p

theorem torusExp_single (h : Fixed) (p : Momentum) (P : Fock) :
    torusExp h (Finsupp.single p P) =
      Complex.exp (fixedGram h (physicalMomentum p)) • Finsupp.single p P := by
  simp only [torusExp, Finsupp.lsum_single, LinearMap.smul_apply, Finsupp.lsingle_apply]

/-- The identity parameter acts as the identity on the entire Fock state. -/
theorem torusExp_zero : torusExp 0 = 1 := by
  apply Finsupp.lhom_ext
  intro p P
  simp only [torusExp_single, LinearMap.BilinForm.zero_left, Complex.exp_zero, one_smul,
    Module.End.one_apply]

/-- Bakalov–Kac (4.40). The inverse of the operator at `h` is the one at `-h`. -/
theorem torusExp_mul (h h' : Fixed) :
    torusExp h * torusExp h' = torusExp (h + h') := by
  apply Finsupp.lhom_ext
  intro p P
  simp only [Module.End.mul_apply, torusExp_single, map_smul, smul_smul,
    LinearMap.BilinForm.add_left, Complex.exp_add, mul_comm]

theorem torusExp_mul_neg (h : Fixed) : torusExp h * torusExp (-h) = 1 := by
  rw [torusExp_mul, add_neg_cancel, torusExp_zero]

/-- The fixed projection of a lattice charge. -/
def projectedCharge (a : Charge lattice) : Fixed :=
  ⟨projectAt 0 (chargeVector a), (mem_fixed_iff _).mpr (by
    change p48qAction (project 1 (chargeVector a)) = project 1 (chargeVector a)
    simpa only [one_pow, one_smul] using project_action 1 (one_pow 3) (chargeVector a))⟩

private theorem shift_pairing (u : Cartan) (a : Charge lattice) (p : Momentum) :
    p48qForm u (physicalMomentum (shift a p) : Cartan) =
      p48qForm u (physicalMomentum p : Cartan) + p48qForm (projectAt 0 u) (chargeVector a) := by
  rw [physicalMomentum_shift, map_add]
  congr 1
  simpa only [projectAt, one_pow] using
    (project_adjoint (1 : ℂ) (one_pow 3) u (chargeVector a)).symm

private theorem fixed_shift_pairing (h : Fixed) (a : Charge lattice) (p : Momentum) :
    fixedGram h (physicalMomentum (shift a p)) =
      fixedGram h (physicalMomentum p) + p48qForm (h : Cartan) (chargeVector a) := by
  have hh : projectAt 0 (h : Cartan) = (h : Cartan) := by
    change project 1 (h : Cartan) = (h : Cartan)
    apply project_of_action 1 (one_pow 3)
    simpa only [one_pow, one_smul] using fixed_action h
  change p48qForm (h : Cartan) (physicalMomentum (shift a p) : Cartan) =
    p48qForm (h : Cartan) (physicalMomentum p : Cartan) + p48qForm (h : Cartan) (chargeVector a)
  simpa only [hh] using shift_pairing (h : Cartan) a p

theorem torusExp_mul_chargeOperator (h : Fixed) (a : Charge lattice) :
    torusExp h * chargeOperator a =
      Complex.exp (p48qForm (h : Cartan) (chargeVector a)) •
        (chargeOperator a * torusExp h) := by
  apply Finsupp.lhom_ext
  intro p P
  simp only [Module.End.mul_apply, LinearMap.smul_apply, torusExp_single,
    chargeOperator_single, map_smul, fixed_shift_pairing, Complex.exp_add, smul_smul]
  rw [mul_comm (Complex.exp (fixedGram h (physicalMomentum p)))]

/-- Bakalov–Kac (4.41) for the actual Fock-lifted charge operator. -/
theorem torusExp_conj_chargeOperator (h : Fixed) (a : Charge lattice) :
    torusExp h * chargeOperator a * torusExp (-h) =
      Complex.exp (p48qForm (h : Cartan) (chargeVector a)) • chargeOperator a := by
  rw [torusExp_mul_chargeOperator, Algebra.smul_mul_assoc, mul_assoc, torusExp_mul_neg, mul_one]

/-- The inclusion of the lattice fixed by the integral row action. -/
def fixedCharge (b : Charge lattice) (hb : g b = b) : Fixed :=
  ⟨chargeVector b, (mem_fixed_iff _).mpr (by rw [action_chargeVector, hb])⟩

private theorem fixedCharge_pairing (b : Charge lattice) (hb : g b = b)
    (p : Momentum) :
    ∃ m : ℤ, fixedGram (fixedCharge b hb) (physicalMomentum p) = (m : ℂ) := by
  obtain ⟨a, ha⟩ := (show ∃ a : Charge lattice, N a = p.1 from p.2)
  have hN : N b = b + b + b := by
    simp only [ThirdTwistedChargeAction.N_apply, hb]
  have hPair : bilinear lattice b p.1 = 3 * bilinear lattice b a := by
    rw [← ha, ← ThirdTwistedChargeAction.norm_pairing lattice g g_cube g_isometry b a,
      hN, bilinear_symmetric lattice (b + b + b) a, bilinear_add_right, bilinear_add_right,
      bilinear_symmetric lattice a b]
    ring
  refine ⟨bilinear lattice b a, ?_⟩
  rw [pairing_physicalMomentum]
  change p48qForm (chargeVector b) (chargeVector p.1) / 3 = _
  rw [show p48qForm (chargeVector b) (chargeVector p.1) =
    (bilinear lattice b p.1 : ℂ) from gram_on_charges ℂ b p.1, hPair]
  push_cast
  ring

/-- Bakalov–Kac (4.47). The fixed integral periods act trivially. -/
theorem torusExp_fixed_period (b : Charge lattice) (hb : g b = b) :
    torusExp (τ • fixedCharge b hb) = 1 := by
  apply Finsupp.lhom_ext
  intro p P
  obtain ⟨m, hm⟩ := fixedCharge_pairing b hb p
  rw [torusExp_single, LinearMap.BilinForm.smul_left, hm, mul_comm τ (m : ℂ),
    Complex.exp_int_mul_two_pi_mul_I, one_smul, Module.End.one_apply]

/-- The action is periodic in each fixed integral direction, as required by (4.48). -/
theorem torusExp_add_fixed_period (h : Fixed) (b : Charge lattice) (hb : g b = b) :
    torusExp (h + τ • fixedCharge b hb) = torusExp h := by
  rw [← torusExp_mul, torusExp_fixed_period, mul_one]

private def liftGround (A : Module.End ℂ Ground) : Module.End ℂ State :=
  (TensorProduct.finsuppScalarLeft ℂ Fock Momentum).conj (A.rTensor Fock)

private theorem liftGround_mul (A B : Module.End ℂ Ground) :
    liftGround (A * B) = liftGround A * liftGround B := by
  change liftGround (A.comp B) = (liftGround A).comp (liftGround B)
  simp only [liftGround, LinearMap.rTensor_comp, LinearEquiv.conj_comp]

private theorem liftGround_smul (c : ℂ) (A : Module.End ℂ Ground) :
    liftGround (c • A) = c • liftGround A := by
  simp only [liftGround, LinearMap.rTensor_smul, map_smul]

/-- The identity charge acts as the identity on the full Fock space. -/
theorem chargeOperator_zero : chargeOperator 0 = 1 := by
  change liftGround (U 0) = LinearMap.id
  simp only [liftGround, U_zero, LinearMap.rTensor_id, LinearEquiv.conj_id]

/-- The native twisted multiplication (4.42) on the full Fock space. -/
theorem chargeOperator_mul (a b : Charge lattice) :
    chargeOperator a * chargeOperator b = (c₃ a b : ℂ) • chargeOperator (a + b) := by
  change liftGround (U a) * liftGround (U b) = (c₃ a b : ℂ) • liftGround (U (a + b))
  rw [← liftGround_mul]
  change liftGround ((U a).comp (U b)) = (c₃ a b : ℂ) • liftGround (U (a + b))
  rw [U_comp, liftGround_smul]

/-- The inverse uses the same multiplication coefficient as (4.42). -/
def chargeOperatorInv (a : Charge lattice) : Module.End ℂ State :=
  ((c₃ a (-a) : ℂ)⁻¹) • chargeOperator (-a)

theorem chargeOperator_mul_inv (a : Charge lattice) :
    chargeOperator a * chargeOperatorInv a = 1 := by
  rw [chargeOperatorInv, Algebra.mul_smul_comm, chargeOperator_mul, add_neg_cancel,
    chargeOperator_zero, smul_smul, inv_mul_cancel₀ (Units.ne_zero (c₃ a (-a))), one_smul]

theorem chargeOperator_inv_mul (a : Charge lattice) :
    chargeOperatorInv a * chargeOperator a = 1 := by
  have h : c₃ a a * c₃ (-a) a = c₃ a a * c₃ a (-a) := by
    rw [← ThirdTwistedChargeCocycle.c_add_left, ← ThirdTwistedChargeCocycle.c_add_right,
      add_neg_cancel, (ThirdTwistedChargeCocycle.c_normalized lattice g a).1,
      (ThirdTwistedChargeCocycle.c_normalized lattice g a).2]
  have hc : c₃ (-a) a = c₃ a (-a) := mul_left_cancel h
  rw [chargeOperatorInv, Algebra.smul_mul_assoc, chargeOperator_mul, neg_add_cancel, hc,
    chargeOperator_zero, smul_smul, inv_mul_cancel₀ (Units.ne_zero (c₃ a (-a))), one_smul]

/-- The operator commutator in (4.43), in terms of the native multiplier. -/
theorem chargeOperator_group_commutator (a b : Charge lattice) :
    chargeOperator a * chargeOperator b * chargeOperatorInv a * chargeOperatorInv b =
      (↑(c₃ a b / c₃ b a) : ℂ) • (1 : Module.End ℂ State) := by
  have hSwap : chargeOperator a * chargeOperator b =
      (↑(c₃ a b / c₃ b a) : ℂ) • (chargeOperator b * chargeOperator a) := by
    rw [chargeOperator_mul a b, chargeOperator_mul b a, add_comm b a, smul_smul]
    have h : (c₃ a b / c₃ b a) * c₃ b a = c₃ a b := div_mul_cancel _ _
    rw [← Units.val_mul, h]
  rw [hSwap, Algebra.smul_mul_assoc, mul_assoc (chargeOperator b), chargeOperator_mul_inv,
    mul_one, Algebra.smul_mul_assoc, chargeOperator_mul_inv]

private theorem projectedCharge_pairing (a : Charge lattice) (p : Momentum) :
    fixedGram (projectedCharge a) (physicalMomentum p) =
      (bilinear lattice a p.1 : ℂ) / 3 := by
  rw [pairing_physicalMomentum]
  change p48qForm (project 1 (chargeVector a)) (chargeVector p.1) / 3 = _
  have hp : p48qAction (chargeVector p.1) = (1 : ℂ) • chargeVector p.1 := by
    obtain ⟨b, hb⟩ := (show ∃ b : Charge lattice, N b = p.1 from p.2)
    rw [action_chargeVector, ← hb, ThirdTwistedChargeAction.norm_fixed lattice g g_cube, one_smul]
  rw [pairing_project 1 (chargeVector a) (chargeVector p.1) hp]
  exact congrArg (fun z : ℂ => z / 3) (gram_on_charges ℂ a p.1)

private theorem monodromy_phase (a : Charge lattice) (p : Momentum) :
    (ζ : ℂ) ^ (ThirdTwistedChargeAction.q lattice g a + bilinear lattice a p.1) =
      Complex.exp (τ * (bShift a : ℂ)) *
        Complex.exp (fixedGram (τ • projectedCharge a) (physicalMomentum p)) := by
  let n := momentumExponent a p
  have hn : (n : ℂ) = 3 * ((bShift a : ℂ) + (bilinear lattice a p.1 : ℂ) / 3) := by
    simpa only [Rat.cast_mul, Rat.cast_add, Rat.cast_div, Rat.cast_intCast, Rat.cast_ofNat] using
      congrArg (fun x : ℚ => (x : ℂ)) (momentumExponent_eq a p)
  change Complex.exp (τ / 3) ^ n = _
  rw [← Complex.exp_int_mul, hn, ← Complex.exp_add, LinearMap.BilinForm.smul_left,
    projectedCharge_pairing]
  congr 1
  ring

private theorem liftGround_monodromy (a : Charge lattice) :
    liftGround (momentumMonodromy a) =
      Complex.exp (τ * (bShift a : ℂ)) • torusExp (τ • projectedCharge a) := by
  apply Finsupp.lhom_ext
  intro p P
  let e := TensorProduct.finsuppScalarLeft ℂ Fock Momentum
  have hs : e.symm (Finsupp.single p P) = Finsupp.single p (1 : ℂ) ⊗ₜ[ℂ] P :=
    TensorProduct.finsuppScalarLeft_symm_apply_single p P
  change e.conj ((momentumMonodromy a).rTensor Fock) (Finsupp.single p P) = _
  rw [LinearEquiv.conj_apply_apply, hs, LinearMap.rTensor_tmul, momentumMonodromy_single,
    ← TensorProduct.smul_tmul', map_smul, ← hs, LinearEquiv.apply_symm_apply,
    monodromy_phase, LinearMap.smul_apply, torusExp_single, smul_smul]

/-- The cover monodromy, expressed using the full-state torus operator. -/
theorem chargeOperator_monodromy (a : Charge lattice) :
    (↑((liftPhase.eta a)⁻¹) : ℂ) • chargeOperator (g a) =
      chargeOperator a *
        (Complex.exp (τ * (bShift a : ℂ)) • torusExp (τ • projectedCharge a)) := by
  calc
    _ = liftGround ((↑((liftPhase.eta a)⁻¹) : ℂ) • U (g a)) :=
      (liftGround_smul _ _).symm
    _ = _ := by
      rw [U_monodromy]
      change liftGround (U a * momentumMonodromy a) =
        liftGround (U a) * (Complex.exp (τ * (bShift a : ℂ)) • torusExp (τ • projectedCharge a))
      rw [liftGround_mul, liftGround_monodromy]

/-- Every generator in (4.46) acts as the identity, with the torus factor
acting at the input momentum. -/
theorem centralGenerator_eq_one (a : Charge lattice) :
    (↑(liftPhase.eta a) : ℂ) •
      (chargeOperatorInv (g a) * chargeOperator a *
        (Complex.exp (τ * (bShift a : ℂ)) • torusExp (τ • projectedCharge a))) = 1 := by
  rw [mul_assoc, ← chargeOperator_monodromy, Algebra.mul_smul_comm, chargeOperator_inv_mul,
    smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]

private theorem mapRange_mul_chargeOperator (A : Module.End ℂ Fock) (a : Charge lattice) :
    Finsupp.mapRange.linearMap A * chargeOperator a =
      chargeOperator a * Finsupp.mapRange.linearMap A := by
  apply Finsupp.lhom_ext
  intro p P
  simp only [Module.End.mul_apply, chargeOperator_single, Finsupp.mapRange.linearMap_apply,
    Finsupp.mapRange_single, map_smul]

private theorem mapRange_mul_torusExp (A : Module.End ℂ Fock) (h : Fixed) :
    Finsupp.mapRange.linearMap A * torusExp h =
      torusExp h * Finsupp.mapRange.linearMap A := by
  apply Finsupp.lhom_ext
  intro p P
  simp only [Module.End.mul_apply]
  rw [torusExp_single, map_smul]
  simp only [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, torusExp_single]

/-- All signed modes commute with the torus operators. -/
theorem mode_mul_torusExp (u : Cartan) (k : ℤ) (h : Fixed) :
    mode u k * torusExp h = torusExp h * mode u k := by
  cases k with
  | ofNat n =>
    cases n with
    | zero =>
      change mode u 0 * torusExp h = torusExp h * mode u 0
      apply Finsupp.lhom_ext
      intro p P
      simp only [Module.End.mul_apply, mode_zero_single, torusExp_single, map_smul,
        smul_smul, mul_comm]
    | succ n =>
      rw [mode_at_pos]
      exact mapRange_mul_torusExp _ h
  | negSucc n =>
    rw [mode_at_neg]
    exact mapRange_mul_torusExp _ h

/-- The scalar commutator with a charge, supported at the zero mode. -/
def modeShift (u : Cartan) (k : ℤ) (a : Charge lattice) : ℂ :=
  if k = 0 then p48qForm (projectAt 0 u) (chargeVector a) else 0

/-- The positive commutator in (4.29) for the actual signed modes and charges.
Here `k` is three times the physical current index. -/
theorem mode_mul_chargeOperator (u : Cartan) (k : ℤ) (a : Charge lattice) :
    mode u k * chargeOperator a =
      chargeOperator a * mode u k + modeShift u k a • chargeOperator a := by
  cases k with
  | ofNat n =>
    cases n with
    | zero =>
      change mode u 0 * chargeOperator a =
        chargeOperator a * mode u 0 + modeShift u 0 a • chargeOperator a
      rw [modeShift, ite_eq_left rfl]
      apply Finsupp.lhom_ext
      intro p P
      simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
        mode_zero_single, chargeOperator_single, map_smul, shift_pairing, ← add_smul]
    | succ n =>
      rw [mode_at_pos, modeShift, ite_eq_right (ne_of_gt (ofNat_succ_pos n)),
        zero_smul, add_zero]
      exact mapRange_mul_chargeOperator _ a
  | negSucc n =>
    rw [mode_at_neg, modeShift, ite_eq_right (ne_of_lt (Int.negSucc_lt_zero n)),
      zero_smul, add_zero]
    exact mapRange_mul_chargeOperator _ a

/-- With the conjugating factors in the printed order of (4.49), the
charge shifts the zero mode by the negative of the pairing, as follows
from (4.29). -/
theorem chargeOperator_mode_conj (u : Cartan) (k : ℤ) (a : Charge lattice) :
    chargeOperator a * mode u k * chargeOperatorInv a =
      mode u k - modeShift u k a • (1 : Module.End ℂ State) := by
  have h := congrArg (fun A : Module.End ℂ State => A * chargeOperatorInv a)
    (mode_mul_chargeOperator u k a)
  simp only [add_mul, mul_assoc, Algebra.smul_mul_assoc, chargeOperator_mul_inv, mul_one] at h
  rw [mul_assoc]
  exact eq_sub_of_add_eq h.symm

/-- The positive shift displayed in (4.49) holds for inverse conjugation. -/
theorem chargeOperator_inv_mode_conj (u : Cartan) (k : ℤ) (a : Charge lattice) :
    chargeOperatorInv a * mode u k * chargeOperator a =
      mode u k + modeShift u k a • (1 : Module.End ℂ State) := by
  rw [mul_assoc, mode_mul_chargeOperator, mul_add,
    ← mul_assoc (chargeOperatorInv a) (chargeOperator a), chargeOperator_inv_mul, one_mul,
    Algebra.mul_smul_comm, chargeOperator_inv_mul]

/-- Conjugation by the full scalar, torus and charge product in (4.49).
The central mode acts as the identity, and the sign follows (4.29). -/
theorem pairOperator_mode_conj
    (c : ℂˣ) (h : Fixed) (a : Charge lattice) (u : Cartan) (k : ℤ) (d : ℂ) :
    ((c : ℂ) • (torusExp h * chargeOperator a)) *
      (mode u k + d • (1 : Module.End ℂ State)) *
      ((↑(c⁻¹) : ℂ) • (chargeOperatorInv a * torusExp (-h))) =
        mode u k + (d - modeShift u k a) • (1 : Module.End ℂ State) := by
  have hScalar : (c : ℂ) * (↑(c⁻¹) : ℂ) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hCharge :
      chargeOperator a * (mode u k + d • (1 : Module.End ℂ State)) * chargeOperatorInv a =
        mode u k + (d - modeShift u k a) • (1 : Module.End ℂ State) := by
    rw [mul_add, add_mul, chargeOperator_mode_conj, Algebra.mul_smul_comm, mul_one,
      Algebra.smul_mul_assoc, chargeOperator_mul_inv]
    simp only [sub_smul]
    abel
  rw [Algebra.smul_mul_assoc, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul,
    hScalar, one_smul]
  calc
    _ = torusExp h *
        (chargeOperator a * (mode u k + d • (1 : Module.End ℂ State)) * chargeOperatorInv a) *
          torusExp (-h) := by simp only [mul_assoc]
    _ = _ := by
      rw [hCharge, mul_add, add_mul, ← mode_mul_torusExp u k h, mul_assoc (mode u k),
        torusExp_mul_neg, mul_one, Algebra.mul_smul_comm, mul_one,
        Algebra.smul_mul_assoc, torusExp_mul_neg]

#print axioms torusExp_mul
#print axioms torusExp_fixed_period
#print axioms centralGenerator_eq_one
#print axioms torusExp_conj_chargeOperator
#print axioms mode_mul_torusExp
#print axioms mode_mul_chargeOperator
#print axioms chargeOperator_mode_conj
#print axioms chargeOperator_inv_mode_conj
#print axioms pairOperator_mode_conj

end

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qHeisenbergPairAction
