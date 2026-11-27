/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qOrderNineLift
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48qOrderNineLift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An exact order-nine conformal lift of Nebe's P48q order-three isometry. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.DiagonalCharacterConjugacy
import D5.S3.VertexAlgebra.Lattice.Orbifold.NativeStandardThirdLift
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedChargeAction
import D5.S3.VertexAlgebra.LatticeHalfFockChargedLZero
import OmegaBuild.Commands

/-! The norm of the coordinate vector e₅ supplies a fixed integral shift.
The corresponding ninth-root character commutes with the standard lift on
each charge summand. Its cube is detected on the ground state of charge e₁. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qOrderNineLift

open LatticeGeneratingFieldLocality LatticeAllStateField LatticeAllStateReconstruction
open LatticeSugawaraConformal
open LatticeActualGeneratorLocality (bilinear_add_right)
open LatticeFiniteNegativeGeneration (bilinear_symmetric)
open LatticeActualConformalState (omega)
open HalfFockSpectralFiberSource (actualInverse actualInverse_left)
open P48qFixedRankCertificate (nebeOrderThree)
open P48qGramCertificate (nebeGram gram_inverse_certificate)
open P48qTwistedChargeAction (lattice g g_cube g_isometry norm_row)
open DiagonalCharacterConjugacy
open NativeStandardThirdLift
open ThirdTwistedChargeAction (nativeStandardEta nativeStandardEta_fixed)
open scoped Matrix VertexOperator

open private nebeSquare nebeSquare_eq from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFixedRankCertificate
open private dotOfFn_eq from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qGramCertificate
open private oscillator_charge from D5.S3.VertexAlgebra.Lattice.IsometryLift
open private ground_ne_zero from
  D5.S3.VertexAlgebra.Lattice.Orbifold.DiagonalCharacterConjugacy

noncomputable section

local notation "A" => nebeOrderThree
local notation "ofAdd" => Multiplicative.ofAdd

/-- The fixed integral row used for the shift, with zero-based coordinates. -/
def v : Charge lattice :=
  show Fin 48 → ℤ from Pi.single (5 : Fin 48) (1 : ℤ) ᵥ* (1 + A + A ^ 2)

private theorem v_eq_norm :
    v = ThirdTwistedChargeAction.N lattice g (unitCharge lattice (5 : Fin 48)) := by
  have he : Pi.single (5 : Fin 48) (1 : ℤ) = unitCharge lattice (5 : Fin 48) := by
    funext j
    by_cases h : j = (5 : Fin 48) <;> simp [unitCharge, h]
  rw [v, he, ← norm_row]

theorem v_fixed : g v = v := by
  rw [v_eq_norm]
  exact ThirdTwistedChargeAction.norm_fixed lattice g g_cube (unitCharge lattice (5 : Fin 48))

private theorem v_row (j : Fin 48) :
    v j = (1 : Matrix (Fin 48) (Fin 48) ℤ) 5 j + A 5 j + nebeSquare 5 j := by
  rw [v, Matrix.single_one_vecMul, pow_two, nebeSquare_eq]
  simp only [Matrix.row, Matrix.add_apply]

private theorem pairing_v_unit (i : Fin 48) :
    bilinear lattice v (unitCharge lattice i) =
      (List.zipWith (· * ·)
        (List.ofFn (fun j => (1 : Matrix (Fin 48) (Fin 48) ℤ) 5 j + A 5 j + nebeSquare 5 j))
        (List.ofFn (fun j => nebeGram j i))).sum := by
  rw [dotOfFn_eq]
  simp [bilinear, unitCharge, v_row]
  rfl

set_option maxRecDepth 4096 in
theorem v_pairing_e1 : bilinear lattice v (unitCharge lattice (1 : Fin 48)) = 2 := by
  rw [pairing_v_unit]
  decide +kernel

set_option maxRecDepth 4096 in
theorem v_norm : bilinear lattice v v = 36 := by
  let e := unitCharge lattice (5 : Fin 48)
  have h : bilinear lattice v e = 12 := by
    rw [pairing_v_unit]
    decide +kernel
  have hn := ThirdTwistedChargeAction.norm_pairing lattice g g_cube g_isometry e v
  rw [← v_eq_norm] at hn
  simp only [ThirdTwistedChargeAction.N_apply, v_fixed, bilinear_add_right,
    bilinear_symmetric lattice e v, h] at hn
  exact hn

/-- An integral pairing exponentiated using a complex unit. -/
def integralShiftCharacter (D : LatticeData) (x : Charge D) (z : ℂˣ) : Character D where
  toFun a := z ^ bilinear D x a.toAdd
  map_one' := by
    change z ^ bilinear D x 0 = 1
    simp [bilinear]
  map_mul' a b := by
    change z ^ bilinear D x (a.toAdd + b.toAdd) = z ^ bilinear D x a.toAdd *
      z ^ bilinear D x b.toAdd
    rw [bilinear_add_right, zpow_add]

private theorem integralShiftCharacter_ofAdd (D : LatticeData) (x : Charge D)
    (z : ℂˣ) (a : Charge D) :
    integralShiftCharacter D x z (ofAdd a) = z ^ bilinear D x a := rfl

private def zeta : ℂˣ :=
  Units.mk0 (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 9)) (Complex.exp_ne_zero _)

private theorem zeta_coe :
    (zeta : ℂ) = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 9) := rfl

private theorem zeta_primitive : IsPrimitiveRoot zeta 9 := by
  apply IsPrimitiveRoot.coe_units_iff.mp
  simpa only [zeta_coe, Nat.cast_ofNat] using
    Complex.isPrimitiveRoot_exp 9 (by decide)

/-- The character associated to the rational shift v/9. -/
def shiftCharacter : Character lattice := integralShiftCharacter lattice v zeta

theorem shiftCharacter_apply (a : Charge lattice) :
    (shiftCharacter (ofAdd a) : ℂ) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (bilinear lattice v a : ℂ) / 9) := by
  rw [shiftCharacter, integralShiftCharacter_ofAdd, Units.val_zpow_eq_zpow_val,
    zeta_coe, ← Complex.exp_int_mul]
  congr 1
  ring

private theorem shiftCharacter_invariant (a : Charge lattice) :
    shiftCharacter (ofAdd (g a)) = shiftCharacter (ofAdd a) := by
  have h := g_isometry v a
  rw [v_fixed] at h
  simp only [shiftCharacter, integralShiftCharacter_ofAdd, h]

/-- A charge-invariant character commutes with any linear lift that carries
each charge summand into the corresponding image summand. -/
theorem diagonal_commute_of_charge_transport (D : LatticeData) (χ : Character D)
    (s : Charge D → Charge D) (U : Carrier D ≃ₗ[ℂ] Carrier D)
    (hχ : ∀ a, χ (ofAdd (s a)) = χ (ofAdd a))
    (hU : ∀ (a : Charge D) (p : Oscillator D), ∃ q : Oscillator D,
      U (Finsupp.single a p) = Finsupp.single (s a) q) :
    Commute (diagonal D χ) U := by
  apply LinearEquiv.toLinearMap_injective
  apply Finsupp.lhom_ext
  intro a p
  change diagonal D χ (U (Finsupp.single a p)) = U (diagonal D χ (Finsupp.single a p))
  obtain ⟨q, hq⟩ := hU a p
  rw [diagonal_single, map_smul, hq, diagonal_single, hχ]

private theorem diagonal_pow_single (D : LatticeData) (χ : Character D)
    (n : ℕ) (a : Charge D) (p : Oscillator D) :
    (diagonal D χ ^ n) (Finsupp.single a p) =
      (↑(χ (ofAdd a) ^ n) : ℂ) • Finsupp.single a p := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', LinearEquiv.mul_apply, ih, map_smul, diagonal_single, smul_smul,
      pow_succ, Units.val_mul]

local notation "σ" => standardLift lattice g g_cube g_isometry
local notation "τ" => diagonal lattice shiftCharacter

/-- The lift acts by the standard lift followed by the charge diagonal. -/
def orderNineLift : Carrier lattice ≃ₗ[ℂ] Carrier lattice := τ * σ

theorem diagonal_commutes_standardLift : Commute τ σ := by
  apply diagonal_commute_of_charge_transport lattice shiftCharacter g σ shiftCharacter_invariant
  intro a p
  refine ⟨(nativeStandardEta lattice g a : ℂ) • IsometryLift.oscillator lattice g p, ?_⟩
  rw [standardLift_single, Finsupp.smul_single]

private theorem diagonal_ninth : τ ^ 9 = 1 := by
  apply LinearEquiv.toLinearMap_injective
  apply Finsupp.lhom_ext
  intro a p
  have hz : shiftCharacter (ofAdd a) ^ (9 : ℕ) = 1 := by
    rw [shiftCharacter, integralShiftCharacter_ofAdd,
      ← zpow_natCast (zeta ^ bilinear lattice v a) 9, zpow_comm,
      zpow_natCast zeta 9, zeta_primitive.pow_eq_one, one_zpow]
  change (τ ^ 9) (Finsupp.single a p) = Finsupp.single a p
  rw [diagonal_pow_single, hz, Units.val_one, one_smul]

private theorem diagonal_cube_ne_one : τ ^ 3 ≠ 1 := by
  intro h
  let a := unitCharge lattice (1 : Fin 48)
  have hs := congrArg (fun U : Carrier lattice ≃ₗ[ℂ] Carrier lattice => U (ground lattice a)) h
  change (τ ^ 3) (Finsupp.single a (1 : Oscillator lattice)) = ground lattice a at hs
  rw [diagonal_pow_single] at hs
  have hu : shiftCharacter (ofAdd a) ^ (3 : ℕ) = 1 := by
    apply Units.ext
    apply smul_left_injective ℂ (ground_ne_zero lattice a)
    simpa only [Units.val_one, one_smul] using hs
  have hPair : bilinear lattice v a = 2 := v_pairing_e1
  have hz : zeta ^ (6 : ℕ) = 1 := by
    simpa only [shiftCharacter, integralShiftCharacter_ofAdd, hPair, zpow_ofNat, ← pow_mul]
      using hu
  exact zeta_primitive.pow_ne_one_of_pos_of_lt (by decide) (by decide) hz

theorem orderNineLift_cube : orderNineLift ^ 3 = τ ^ 3 := by
  rw [orderNineLift, diagonal_commutes_standardLift.mul_pow,
    standardLift_cube lattice g g_cube g_isometry, mul_one]

/-- The order is nine on the actual carrier of all lattice states. -/
theorem orderNineLift_order : orderOf orderNineLift = 9 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  refine orderOf_eq_prime_pow (p := 3) (n := 1) ?_ ?_
  · change orderNineLift ^ (3 : ℕ) ≠ 1
    rw [orderNineLift_cube]
    exact diagonal_cube_ne_one
  · change orderNineLift ^ (9 : ℕ) = 1
    rw [show (9 : ℕ) = 3 * 3 from rfl, pow_mul, orderNineLift_cube, ← pow_mul]
    exact diagonal_ninth

private theorem diagonal_standard_modes (D : LatticeData) (s : AddAut (Charge D))
    (h3 : ∀ a, s (s (s a)) = a)
    (hs : ∀ a b, bilinear D (s a) (s b) = bilinear D a b) (χ : Character D) :
    PreservesModes D (diagonal D χ * standardLift D s h3 hs) := by
  intro u w n
  simp only [LinearEquiv.mul_apply, (standardLift_compatible D s h3 hs).2.1, diagonal_modes]

/-- A fixed integral Cartan direction gives a fixed weight-one current for
every diagonal character twist of the standard lift. Each mode of that
current commutes with the twisted lift. -/
theorem diagonal_standard_fixed_current (D : LatticeData) (s : AddAut (Charge D))
    (h3 : ∀ a, s (s (s a)) = a)
    (hs : ∀ a b, bilinear D (s a) (s b) = bilinear D a b)
    (χ : Character D) (x : Charge D) (hx : s x = x) :
    let H : Carrier D := Finsupp.single 0 (chargePolynomial D x)
    let U := diagonal D χ * standardLift D s h3 hs
    U H = H ∧ ∀ (n : ℤ) (w : Carrier D), U (((Y D H)[[n]]) w) = ((Y D H)[[n]]) (U w) := by
  dsimp only
  have hp : IsometryLift.oscillator D s (chargePolynomial D x) = chargePolynomial D x := by
    simpa only [chargePolynomial, hx] using oscillator_charge D s x 0
  have hFix : (diagonal D χ * standardLift D s h3 hs)
      (Finsupp.single 0 (chargePolynomial D x)) = Finsupp.single 0 (chargePolynomial D x) := by
    rw [LinearEquiv.mul_apply, standardLift_single, nativeStandardEta_fixed D s hs 0 (map_zero s),
      Units.val_one, one_smul, map_zero, hp, diagonal_neutral]
  refine ⟨hFix, fun n w => ?_⟩
  rw [diagonal_standard_modes D s h3 hs χ, hFix]

/-- The action on each charge and oscillator summand, including its scalar
phase. The target charge is the image under Nebe's isometry. -/
theorem orderNineLift_single (a : Charge lattice) (p : Oscillator lattice) :
    orderNineLift (Finsupp.single a p) =
      ((nativeStandardEta lattice g a : ℂ) * (shiftCharacter (ofAdd a) : ℂ)) •
        Finsupp.single (g a) (IsometryLift.oscillator lattice g p) := by
  rw [orderNineLift, LinearEquiv.mul_apply, standardLift_single, map_smul, diagonal_single,
    shiftCharacter_invariant, smul_smul]

/-- An order-nine automorphism of the actual P48q lattice VOA, preserving
the vacuum, translation, conformal state and all integer modes, with
charge transport given by Nebe's isometry. -/
theorem orderNineLift_automorphism :
    orderOf orderNineLift = 9 ∧ PreservesModes lattice orderNineLift ∧
    orderNineLift (vacuum lattice) = vacuum lattice ∧
    orderNineLift (omega lattice (actualInverse lattice)) =
      omega lattice (actualInverse lattice) ∧
    (∀ w : Carrier lattice, orderNineLift (translation lattice w) =
      translation lattice (orderNineLift w)) ∧
    (∀ (a : Charge lattice) (p : Oscillator lattice), ∃ q : Oscillator lattice,
      orderNineLift (Finsupp.single a p) = Finsupp.single (g a) q) := by
  have hσ := standardLift_compatible lattice g g_cube g_isometry
  have hdet : IsUnit lattice.G.det := Matrix.isUnit_det_of_left_inverse gram_inverse_certificate
  refine ⟨orderNineLift_order,
    diagonal_standard_modes lattice g g_cube g_isometry shiftCharacter, ?_, ?_, ?_, ?_⟩
  · rw [orderNineLift, LinearEquiv.mul_apply, hσ.1, diagonal_vacuum]
  · rw [orderNineLift, LinearEquiv.mul_apply, standardLift_omega lattice g g_cube g_isometry
      (actualInverse lattice) (actualInverse_left lattice hdet), diagonal_omega]
  · intro w
    rw [orderNineLift, LinearEquiv.mul_apply, hσ.2.2, diagonal_translation, LinearEquiv.mul_apply]
  · intro a p
    rw [orderNineLift_single, Finsupp.smul_single]
    exact ⟨_, rfl⟩

#print axioms v_fixed
#print axioms v_norm
#print axioms v_pairing_e1
#print axioms shiftCharacter_apply
#print axioms diagonal_commute_of_charge_transport
#print axioms diagonal_commutes_standardLift
#print axioms orderNineLift_cube
#print axioms orderNineLift_order
#print axioms orderNineLift_single
#print axioms orderNineLift_automorphism
#print axioms diagonal_standard_fixed_current

end

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qOrderNineLift
