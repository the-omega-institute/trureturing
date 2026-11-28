/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qTwistedGeneratorVacuum
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Vacuum and deck identities for the concrete charged and current fields. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qHeisenbergCharged
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedFieldCovariance

/-!
The vacuum and deck identities for the concrete P48q generating fields in the
Bakalov–Kac cover coordinate `z = x^3`. The deck change is `x ↦ ζ x`, where
`ζ = exp(2πi/3)`. On currents it acts by the complexification of the actual
Nebe row automorphism `g`, and on charges by `a ↦ g a` with the lift factor
`η(a)⁻¹` of the checked charged-field covariance.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedGeneratorVacuum

open LatticeGeneratingFieldLocality (Charge bilinear)
open P48qTwistedChargeAction (lattice g Momentum liftPhase U_zero)
open P48qThirdTwistedField
open P48qTwistedHeisenberg
open ThirdEigenspacePairing (p48qAction)
open private action_chargeVector from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField

noncomputable section

local notation "ζ" => (ThirdTwistedChargeCocycle.zeta : ℂ)

private theorem chargeVector_zero : chargeVector (0 : Charge lattice) = 0 := by
  funext i
  change ((0 : ℤ) : ℂ) = 0
  exact Int.cast_zero

private theorem creationSeries_zero_charge (B : FixedDualBases) :
    creationSeries B 0 = 0 := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp only [creationSeries, PowerSeries.coeff_mk, map_zero]
  | succ n =>
    simp only [coeff_creationSeries_succ, creationCoordinate, chargeVector_zero,
      map_zero, LinearMap.zero_apply, zero_smul, Finset.sum_const_zero, smul_zero]

private theorem creationExponential_zero_charge (B : FixedDualBases) :
    creationExponential B 0 = 1 := by
  simp only [creationExponential, creationSeries_zero_charge,
    PowerSeries.subst_zero_eq_C_constantCoeff, PowerSeries.constantCoeff_exp, map_one]

private theorem creationCoeff_zero_charge (B : FixedDualBases) (m : ℤ) :
    creationCoeff B 0 m = if m = 0 then 1 else 0 := by
  by_cases hm : m < 0
  · simp only [creationCoeff, if_pos hm, if_neg (ne_of_lt hm)]
  · have hnat : m.toNat = 0 ↔ m = 0 := by omega
    simp only [creationCoeff, if_neg hm, creationExponential_zero_charge,
      PowerSeries.coeff_one, hnat]

private theorem translatedPolynomial_zero_charge (B : FixedDualBases) (P : Fock) :
    translatedPolynomial B 0 P = Polynomial.C P := by
  have h : translatedPolynomial B 0 =
      (Polynomial.CAlgHom : Fock →ₐ[ℂ] Polynomial Fock) := by
    apply MvPolynomial.algHom_ext
    intro j
    rw [translatedPolynomial, MvPolynomial.aeval_X]
    change translationVariable B 0 j = Polynomial.C (MvPolynomial.X j)
    simp only [translationVariable, annihilationPairing, chargeVector_zero,
      map_zero, LinearMap.zero_apply, zero_smul, zero_mul, sub_zero]
  exact DFunLike.congr_fun h P

private theorem oscillatorCoeff_zero_charge (B : FixedDualBases) (m : ℤ) (P : Fock) :
    oscillatorCoeff B 0 m P = if m = 0 then P else 0 := by
  change (translatedPolynomial B 0 P).sum
    (fun d b => creationCoeff B 0 (m + (d : ℤ)) * b) = _
  rw [translatedPolynomial_zero_charge,
    Polynomial.sum_C_index (f := fun d b => creationCoeff B 0 (m + (d : ℤ)) * b)
      (mul_zero _)]
  simp only [Nat.cast_zero, add_zero, creationCoeff_zero_charge]
  split_ifs <;> simp only [one_mul, zero_mul]

private theorem shift_zero_charge (p : Momentum) :
    ThirdTwistedChargeAction.shift lattice g 0 p = p := by
  apply Subtype.ext
  rw [shift_numerator, map_zero, add_zero]

private theorem momentumExponent_zero_charge (p : Momentum) :
    momentumExponent 0 p = 0 := by
  simp [momentumExponent, ThirdTwistedChargeAction.q, bilinear]

private theorem chargePhase_zero_charge (p : Momentum) : chargePhase 0 p = 1 := by
  rw [chargePhase, shift_zero_charge, U_zero, LinearMap.id_apply, Finsupp.single_eq_same]

/-- The concrete zero-charge field has the identity as its degree-zero
endomorphism and vanishes at every other signed cover degree. -/
theorem concreteChargedField_zero_coeff (m : ℤ) :
    HVertexOperator.coeff (concreteChargedField 0) m =
      if m = 0 then (LinearMap.id : Module.End ℂ State) else 0 := by
  change fieldCoeff fixedDualBases 0 m = _
  by_cases hm : m = 0
  · rw [if_pos hm]
    apply Finsupp.lhom_ext
    intro p P
    simp only [fieldCoeff_single, shift_zero_charge, momentumExponent_zero_charge, sub_zero,
      chargePhase_zero_charge, one_smul, oscillatorCoeff_zero_charge, if_pos hm,
      LinearMap.id_apply]
  · rw [if_neg hm]
    apply Finsupp.lhom_ext
    intro p P
    simp only [fieldCoeff_single, shift_zero_charge, momentumExponent_zero_charge, sub_zero,
      chargePhase_zero_charge, one_smul, oscillatorCoeff_zero_charge, if_neg hm,
      Finsupp.single_zero, LinearMap.zero_apply]

/-- The zero-charge field sends every state to the constant Hahn series at degree zero. -/
theorem concreteChargedField_zero (w : State) :
    concreteChargedField 0 w = HahnModule.of ℂ (HahnSeries.single (0 : ℤ) w) := by
  apply HahnModule.ext
  funext m
  change HVertexOperator.coeff (concreteChargedField 0) m w =
    (HahnSeries.single (0 : ℤ) w).coeff m
  rw [concreteChargedField_zero_coeff, HahnSeries.coeff_single]
  split_ifs <;> rfl

/-- The vacuum identity as an equality of native field maps. -/
theorem concreteChargedField_zero_eq_single :
    concreteChargedField 0 =
      (show VertexOperator ℂ State from
        HahnSeries.single.linearMap (R := ℂ) (V := State) (0 : ℤ)) := by
  apply LinearMap.ext
  intro w
  exact concreteChargedField_zero w

private theorem zeta_cube : ζ ^ (3 : ℕ) = 1 :=
  (IsPrimitiveRoot.coe_units_iff.mpr ThirdTwistedChargeCocycle.zeta_primitive).pow_eq_one

private theorem zeta_zpow_add_three_mul (m n : ℤ) :
    ζ ^ (m + 3 * n) = ζ ^ m := by
  have hz : ζ ^ (3 : ℤ) = 1 := (zpow_natCast ζ 3).trans zeta_cube
  rw [zpow_add₀ (Units.ne_zero ThirdTwistedChargeCocycle.zeta), zpow_mul ζ 3 n, hz,
    one_zpow, mul_one]

/-- The mode at signed index `k` uses the Cartan eigenspace of eigenvalue `ζ^(-k)`. -/
theorem projectAt_action (h : Cartan) (k : ℤ) :
    p48qAction (projectAt k h) = ζ ^ (-k) • projectAt k h := by
  let r := (k % 3).toNat
  have hr : (r : ℤ) = k % 3 :=
    Int.toNat_of_nonneg (Int.emod_nonneg k (by decide : (3 : ℤ) ≠ 0))
  have hroot : ζ ^ r = ζ ^ k := by
    calc
      ζ ^ r = ζ ^ (k % 3) := by rw [← zpow_natCast ζ r, hr]
      _ = ζ ^ (k % 3 + 3 * (k / 3)) := (zeta_zpow_add_three_mul (k % 3) (k / 3)).symm
      _ = ζ ^ k := by rw [Int.emod_add_mul_ediv]
  have hcube : (ζ ^ r) ^ (3 : ℕ) = 1 := by
    rw [pow_right_comm ζ r 3, zeta_cube, one_pow]
  have hsquare : (ζ ^ r) ^ (2 : ℕ) = ζ ^ (-k) := by
    rw [hroot, ← zpow_natCast (ζ ^ k) 2, ← zpow_mul, Nat.cast_ofNat,
      show k * 2 = -k + 3 * k by omega, zeta_zpow_add_three_mul]
  rw [projectAt_eq_fourier k h]
  change p48qAction (project (ζ ^ r) h) = ζ ^ (-k) • project (ζ ^ r) h
  rw [project_action _ hcube, hsquare]

theorem mode_action (h : Cartan) (k : ℤ) :
    mode (p48qAction h) k = ζ ^ (-k) • mode h k := by
  calc
    mode (p48qAction h) k = mode (projectAt k (p48qAction h)) k :=
      (mode_projectAt (p48qAction h) k).symm
    _ = mode (p48qAction (projectAt k h)) k := by
      simp only [projectAt_eq_fourier, project, map_smul, map_add]
    _ = ζ ^ (-k) • mode (projectAt k h) k := by
      rw [projectAt_action]
      exact (modeLinear k).map_smul _ _
    _ = ζ ^ (-k) • mode h k := by rw [mode_projectAt]

/-- A mode at physical index `k / 3` occurs at exponent `m = -k - 3`.
At that exponent the deck multiplier is `ζ^m = ζ^(-k)`. -/
theorem currentField_action_coeff (h : Cartan) (m : ℤ) :
    HVertexOperator.coeff (currentField (p48qAction h)) m =
      ζ ^ m • HVertexOperator.coeff (currentField h) m := by
  rw [currentField_coeff, currentField_coeff, mode_action,
    show -(-m - 3) = m + 3 * 1 by omega, zeta_zpow_add_three_mul]

/-- Substitute `ζ x` for `x` in a native Hahn field. -/
def rotateCover (A : VertexOperator ℂ State) : VertexOperator ℂ State :=
  HVertexOperator.of_coeff (fun m => ζ ^ m • HVertexOperator.coeff A m) (by
    intro w
    refine (HVertexOperator.isPWO_support_coeff A w).mono ?_
    intro m hm
    rw [Function.mem_support] at hm ⊢
    change (ζ ^ m • HVertexOperator.coeff A m) w ≠ 0 at hm
    change HVertexOperator.coeff A m w ≠ 0
    intro hz
    exact hm (by rw [LinearMap.smul_apply, hz, smul_zero]))

theorem rotateCover_coeff (A : VertexOperator ℂ State) (m : ℤ) :
    HVertexOperator.coeff (rotateCover A) m = ζ ^ m • HVertexOperator.coeff A m :=
  rfl

theorem currentField_action (h : Cartan) :
    currentField (p48qAction h) = rotateCover (currentField h) := by
  apply HVertexOperator.coeff_inj
  funext m
  rw [rotateCover_coeff, currentField_action_coeff]

/-- On a lattice current the Cartan action comes from the same `g` as on charges. -/
theorem currentField_chargeVector_g (a : Charge lattice) :
    currentField (chargeVector (g a)) = rotateCover (currentField (chargeVector a)) := by
  rw [← action_chargeVector, currentField_action]

theorem concreteChargedField_g (a : Charge lattice) :
    (↑((liftPhase.eta a)⁻¹) : ℂ) • concreteChargedField (g a) =
      rotateCover (concreteChargedField a) := by
  apply HVertexOperator.coeff_inj
  funext m
  rw [rotateCover_coeff]
  apply LinearMap.ext
  intro w
  simpa only [LinearMap.smul_apply, HVertexOperator.coeff_apply_apply, HahnModule.of_symm_smul,
    HahnSeries.coeff_smul] using concreteChargedField_coeff_g a w m

end

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedGeneratorVacuum
