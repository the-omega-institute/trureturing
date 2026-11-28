/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qTwistedFieldCovariance
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coefficientwise covariance of charged fields under third-cover rotation. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFixedDualBases
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargeMonodromy
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.RingTheory.PowerSeries.Substitution

/-!
Coefficientwise covariance of the third-twisted charged field under
`x ↦ ζ x`, with `z = x^3`. The creation and translation variables have
opposite cover degrees. The ground charge contributes the momentum exponent.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField

open LatticeGeneratingFieldLocality (Charge bilinear)
open P48qTwistedChargeAction (lattice g g_cube g_isometry liftPhase Momentum Ground)
open ThirdEigenspacePairing (p48qAction p48qForm)
open private formInvariant action_chargeVector from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField

noncomputable section

local notation "ζ" => (ThirdTwistedChargeCocycle.zeta : ℂ)
local notation "shift" => ThirdTwistedChargeAction.shift lattice g

private theorem zeta_ne_zero : ζ ≠ 0 :=
  Units.ne_zero ThirdTwistedChargeCocycle.zeta

private theorem zeta_cube : ζ ^ (3 : ℕ) = 1 :=
  (IsPrimitiveRoot.coe_units_iff.mpr ThirdTwistedChargeCocycle.zeta_primitive).pow_eq_one

private theorem modeRoot_eq_pow (j : Mode) : modeRoot j = ζ ^ frequency j :=
  (pow_eq_pow_mod (frequency j) zeta_cube).symm

private theorem zeta_zpow_neg_nat (n : ℕ) : ζ ^ (-(n : ℤ)) = ζ⁻¹ ^ n := by
  rw [zpow_neg, zpow_natCast, inv_pow]

private theorem pairing_g (a : Charge lattice) (v : Cartan) (u r : ℂ)
    (hr : r * u = 1) (hv : p48qAction v = u • v) :
    p48qForm (chargeVector (g a)) v = r * p48qForm (chargeVector a) v := by
  have h : u * p48qForm (chargeVector (g a)) v = p48qForm (chargeVector a) v := by
    simpa only [action_chargeVector, hv, LinearMap.BilinForm.smul_right]
      using formInvariant (chargeVector a) v
  rw [← h, ← mul_assoc, hr, one_mul]

theorem creationCoordinate_g (B : FixedDualBases) (a : Charge lattice) (j : Mode) :
    creationCoordinate B (g a) j = ζ ^ frequency j * creationCoordinate B a j := by
  unfold creationCoordinate
  refine pairing_g a (annihilatorDual B j) (modeRoot j ^ 2) _ ?_ (annihilatorDual_action B j)
  rw [modeRoot_eq_pow, ← pow_succ' (ζ ^ frequency j) 2]
  change (ζ ^ frequency j) ^ (3 : ℕ) = 1
  rw [pow_right_comm ζ (frequency j) 3, zeta_cube, one_pow]

theorem annihilationPairing_g (B : FixedDualBases) (a : Charge lattice) (j : Mode) :
    annihilationPairing B (g a) j = ζ ^ (-(frequency j : ℤ)) * annihilationPairing B a j := by
  unfold annihilationPairing
  refine pairing_g a (creator B j) (modeRoot j) _ ?_ (creator_action B j)
  rw [modeRoot_eq_pow]
  simpa only [zpow_natCast] using zpow_neg_mul_zpow_self (frequency j : ℤ) zeta_ne_zero

theorem creationSeries_g (B : FixedDualBases) (a : Charge lattice) :
    creationSeries B (g a) = PowerSeries.rescale (algebraMap ℂ Fock ζ) (creationSeries B a) := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_rescale]
  cases n with
  | zero => simp only [creationSeries, PowerSeries.coeff_mk, mul_zero]
  | succ m =>
    rw [coeff_creationSeries_succ, coeff_creationSeries_succ, ← map_pow, ← Algebra.smul_def]
    simp only [creationCoordinate_g, frequency, mul_smul]
    rw [← Finset.smul_sum, smul_comm]

theorem creationExponential_g (B : FixedDualBases) (a : Charge lattice) :
    creationExponential B (g a) =
      PowerSeries.rescale (algebraMap ℂ Fock ζ) (creationExponential B a) := by
  have hzero : PowerSeries.constantCoeff (creationSeries B a) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, creationSeries, PowerSeries.coeff_mk]
  rw [creationExponential, creationSeries_g, PowerSeries.rescale_eq_subst,
    creationExponential, PowerSeries.rescale_eq_subst,
    PowerSeries.subst_comp_subst_apply
      (PowerSeries.HasSubst.of_constantCoeff_zero' hzero)
      (PowerSeries.HasSubst.smul_X' (algebraMap ℂ Fock ζ))]

theorem creationCoeff_g (B : FixedDualBases) (a : Charge lattice) (k : ℤ) :
    creationCoeff B (g a) k = ζ ^ k • creationCoeff B a k := by
  by_cases h : k < 0
  · simp only [creationCoeff, if_pos h, smul_zero]
  · have hk : (k.toNat : ℤ) = k := Int.toNat_of_nonneg (le_of_not_gt h)
    simp only [creationCoeff, if_neg h, creationExponential_g, PowerSeries.coeff_rescale]
    rw [← map_pow, ← Algebra.smul_def, ← zpow_natCast ζ k.toNat, hk]

private theorem coeff_comp_rescale (Q : Polynomial Fock) (c : ℂ) (n : ℕ) :
    (Q.comp (Polynomial.C (algebraMap ℂ Fock c) * Polynomial.X)).coeff n =
      c ^ n • Q.coeff n := by
  rw [Polynomial.comp_C_mul_X_coeff, ← map_pow, mul_comm (Q.coeff n), ← Algebra.smul_def]

theorem translatedPolynomial_g (B : FixedDualBases) (a : Charge lattice) (P : Fock) :
    translatedPolynomial B (g a) P =
      (translatedPolynomial B a P).comp (Polynomial.C (algebraMap ℂ Fock ζ⁻¹) * Polynomial.X) := by
  let scale : Polynomial Fock →ₐ[ℂ] Polynomial Fock :=
    (Polynomial.aeval (R := Fock)
      (Polynomial.C (algebraMap ℂ Fock ζ⁻¹) * Polynomial.X)).restrictScalars ℂ
  have h : translatedPolynomial B (g a) = scale.comp (translatedPolynomial B a) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [translatedPolynomial, MvPolynomial.aeval_X, AlgHom.comp_apply, scale,
      AlgHom.restrictScalars_apply, ← Polynomial.comp_eq_aeval]
    apply Polynomial.ext
    intro n
    rw [coeff_comp_rescale]
    simp only [translationVariable, Polynomial.coeff_sub, Polynomial.coeff_C,
      Polynomial.coeff_C_mul_X_pow, annihilationPairing_g, zeta_zpow_neg_nat]
    by_cases hn : n = frequency j
    · subst n
      have hfreq : frequency j ≠ 0 := Nat.succ_ne_zero j.2
      simp only [if_neg hfreq, ite_true, zero_sub, smul_neg, smul_smul]
    · simp only [if_neg hn, sub_zero]
      by_cases h0 : n = 0
      · subst n
        simp only [pow_zero, one_smul]
      · simp only [if_neg h0, smul_zero]
  simpa only [AlgHom.comp_apply, scale, AlgHom.restrictScalars_apply, ← Polynomial.comp_eq_aeval]
    using DFunLike.congr_fun h P

theorem coeff_translatedPolynomial_g (B : FixedDualBases) (a : Charge lattice) (P : Fock) (d : ℕ) :
    (translatedPolynomial B (g a) P).coeff d =
      ζ ^ (-(d : ℤ)) • (translatedPolynomial B a P).coeff d := by
  rw [translatedPolynomial_g, coeff_comp_rescale, zeta_zpow_neg_nat]

/-- The degree `k + d` from creation and the degree `-d` from translation
give the phase at the exact Laurent cover exponent `k`. -/
theorem oscillatorCoeff_g (B : FixedDualBases) (a : Charge lattice) (k : ℤ) (P : Fock) :
    oscillatorCoeff B (g a) k P = ζ ^ k • oscillatorCoeff B a k P := by
  classical
  have hs : (translatedPolynomial B (g a) P).support = (translatedPolynomial B a P).support := by
    apply Finset.ext
    intro d
    rw [Polynomial.mem_support_iff, Polynomial.mem_support_iff, coeff_translatedPolynomial_g]
    exact smul_ne_zero_iff_right (zpow_ne_zero _ zeta_ne_zero)
  rw [oscillatorCoeff_apply, oscillatorCoeff_apply, hs, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [creationCoeff_g, coeff_translatedPolynomial_g, smul_mul_assoc, mul_smul_comm,
    smul_smul, ← zpow_add₀ zeta_ne_zero, add_neg_cancel_right]

private theorem shift_g (a : Charge lattice) (p : Momentum) : shift (g a) p = shift a p := by
  apply Subtype.ext
  simp only [shift_numerator, ThirdTwistedChargeAction.N_apply, g_cube]
  ac_rfl

private theorem momentumExponent_g (a : Charge lattice) (p : Momentum) :
    momentumExponent (g a) p = momentumExponent a p := by
  obtain ⟨b, hb⟩ := (show ∃ b, ThirdTwistedChargeAction.N lattice g b = p.1 from p.2)
  have hp : g p.1 = p.1 := by
    rw [← hb]
    exact ThirdTwistedChargeAction.norm_fixed lattice g g_cube b
  have hpair : bilinear lattice (g a) p.1 = bilinear lattice a p.1 := by
    simpa only [hp] using g_isometry a p.1
  unfold momentumExponent ThirdTwistedChargeAction.q
  rw [g_isometry a (g a), g_isometry a a, hpair]

private theorem chargePhase_g (a : Charge lattice) (p : Momentum) :
    (↑((liftPhase.eta a)⁻¹) : ℂ) * chargePhase (g a) p =
      ζ ^ momentumExponent a p * chargePhase a p := by
  have h := P48qChargeMonodromy.U_monodromy_single a p 1
  simp only [U_ground, shift_g] at h
  have hphase := congrArg (fun v : Ground => v (shift a p)) h
  simpa only [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, momentumExponent]
    using hphase

theorem fieldCoeff_g (B : FixedDualBases) (a : Charge lattice) (k : ℤ) :
    (↑((liftPhase.eta a)⁻¹) : ℂ) • fieldCoeff B (g a) k = ζ ^ k • fieldCoeff B a k := by
  apply Finsupp.lhom_ext
  intro p P
  simp only [LinearMap.smul_apply, fieldCoeff_single, shift_g, momentumExponent_g,
    oscillatorCoeff_g, Finsupp.smul_single]
  apply congrArg (Finsupp.single (shift a p))
  have hdegree : momentumExponent a p + (k - momentumExponent a p) = k := by omega
  have hpow : ζ ^ momentumExponent a p * ζ ^ (k - momentumExponent a p) = ζ ^ k := by
    rw [← zpow_add₀ zeta_ne_zero, hdegree]
  simp only [smul_smul]
  rw [← mul_assoc, chargePhase_g, mul_right_comm (ζ ^ momentumExponent a p), hpow]

theorem chargedField_coeff_g (B : FixedDualBases) (a : Charge lattice) (v : State) (k : ℤ) :
    (↑((liftPhase.eta a)⁻¹) : ℂ) • ((HahnModule.of ℂ).symm (chargedField B (g a) v)).coeff k =
      ζ ^ k • ((HahnModule.of ℂ).symm (chargedField B a v)).coeff k := by
  rw [chargedField_coeff, chargedField_coeff]
  simpa only [LinearMap.smul_apply] using
    congrArg (fun f : Module.End ℂ State => f v) (fieldCoeff_g B a k)

/-- The concrete charged field obeys the cover branch change on every finite state. -/
theorem concreteChargedField_coeff_g (a : Charge lattice) (v : State) (k : ℤ) :
    (↑((liftPhase.eta a)⁻¹) : ℂ) •
        ((HahnModule.of ℂ).symm (concreteChargedField (g a) v)).coeff k =
      ζ ^ k • ((HahnModule.of ℂ).symm (concreteChargedField a v)).coeff k :=
  chargedField_coeff_g fixedDualBases a v k

#print axioms oscillatorCoeff_g
#print axioms concreteChargedField_coeff_g

end

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField
