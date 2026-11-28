/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qPositiveCurrentChargedField
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive current derivations and their commutator with the charged field. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFixedDualBases
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.RingTheory.PowerSeries.Exp

/-!
The positive-current commutator with the P48q twisted charged field in the
cover coordinate `x`. The exponential proof follows the coefficient recurrence
in `ActualSeriesDerivation.actual_exponential_derivation` on the P48q carrier.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField

open LatticeGeneratingFieldLocality (Charge)
open P48qTwistedChargeAction (lattice Momentum)
open MvPolynomial (X)
open scoped BigOperators

noncomputable section

private def positiveDerivation (j : Mode) : Derivation ℂ Fock Fock :=
  ((frequency j : ℂ) / 3) • MvPolynomial.pderiv j

private theorem positiveDerivation_apply (j : Mode) (P : Fock) :
    positiveDerivation j P = ((frequency j : ℂ) / 3) • MvPolynomial.pderiv j P :=
  rfl

/-- The current at frequency `frequency j / 3` is the normalized partial derivative. -/
def positiveCurrent (j : Mode) : Module.End ℂ Fock :=
  (positiveDerivation j).toLinearMap

theorem positiveCurrent_apply (j : Mode) (P : Fock) :
    positiveCurrent j P = ((frequency j : ℂ) / 3) • MvPolynomial.pderiv j P :=
  rfl

private theorem coeff_zero_creationSeries (B : FixedDualBases) (a : Charge lattice) :
    PowerSeries.coeff 0 (creationSeries B a) = 0 := by
  rw [creationSeries, PowerSeries.coeff_mk]

private theorem pderiv_creationLinear (B : FixedDualBases) (a : Charge lattice)
    (j : Mode) (m : ℕ) :
    MvPolynomial.pderiv j (∑ i : Fin 16, creationCoordinate B a (i, m) • (X (i, m) : Fock)) =
      if m = j.2 then creationCoordinate B a j • (1 : Fock) else 0 := by
  classical
  rcases j with ⟨i, n⟩
  rw [map_sum]
  by_cases hm : m = n
  · subst m
    rw [if_pos rfl, Finset.sum_eq_single i]
    · rw [Derivation.map_smul, MvPolynomial.pderiv_X_self]
    · intro l _ hl
      have hp : (l, n) ≠ (i, n) := fun h => hl (congrArg Prod.fst h)
      rw [Derivation.map_smul, MvPolynomial.pderiv_X_of_ne hp, smul_zero]
    · simp
  · rw [if_neg hm]
    apply Finset.sum_eq_zero
    intro i' _
    have hp : (i', m) ≠ (i, n) := fun h => hm (congrArg Prod.snd h)
    rw [Derivation.map_smul, MvPolynomial.pderiv_X_of_ne hp, smul_zero]

/-- The normalization cancels the inverse frequency in the creation exponent. -/
theorem positiveCurrent_creationSeries_coeff (B : FixedDualBases) (a : Charge lattice)
    (j : Mode) (n : ℕ) :
    positiveCurrent j (PowerSeries.coeff n (creationSeries B a)) =
      if n = frequency j then creationCoordinate B a j • (1 : Fock) else 0 := by
  cases n with
  | zero =>
    have hn : 0 ≠ frequency j := by unfold frequency; omega
    rw [coeff_zero_creationSeries, map_zero, if_neg hn]
  | succ n =>
    rw [positiveCurrent_apply, coeff_creationSeries_succ, Derivation.map_smul, pderiv_creationLinear]
    by_cases hn : n = j.2
    · subst n
      have hfreq : (((j.2 + 1 : ℕ) : ℂ) / 3) ≠ 0 :=
        div_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j.2)) (by norm_num)
      simp only [frequency, Nat.succ_eq_add_one, if_pos rfl, smul_smul,
        ← mul_assoc, mul_inv_cancel₀ hfreq, one_mul, one_smul]
    · have hdegree : n + 1 ≠ frequency j := by unfold frequency; omega
      simp only [Nat.succ_eq_add_one, if_neg hn, if_neg hdegree, smul_zero]

/-- Extend the current to power series by acting on each Fock coefficient. -/
private def seriesDerivation (j : Mode) :
    Derivation ℂ (PowerSeries Fock) (PowerSeries Fock) where
  toFun f := PowerSeries.mk fun n => positiveDerivation j (PowerSeries.coeff n f)
  map_add' f g := by apply PowerSeries.ext; intro n; simp
  map_smul' c f := by apply PowerSeries.ext; intro n; simp
  map_one_eq_zero' := by
    apply PowerSeries.ext
    intro n
    simp [PowerSeries.coeff_one, apply_ite]
  leibniz' f g := by
    apply PowerSeries.ext
    intro n
    change PowerSeries.coeff n
        (PowerSeries.mk fun d => positiveDerivation j (PowerSeries.coeff d (f * g))) =
      PowerSeries.coeff n
        (f * (PowerSeries.mk fun d => positiveDerivation j (PowerSeries.coeff d g)) +
          g * (PowerSeries.mk fun d => positiveDerivation j (PowerSeries.coeff d f)))
    rw [mul_comm g (PowerSeries.mk fun d => positiveDerivation j (PowerSeries.coeff d f))]
    simp only [PowerSeries.coeff_mk, map_add, PowerSeries.coeff_mul, map_sum,
      Derivation.leibniz, smul_eq_mul, Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    ring

private theorem seriesDerivation_coeff (j : Mode) (f : PowerSeries Fock) (n : ℕ) :
    PowerSeries.coeff n (seriesDerivation j f) = positiveDerivation j (PowerSeries.coeff n f) := by
  change PowerSeries.coeff n
    (PowerSeries.mk fun d => positiveDerivation j (PowerSeries.coeff d f)) = _
  exact PowerSeries.coeff_mk n (fun d => positiveDerivation j (PowerSeries.coeff d f))

private theorem seriesDerivation_commute (j : Mode) (f : PowerSeries Fock) :
    seriesDerivation j (PowerSeries.derivative f) =
      PowerSeries.derivative (seriesDerivation j f) := by
  apply PowerSeries.ext
  intro n
  simp only [seriesDerivation_coeff, PowerSeries.coeff_derivative, Derivation.leibniz,
    Derivation.map_add, Derivation.map_natCast, Derivation.map_one_eq_zero,
    add_zero, smul_eq_mul]
  ring

private theorem seriesDerivation_creationExponential (B : FixedDualBases)
    (a : Charge lattice) (j : Mode) :
    seriesDerivation j (creationExponential B a) =
      creationExponential B a * seriesDerivation j (creationSeries B a) := by
  let S := creationSeries B a
  let E := creationExponential B a
  let A := PowerSeries.derivative S
  let H := seriesDerivation j E - E * seriesDerivation j S
  have hS : PowerSeries.constantCoeff S = 0 := by
    exact (PowerSeries.coeff_zero_eq_constantCoeff_apply S).symm.trans
      (coeff_zero_creationSeries B a)
  have hE : PowerSeries.derivative E = E * A := by
    dsimp only [E, creationExponential, A, S]
    rw [PowerSeries.derivative_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hS),
      PowerSeries.derivative_exp]
  have hH : PowerSeries.derivative H = H * A := by
    dsimp only [H]
    rw [map_sub, ← seriesDerivation_commute, hE, (seriesDerivation j).leibniz,
      (PowerSeries.derivative (R := Fock)).leibniz, hE, ← seriesDerivation_commute]
    simp only [smul_eq_mul]
    ring
  have h0 : PowerSeries.coeff 0 H = 0 := by
    dsimp only [H, E, S]
    rw [map_sub, seriesDerivation_coeff, coeff_zero_creationExponential,
      Derivation.map_one_eq_zero, PowerSeries.coeff_mul]
    simp only [Finset.Nat.antidiagonal_zero, Finset.sum_singleton, seriesDerivation_coeff,
      coeff_zero_creationSeries, map_zero, mul_zero, sub_zero]
  have hz : H = 0 := by
    apply PowerSeries.ext
    intro n
    rw [map_zero]
    induction n using Nat.strong_induction_on with
    | h n ih =>
      cases n with
      | zero => exact h0
      | succ n =>
        have hcoeff := congrArg (PowerSeries.coeff n) hH
        rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul] at hcoeff
        have hsum : (∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
            PowerSeries.coeff p.1 H * PowerSeries.coeff p.2 A) = 0 := by
          apply Finset.sum_eq_zero
          intro p hp
          have hindex := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
          rw [ih p.1 (by omega), zero_mul]
        rw [hsum] at hcoeff
        have hnsmul : (n + 1) • PowerSeries.coeff (n + 1) H = (n + 1) • (0 : Fock) := by
          simpa only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one, mul_comm, mul_zero, zero_mul]
            using hcoeff
        exact (smul_right_inj (Nat.succ_ne_zero n)).mp hnsmul
  exact sub_eq_zero.mp hz

theorem positiveCurrent_creationExponential_coeff (B : FixedDualBases) (a : Charge lattice)
    (j : Mode) (n : ℕ) :
    positiveCurrent j (PowerSeries.coeff n (creationExponential B a)) =
      if frequency j ≤ n then
        creationCoordinate B a j •
          PowerSeries.coeff (n - frequency j) (creationExponential B a)
      else 0 := by
  have hseries : seriesDerivation j (creationSeries B a) =
      PowerSeries.C (creationCoordinate B a j • (1 : Fock)) * PowerSeries.X ^ frequency j := by
    apply PowerSeries.ext
    intro d
    rw [seriesDerivation_coeff, PowerSeries.coeff_C_mul_X_pow]
    exact positiveCurrent_creationSeries_coeff B a j d
  have h := congrArg (PowerSeries.coeff n) (seriesDerivation_creationExponential B a j)
  rw [seriesDerivation_coeff, hseries, ← mul_assoc, PowerSeries.coeff_mul_X_pow'] at h
  change positiveDerivation j (PowerSeries.coeff n (creationExponential B a)) = _
  rw [h]
  split_ifs
  · rw [PowerSeries.coeff_mul_C, mul_smul_comm, mul_one]
  · rfl

/-- The Laurent coefficient formula includes the zero extension to negative degrees. -/
theorem positiveCurrent_creationCoeff (B : FixedDualBases) (a : Charge lattice)
    (j : Mode) (k : ℤ) :
    positiveCurrent j (creationCoeff B a k) =
      creationCoordinate B a j • creationCoeff B a (k - (frequency j : ℤ)) := by
  by_cases hk : k < 0
  · have hshift : k - (frequency j : ℤ) < 0 := by omega
    simp only [creationCoeff, if_pos hk, if_pos hshift, map_zero, smul_zero]
  · rw [creationCoeff, if_neg hk, positiveCurrent_creationExponential_coeff]
    by_cases hj : frequency j ≤ k.toNat
    · have hshift : ¬ k - (frequency j : ℤ) < 0 := by omega
      rw [if_pos hj, creationCoeff, if_neg hshift,
        show (k - (frequency j : ℤ)).toNat = k.toNat - frequency j by omega]
    · have hshift : k - (frequency j : ℤ) < 0 := by omega
      rw [if_neg hj, creationCoeff, if_pos hshift, smul_zero]

private def polynomialDerivation (j : Mode) :
    Derivation ℂ (Polynomial Fock) (Polynomial Fock) :=
  PolynomialModule.equivPolynomialSelf.toLinearMap.compDer (positiveDerivation j).mapCoeffs

private theorem polynomialDerivation_monomial (j : Mode) (n : ℕ) (P : Fock) :
    polynomialDerivation j (Polynomial.monomial n P) =
      Polynomial.monomial n (positiveDerivation j P) := by
  apply Polynomial.ext
  intro d
  change positiveDerivation j ((Polynomial.monomial n P).coeff d) = _
  by_cases h : n = d <;> simp [Polynomial.coeff_monomial, h]

private theorem polynomialDerivation_C (j : Mode) (P : Fock) :
    polynomialDerivation j (Polynomial.C P) = Polynomial.C (positiveDerivation j P) :=
  polynomialDerivation_monomial j 0 P

private theorem polynomialDerivation_X (j : Mode) :
    polynomialDerivation j (Polynomial.X : Polynomial Fock) = 0 := by
  rw [← Polynomial.monomial_one_one_eq_X, polynomialDerivation_monomial,
    Derivation.map_one_eq_zero, map_zero]

private theorem polynomialDerivation_translatedPolynomial (B : FixedDualBases) (a : Charge lattice)
    (j : Mode) (P : Fock) :
    polynomialDerivation j (translatedPolynomial B a P) =
      translatedPolynomial B a (positiveDerivation j P) := by
  have hconstant (c : ℂ) : positiveDerivation j (c • (1 : Fock)) = 0 := by
    rw [Derivation.map_smul, Derivation.map_one_eq_zero, smul_zero]
  have hscalar (c : ℂ) :
      translatedPolynomial B a (c • (1 : Fock)) = Polynomial.C (c • (1 : Fock)) := by
    simp only [Algebra.smul_def, mul_one, AlgHom.commutes, Polynomial.algebraMap_apply]
  have hX (i : Mode) : polynomialDerivation j (translatedPolynomial B a (X i)) =
      translatedPolynomial B a (positiveDerivation j (X i)) := by
    have hvar : translatedPolynomial B a (X i) = translationVariable B a i :=
      MvPolynomial.aeval_X _ _
    rw [hvar]
    simp only [translationVariable, map_sub, Derivation.leibniz, polynomialDerivation_C,
      hconstant, polynomialDerivation_X, Derivation.leibniz_pow, smul_zero, zero_smul,
      add_zero, zero_add, map_zero, sub_zero]
    by_cases hi : i = j
    · subst i
      simp only [positiveDerivation_apply, MvPolynomial.pderiv_X_self, hscalar]
    · simp only [positiveDerivation_apply, MvPolynomial.pderiv_X_of_ne hi, smul_zero, map_zero]
  induction P using MvPolynomial.induction_on with
  | C c =>
    simp only [translatedPolynomial, MvPolynomial.aeval_C, Polynomial.algebraMap_apply,
      MvPolynomial.algebraMap_eq, polynomialDerivation_C, positiveDerivation_apply,
      MvPolynomial.pderiv_C, smul_zero, map_zero]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
    rw [map_mul, (polynomialDerivation j).leibniz, (positiveDerivation j).leibniz, hP, hX]
    simp only [smul_eq_mul, map_add, map_mul]

private def positiveCreationSum (B : FixedDualBases) (a : Charge lattice) (k : ℤ) :
    Polynomial Fock →ₗ[ℂ] Fock :=
  Polynomial.lsum fun d => LinearMap.mulLeft ℂ (creationCoeff B a (k + (d : ℤ)))

private theorem positiveCreationSum_monomial (B : FixedDualBases) (a : Charge lattice)
    (k : ℤ) (n : ℕ) (P : Fock) :
    positiveCreationSum B a k (Polynomial.monomial n P) = creationCoeff B a (k + (n : ℤ)) * P := by
  change (Polynomial.monomial n P).sum (fun d c => creationCoeff B a (k + (d : ℤ)) * c) = _
  exact Polynomial.sum_monomial_index P _ (mul_zero _)

private theorem positiveDerivation_creationSum (B : FixedDualBases) (a : Charge lattice)
    (j : Mode) (k : ℤ) (Q : Polynomial Fock) :
    positiveDerivation j (positiveCreationSum B a k Q) =
      positiveCreationSum B a k (polynomialDerivation j Q) +
        creationCoordinate B a j • positiveCreationSum B a (k - (frequency j : ℤ)) Q := by
  induction Q using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [map_add, hP, hQ, smul_add]
    abel
  | monomial n P =>
    have hshift : k + (n : ℤ) - (frequency j : ℤ) = k - (frequency j : ℤ) + (n : ℤ) := by
      omega
    have hcoeff : positiveDerivation j (creationCoeff B a (k + (n : ℤ))) =
        creationCoordinate B a j • creationCoeff B a (k - (frequency j : ℤ) + (n : ℤ)) := by
      rw [← hshift]
      exact positiveCurrent_creationCoeff B a j _
    simp only [positiveCreationSum_monomial, polynomialDerivation_monomial,
      Derivation.leibniz, smul_eq_mul, hcoeff, mul_smul_comm,
      mul_comm P (creationCoeff B a (k - (frequency j : ℤ) + (n : ℤ)))]

theorem oscillatorCoeff_positiveCurrent_commutator_apply (B : FixedDualBases)
    (a : Charge lattice) (j : Mode) (k : ℤ) (P : Fock) :
    positiveCurrent j (oscillatorCoeff B a k P) - oscillatorCoeff B a k (positiveCurrent j P) =
      creationCoordinate B a j • oscillatorCoeff B a (k - (frequency j : ℤ)) P := by
  change positiveDerivation j (positiveCreationSum B a k (translatedPolynomial B a P)) -
      positiveCreationSum B a k (translatedPolynomial B a (positiveDerivation j P)) =
    creationCoordinate B a j • positiveCreationSum B a (k - (frequency j : ℤ))
      (translatedPolynomial B a P)
  rw [positiveDerivation_creationSum, polynomialDerivation_translatedPolynomial,
    add_sub_cancel_left]

theorem oscillatorCoeff_positiveCurrent_commutator (B : FixedDualBases)
    (a : Charge lattice) (j : Mode) (k : ℤ) :
    positiveCurrent j * oscillatorCoeff B a k - oscillatorCoeff B a k * positiveCurrent j =
      creationCoordinate B a j • oscillatorCoeff B a (k - (frequency j : ℤ)) := by
  apply LinearMap.ext
  intro P
  simpa only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply] using
    oscillatorCoeff_positiveCurrent_commutator_apply B a j k P

/-- The positive current acts by the same Fock derivative in every momentum summand. -/
def positiveCurrentState (j : Mode) : Module.End ℂ State :=
  Finsupp.mapRange.linearMap (positiveCurrent j)

theorem positiveCurrentState_single (j : Mode) (p : Momentum) (P : Fock) :
    positiveCurrentState j (Finsupp.single p P) = Finsupp.single p (positiveCurrent j P) := by
  simp only [positiveCurrentState, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single]

theorem fieldCoeff_positiveCurrent_commutator (B : FixedDualBases)
    (a : Charge lattice) (j : Mode) (k : ℤ) :
    positiveCurrentState j * fieldCoeff B a k - fieldCoeff B a k * positiveCurrentState j =
      creationCoordinate B a j • fieldCoeff B a (k - (frequency j : ℤ)) := by
  apply Finsupp.lhom_ext
  intro p P
  have hdegree : k - (frequency j : ℤ) - momentumExponent a p =
      (k - momentumExponent a p) - (frequency j : ℤ) := by omega
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    positiveCurrentState_single, fieldCoeff_single, LinearMap.map_smul, Finsupp.smul_single,
    hdegree]
  rw [← Finsupp.single_sub, ← smul_sub, oscillatorCoeff_positiveCurrent_commutator_apply, smul_comm]

theorem concreteChargedField_coeff_positiveCurrent_commutator (a : Charge lattice)
    (j : Mode) (k : ℤ) (v : State) :
    positiveCurrentState j (((HahnModule.of ℂ).symm (concreteChargedField a v)).coeff k) -
        ((HahnModule.of ℂ).symm (concreteChargedField a (positiveCurrentState j v))).coeff k =
      creationCoordinate fixedDualBases a j •
        ((HahnModule.of ℂ).symm (concreteChargedField a v)).coeff (k - (frequency j : ℤ)) := by
  simp only [concreteChargedField, chargedField_coeff]
  simpa only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply] using
    DFunLike.congr_fun (fieldCoeff_positiveCurrent_commutator fixedDualBases a j k) v

end

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField
