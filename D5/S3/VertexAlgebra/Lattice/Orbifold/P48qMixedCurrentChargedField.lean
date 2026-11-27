/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qMixedCurrentChargedField
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The negative current commutator from translation in the inverse cover variable. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFixedDualBases

/-!
The negative-current commutator with the P48q twisted charged field in the
cover coordinate `x`. The translation polynomial uses `u = x⁻¹`, so a
monomial of degree `n` in `u` shifts the oscillator coefficient index by `+n`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField

open LatticeGeneratingFieldLocality (Charge)
open P48qTwistedChargeAction (lattice Momentum)
open MvPolynomial (X)

noncomputable section

private def creationSum (B : FixedDualBases) (a : Charge lattice) (k : ℤ) :
    Polynomial Fock →ₗ[ℂ] Fock :=
  Polynomial.lsum fun d => LinearMap.mulLeft ℂ (creationCoeff B a (k + (d : ℤ)))

private theorem creationSum_monomial (B : FixedDualBases) (a : Charge lattice) (k : ℤ)
    (n : ℕ) (b : Fock) :
    creationSum B a k (Polynomial.monomial n b) = creationCoeff B a (k + (n : ℤ)) * b := by
  change (Polynomial.monomial n b).sum (fun d c => creationCoeff B a (k + (d : ℤ)) * c) = _
  exact Polynomial.sum_monomial_index b _ (mul_zero _)

private theorem creationSum_monomial_mul (B : FixedDualBases) (a : Charge lattice) (k : ℤ)
    (n : ℕ) (b : Fock) (Q : Polynomial Fock) :
    creationSum B a k (Polynomial.monomial n b * Q) =
      b * creationSum B a (k + (n : ℤ)) Q := by
  induction Q using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [mul_add, map_add, hP, hQ]
  | monomial d c =>
    simp only [Polynomial.monomial_mul_monomial, creationSum_monomial, Nat.cast_add, add_assoc]
    ac_rfl

/-- The current mode at `-(frequency j)/3` acts by creation. -/
def negativeCurrent (j : Mode) : Module.End ℂ Fock :=
  LinearMap.mulLeft ℂ (X j)

/-- Subtracting the translated multiplication cancels its constant term and
keeps the positive pairing from the degree-`frequency j` translation term. -/
theorem oscillatorCoeff_commutator_apply (B : FixedDualBases) (a : Charge lattice)
    (j : Mode) (k : ℤ) (P : Fock) :
    X j * oscillatorCoeff B a k P - oscillatorCoeff B a k (X j * P) =
      annihilationPairing B a j • oscillatorCoeff B a (k + (frequency j : ℤ)) P := by
  have htranslate : translatedPolynomial B a (X j * P) =
      (Polynomial.monomial 0 (X j : Fock) -
        Polynomial.monomial (frequency j) (annihilationPairing B a j • (1 : Fock))) *
        translatedPolynomial B a P := by
    simp only [map_mul, translatedPolynomial, MvPolynomial.aeval_X, translationVariable,
      Polynomial.C_mul_X_pow_eq_monomial, Polynomial.monomial_zero_left]
  change X j * creationSum B a k (translatedPolynomial B a P) -
      creationSum B a k (translatedPolynomial B a (X j * P)) =
    annihilationPairing B a j • creationSum B a (k + (frequency j : ℤ)) (translatedPolynomial B a P)
  simp only [htranslate, sub_mul, map_sub, creationSum_monomial_mul,
    Nat.cast_zero, add_zero, smul_mul_assoc, one_mul, sub_sub_cancel]

theorem oscillatorCoeff_commutator (B : FixedDualBases) (a : Charge lattice) (j : Mode) (k : ℤ) :
    negativeCurrent j * oscillatorCoeff B a k - oscillatorCoeff B a k * negativeCurrent j =
      annihilationPairing B a j • oscillatorCoeff B a (k + (frequency j : ℤ)) := by
  apply LinearMap.ext
  intro P
  simpa only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    negativeCurrent, LinearMap.mulLeft_apply] using oscillatorCoeff_commutator_apply B a j k P

/-- Apply the same negative current in each momentum summand. -/
def negativeCurrentState (j : Mode) : Module.End ℂ State :=
  Finsupp.mapRange.linearMap (negativeCurrent j)

theorem negativeCurrentState_apply (j : Mode) (v : State) (p : Momentum) :
    negativeCurrentState j v p = X j * v p := by
  simp only [negativeCurrentState, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply,
    negativeCurrent, LinearMap.mulLeft_apply]

theorem negativeCurrentState_single (j : Mode) (p : Momentum) (P : Fock) :
    negativeCurrentState j (Finsupp.single p P) = Finsupp.single p (X j * P) := by
  simp only [negativeCurrentState, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single,
    negativeCurrent, LinearMap.mulLeft_apply]

/-- The oscillator commutator lifts through the momentum shift and its charge phase. -/
theorem fieldCoeff_commutator (B : FixedDualBases) (a : Charge lattice) (j : Mode) (k : ℤ) :
    negativeCurrentState j * fieldCoeff B a k - fieldCoeff B a k * negativeCurrentState j =
      annihilationPairing B a j • fieldCoeff B a (k + (frequency j : ℤ)) := by
  apply Finsupp.lhom_ext
  intro p P
  have hdegree : k + (frequency j : ℤ) - momentumExponent a p =
      (k - momentumExponent a p) + (frequency j : ℤ) := by omega
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    negativeCurrentState_single, fieldCoeff_single, Finsupp.smul_single, mul_smul_comm, hdegree]
  rw [← Finsupp.single_sub, ← smul_sub, oscillatorCoeff_commutator_apply, smul_comm]

/-- Coefficientwise commutator for the charged field with the fixed dual bases supplied. -/
theorem concreteChargedField_coeff_commutator (a : Charge lattice) (j : Mode) (k : ℤ) (v : State) :
    negativeCurrentState j (((HahnModule.of ℂ).symm (concreteChargedField a v)).coeff k) -
        ((HahnModule.of ℂ).symm (concreteChargedField a (negativeCurrentState j v))).coeff k =
      annihilationPairing fixedDualBases a j •
        ((HahnModule.of ℂ).symm (concreteChargedField a v)).coeff (k + (frequency j : ℤ)) := by
  simp only [concreteChargedField, chargedField_coeff]
  simpa only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply] using
    DFunLike.congr_fun (fieldCoeff_commutator fixedDualBases a j k) v

end

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField

#print axioms D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField.concreteChargedField_coeff_commutator
