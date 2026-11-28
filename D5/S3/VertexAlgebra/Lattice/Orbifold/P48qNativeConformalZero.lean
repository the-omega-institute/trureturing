/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeConformalZero
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The native P48q conformal zero mode and its ground-state spectrum. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qConformalVectorDecomposition
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFixedCurrentCasimir
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFixedCurrentIterate
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qMovingCurrentZero
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedStateEnergy
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qConcreteNeutralConformalMode
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeMonodromy

/-!
The actual P48q lattice conformal state has coefficient `totalLZero`
at cover exponent `-6` in the native Wick field. The abstract signed-mode
comparison uses the Bakalov–Kac current-pair iterates and the current and
vacuum restrictions of the state field.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeConformalZero

open HalfFockSpectralFiberSource (actualInverse)
open LatticeActualConformalState (omega)
open LatticeGeneratingFieldLocality (Carrier)
open P48qConformalVectorDecomposition (currentPair currentPair_comm omega_decomposition)
open P48qFixedCurrentCasimir (totalLZero_apply_fixedCurrent)
open P48qFixedCurrentIterate (FixedPairIterate currentMinusOne_zero_of_fixedPairIterate
  normalOrderedZero)
open P48qMomentumEnergy (fixedBasis fixedGramDual)
open P48qMovingCurrentZero (PairIterateAtZero firstCurrent firstDirection movingLZero
  movingLZero_apply nativeMoving_zero_of_iterate secondCurrent secondDirection)
open P48qThirdTwistedField (State)
open P48qTwistedChargeAction (lattice)
open P48qTwistedStateEnergy (totalLZero totalLZero_vacuum_spectrum)
open ThirdEigenspacePairing (p48qBasis p48qOppositeBasis)
open D5.S3.VertexAlgebra.Lattice.Automorphisms.ConformalGroundTransport (current)
open ThirdTwistedQuadratic (residue)
open scoped BigOperators

noncomputable section

variable (Ytw : Carrier lattice →ₗ[ℂ] ℤ → Module.End ℂ State)
variable
  (hFixedBasis : ∀ (i : Fin 16) (n : ℤ),
    Ytw (current lattice (fixedBasis i).val) (3 * n) =
      P48qFixedCurrentIterate.currentMode (fixedBasis i) n)
  (hFixedDual : ∀ (i : Fin 16) (n : ℤ),
    Ytw (current lattice (fixedGramDual fixedBasis i).val) (3 * n) =
      P48qFixedCurrentIterate.currentMode (fixedGramDual fixedBasis i) n)
  (hFirst : ∀ (i : Fin 16) (k : ℤ), k ∈ residue 1 →
    Ytw (firstCurrent i) k = P48qMovingCurrentZero.currentMode 1 i k)
  (hSecond : ∀ (i : Fin 16) (k : ℤ), k ∈ residue 2 →
    Ytw (secondCurrent i) k = P48qMovingCurrentZero.currentMode 2 i k)
  (hVac : Ytw (LatticeAllStateField.vacuum lattice) (-3) = LinearMap.id)
  (hFixedIterate : ∀ i : Fin 16, FixedPairIterate
    (current lattice (fixedBasis i).val)
    (current lattice (fixedGramDual fixedBasis i).val) Ytw)
  (hMovingIterate : ∀ i : Fin 16, PairIterateAtZero i Ytw)

include hFixedBasis hFixedDual hFirst hSecond hVac hFixedIterate hMovingIterate

/-- The cover index `3` is the coefficient of `z⁻²` in the field of the
native conformal state. The fixed and moving iterates give its full zero mode. -/
theorem native_conformal_zero_eq_totalLZero :
    Ytw (omega lattice (actualInverse lattice)) 3 = totalLZero := by
  have hζ : IsPrimitiveRoot (ThirdTwistedChargeCocycle.zeta : ℂ) 3 :=
    IsPrimitiveRoot.coe_units_iff.mpr ThirdTwistedChargeCocycle.zeta_primitive
  -- The first moving current is the canonical ζ² direction on the signed cover.
  have hMovingOrder :
      (∑ i : Fin 16, currentPair (p48qBasis hζ i) (p48qOppositeBasis hζ i)) =
        ∑ i : Fin 16, currentPair (firstDirection i) (secondDirection i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simpa only [firstDirection, secondDirection] using
      currentPair_comm (p48qBasis hζ i) (p48qOppositeBasis hζ i)
  have hFixedZero :
      Ytw (∑ i : Fin 16, currentPair (fixedBasis i) (fixedGramDual fixedBasis i)) 3 =
        ∑ i : Fin 16, normalOrderedZero (fixedBasis i) (fixedGramDual fixedBasis i) := by
    rw [map_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ =>
      currentMinusOne_zero_of_fixedPairIterate (fixedBasis i) (fixedGramDual fixedBasis i)
        Ytw (hFixedBasis i) (hFixedDual i) (hFixedIterate i)
  have hMovingZero :
      Ytw (∑ i : Fin 16, currentPair (firstDirection i) (secondDirection i)) 3 =
        movingLZero :=
    nativeMoving_zero_of_iterate Ytw hFirst hSecond hVac hMovingIterate
  calc
    Ytw (omega lattice (actualInverse lattice)) 3 =
        (2 : ℂ)⁻¹ • (∑ i : Fin 16,
          normalOrderedZero (fixedBasis i) (fixedGramDual fixedBasis i)) + movingLZero := by
      rw [omega_decomposition hζ, hMovingOrder]
      simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, hFixedZero, hMovingZero]
    _ = totalLZero := by
      apply LinearMap.ext
      intro w
      apply Finsupp.ext
      intro p
      simp only [LinearMap.add_apply, Finsupp.add_apply, movingLZero_apply,
        totalLZero_apply_fixedCurrent, Nat.dvd_iff_mod_eq_zero, add_assoc]

/-- Under the generator-level restrictions and iterates, the native twisted
conformal zero mode has minimum `16 / 9` and ground line `ℂ(e₀ ⊗ 1)`. -/
theorem native_conformal_ground_spectrum :
    IsLeast {x : ℝ | ∃ v : State, v ≠ 0 ∧
      Ytw (omega lattice (actualInverse lattice)) 3 v = (x : ℂ) • v} (16 / 9) ∧
    (Ytw (omega lattice (actualInverse lattice)) 3).eigenspace (16 / 9 : ℂ) =
      Submodule.span ℂ ({P48qTwistedStateEnergy.vacuum} : Set State) ∧
    Module.finrank ℂ ((Ytw (omega lattice (actualInverse lattice)) 3).eigenspace (16 / 9 : ℂ)) =
      1 := by
  rw [native_conformal_zero_eq_totalLZero Ytw hFixedBasis hFixedDual hFirst hSecond
    hVac hFixedIterate hMovingIterate]
  exact totalLZero_vacuum_spectrum

end

section NativeField

open scoped VertexOperator
open P48qAllJetWickField (allJetCoeff nativeField pairWeight singletonWeight singletonWeight_first)
open P48qArbitraryWickRecursion (normalWick_two)
open P48qConcreteNeutralConformalMode (conformalState conformal_coeff_neg_six_eq_totalLZero)
open P48qJetContractions (pairJetCoeff_one_one)
open P48qJetNormalOrdering (normalOrderedCoeff normalOrderedCoeff_allFirst
  normalOrderedField_coeff normalOrderedField_nil)
open P48qQuadraticStateField (correction correction_eq currentProduct movingGram_swap
  neutralStates neutralStateField neutralStateField_pair_coeff)
open P48qThirdTwistedField (Cartan)
open P48qTwistedGeneratorVacuum (concreteChargedField_zero_coeff)
open P48qTwistedHeisenberg (movingGram project projectAt projectAt_eq_fourier
  project_action project_of_action)
open ThirdEigenspacePairing (p48qForm)

open private formSymmetric from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField
open private project_adjoint from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedHeisenberg
open private contraction_at_zero normalOrderedSecondCoeff_zero_charge from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedTwoCurrentIterate
open private currentPolynomial currentPair_eq_polynomial from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qQuadraticStateField
open private nativeCoeff nativeCoeff_jetWord from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeMonodromy
open private conformalState_decomposition from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qConcreteNeutralConformalMode

local notation "ζ" => (ThirdTwistedChargeCocycle.zeta : ℂ)

private theorem moving_pairing (u v : Cartan) :
    p48qForm (projectAt 1 u) (projectAt 2 v) = movingGram 1 u v := by
  have hζ : ζ ^ 3 = 1 :=
    (IsPrimitiveRoot.coe_units_iff.mpr ThirdTwistedChargeCocycle.zeta_primitive).pow_eq_one
  have hζ₂ : (ζ ^ 2) ^ 3 = 1 := by rw [pow_right_comm, hζ, one_pow]
  unfold movingGram
  rw [projectAt_eq_fourier 1 u, projectAt_eq_fourier 2 v]
  change p48qForm (project (ζ ^ 1) u) (project (ζ ^ 2) v) = p48qForm (project (ζ ^ 1) u) v
  simp only [pow_one]
  calc
    _ = p48qForm u (project (ζ ^ 2) v) := by
      rw [project_adjoint ζ hζ,
        project_of_action _ hζ₂ _ (project_action _ hζ₂ v)]
    _ = _ := (project_adjoint ζ hζ u v).symm

private theorem first_pairWeight (u v : Cartan) :
    pairWeight (u, 1) (v, 1) = correction u v := by
  have h₂ : p48qForm (projectAt 2 u) (projectAt 1 v) = movingGram 2 u v :=
    (formSymmetric.eq _ _).trans ((moving_pairing v u).trans (movingGram_swap v u))
  simp only [pairWeight, PNat.val_ofNat, pairJetCoeff_one_one, moving_pairing, h₂, correction_eq]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Coefficient comparison reduces the all-jet recursion and the neutral subtype field.
private theorem allJetCoeff_firstPair_zero_charge (u v : Cartan) (k : ℤ) :
    allJetCoeff 0 k [(u, 1), (v, 1)] =
      HVertexOperator.coeff (neutralStateField (currentProduct u v 0)) k := by
  rw [allJetCoeff, normalWick_two]
  change normalOrderedCoeff 0 (k + 3 * (2 - 2)) [(u, 1), (v, 1)] +
    singletonWeight 0 (v, 1) • normalOrderedCoeff 0 (k + 3 * (2 - 1)) [(u, 1)] +
    singletonWeight 0 (u, 1) • normalOrderedCoeff 0 (k + 3 * (2 - 1)) [(v, 1)] +
    (singletonWeight 0 (u, 1) * singletonWeight 0 (v, 1) + pairWeight (u, 1) (v, 1)) •
      normalOrderedCoeff 0 (k + 3 * (2 - 0)) [] = _
  simp only [singletonWeight_first, contraction_at_zero, neg_zero, zero_smul, zero_mul,
    add_zero, zero_add, first_pairWeight,
    show (3 : ℤ) * (2 - 2) = 0 by decide, show (3 : ℤ) * (2 - 0) = 6 by decide]
  have hnormal := normalOrderedCoeff_allFirst 0 k [u, v]
  change normalOrderedCoeff 0 k [(u, 1), (v, 1)] = _ at hnormal
  rw [hnormal, P48qSignedNormalWord.normalOrderedCoeff_pair,
    normalOrderedSecondCoeff_zero_charge, ← normalOrderedField_coeff, normalOrderedField_nil,
    concreteChargedField_zero_coeff]
  have hpair := neutralStateField_pair_coeff u v (-k - 6)
  rw [show -(-k - 6) - 6 = k by omega] at hpair
  rw [hpair]
  by_cases hk : k + 6 = 0
  · rw [ite_eq_left hk, ite_eq_left (show -k - 6 = 0 by omega)]
    rfl
  · simp only [ite_eq_right hk, ite_eq_right (show -k - 6 ≠ 0 by omega), smul_zero]

set_option maxRecDepth 100000 in
private theorem nativeField_pair (u v : Cartan) :
    nativeField (currentPair u v) = neutralStateField (currentProduct u v 0) := by
  apply HVertexOperator.coeff_inj
  funext k
  have h := nativeCoeff_jetWord 0 k [(u, 1), (v, 1)] []
  change nativeCoeff 0 k ((currentPolynomial u * (currentPolynomial v * 1)) * 1) =
    allJetCoeff 0 k [(u, 1), (v, 1)] at h
  simp only [mul_one] at h
  rw [currentPair_eq_polynomial]
  change nativeCoeff 0 k (currentPolynomial u * currentPolynomial v) = _
  rw [h, allJetCoeff_firstPair_zero_charge]

set_option maxRecDepth 100000 in
/-- The coefficient of `x⁻⁶` (`z⁻²` for `z = x³`) in the native Wick field
of the actual conformal state is the Fock energy operator on the full carrier. -/
theorem native_conformal_coeff_neg_six_eq_totalLZero :
    HVertexOperator.coeff (nativeField (omega lattice (actualInverse lattice))) (-6) =
      totalLZero := by
  have hpair (u v : Cartan) :
      (nativeField.comp neutralStates.subtype) (currentProduct u v 0) =
        neutralStateField (currentProduct u v 0) :=
    nativeField_pair u v
  have hfield : nativeField (omega lattice (actualInverse lattice)) =
      neutralStateField conformalState := by
    change (nativeField.comp neutralStates.subtype) conformalState = _
    rw [conformalState_decomposition]
    simp only [map_add, map_smul, map_sum, hpair]
  rw [hfield, conformal_coeff_neg_six_eq_totalLZero]

#print axioms allJetCoeff_firstPair_zero_charge
#print axioms nativeField_pair
#print axioms native_conformal_coeff_neg_six_eq_totalLZero

end NativeField

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeConformalZero

#print axioms D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeConformalZero.native_conformal_zero_eq_totalLZero
#print axioms D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeConformalZero.native_conformal_ground_spectrum
