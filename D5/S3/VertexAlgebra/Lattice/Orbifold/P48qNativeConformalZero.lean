import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qConformalVectorDecomposition
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFixedCurrentCasimir
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFixedCurrentIterate
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qMovingCurrentZero
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedStateEnergy

/-!
The actual P48q lattice conformal state's twisted mode at cover index `3`.
The comparison and ground spectrum are conditional on the Bakalov–Kac
current-pair iterates and the current and vacuum restrictions of the state field.
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
open ThirdTwistedIterate (currentAlong)
open ThirdTwistedQuadratic (residue)
open scoped BigOperators

noncomputable section

variable (Ytw : Carrier lattice →ₗ[ℂ] ℤ → Module.End ℂ State)
variable
  (hFixedBasis : ∀ (i : Fin 16) (n : ℤ),
    Ytw (currentAlong lattice (fixedBasis i).val) (3 * n) =
      P48qFixedCurrentIterate.currentMode (fixedBasis i) n)
  (hFixedDual : ∀ (i : Fin 16) (n : ℤ),
    Ytw (currentAlong lattice (fixedGramDual fixedBasis i).val) (3 * n) =
      P48qFixedCurrentIterate.currentMode (fixedGramDual fixedBasis i) n)
  (hFirst : ∀ (i : Fin 16) (k : ℤ), k ∈ residue 1 →
    Ytw (firstCurrent i) k = P48qMovingCurrentZero.currentMode 1 i k)
  (hSecond : ∀ (i : Fin 16) (k : ℤ), k ∈ residue 2 →
    Ytw (secondCurrent i) k = P48qMovingCurrentZero.currentMode 2 i k)
  (hVac : Ytw (LatticeAllStateField.vacuum lattice) (-3) = LinearMap.id)
  (hFixedIterate : ∀ i : Fin 16, FixedPairIterate
    (currentAlong lattice (fixedBasis i).val)
    (currentAlong lattice (fixedGramDual fixedBasis i).val) Ytw)
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

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeConformalZero

#print axioms D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeConformalZero.native_conformal_zero_eq_totalLZero
#print axioms D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeConformalZero.native_conformal_ground_spectrum
