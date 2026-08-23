/- GID: D5/S3/PrimeForms/PellFamilies/LocalPellPeriodicity
   generality: G
   mirror-B: D5/B/S3/PrimeForms/PellFamilies/LocalPellPeriodicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Pell-unit and unimodular recurrences are periodic modulo every prime power. -/

import D5.S3.PrimeForms.PellFamilies.CrossingPellFamily
import D5.S3.PrimeForms.PellFamilies.SqrtTwentyOnePellTower
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Algebra.Ring.Units
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/- Library-search audit trail (2026-08-24):
   * Existing Pell-family modules supply the repository family context; searches
     there and across D5 found no theorem on prime-power periodicity of their
     unit or unimodular recurrences.
   * Pinned Mathlib exact hits `Matrix.isUnit_iff_isUnit_det`,
     `RingHom.map_det`, `pow_orderOf_eq_one`, `orderOf_pos`, and
     `Matrix.det_fin_two_of` are applied below.
   * Repository and pinned-library searches for a theorem directly packaging
     prime-power reduction with pure matrix-orbit periodicity missed.
   * `loogle` and `leansearch` executables are absent from PATH. -/

noncomputable section

open Matrix

namespace D5.S3.PrimeForms.PellFamilies.LocalPellPeriodicity

/-- The multiplication matrix of a Pell unit and every integral unimodular
two-coordinate recurrence have pure-periodic reductions modulo each prime
power. Each public implication uses only the premise for its own generator. -/
theorem pell_unit_and_unimodular_recurrences_are_locally_periodic
    (discriminant unitX unitY : Int)
    (unitSeed recurrenceSeed : Fin 2 -> Int)
    (recurrence : Matrix (Fin 2) (Fin 2) Int)
    (prime exponent : Nat) (prime_is_prime : Nat.Prime prime) :
    let modulus := prime ^ exponent
    let reduceMatrix := fun matrix : Matrix (Fin 2) (Fin 2) Int =>
      matrix.map (Int.castRingHom (ZMod modulus))
    let reduceVector := fun vector : Fin 2 -> Int =>
      fun i => (vector i : ZMod modulus)
    let pellMatrix : Matrix (Fin 2) (Fin 2) Int :=
      !![unitX, discriminant * unitY; unitY, unitX]
    let pellOrbit := fun n =>
      (reduceMatrix pellMatrix) ^ n *ᵥ reduceVector unitSeed
    let recurrenceOrbit := fun n =>
      (reduceMatrix recurrence) ^ n *ᵥ reduceVector recurrenceSeed
    ((unitX ^ 2 - discriminant * unitY ^ 2 = 1 ∨
        unitX ^ 2 - discriminant * unitY ^ 2 = -1) ->
      exists period, 0 < period ∧ Function.Periodic pellOrbit period) ∧
    ((recurrence.det = 1 ∨ recurrence.det = -1) ->
      exists period, 0 < period ∧ Function.Periodic recurrenceOrbit period) := by
  dsimp only
  let modulus := prime ^ exponent
  let reduceMatrix := fun matrix : Matrix (Fin 2) (Fin 2) Int =>
    matrix.map (Int.castRingHom (ZMod modulus))
  let reduceVector := fun vector : Fin 2 -> Int =>
    fun i => (vector i : ZMod modulus)
  let pellMatrix : Matrix (Fin 2) (Fin 2) Int :=
    !![unitX, discriminant * unitY; unitY, unitX]
  letI : NeZero modulus := ⟨pow_ne_zero exponent prime_is_prime.ne_zero⟩
  have periodic_of_unimodular
      (integerMatrix : Matrix (Fin 2) (Fin 2) Int)
      (integerSeed : Fin 2 -> Int)
      (unimodular : integerMatrix.det = 1 ∨ integerMatrix.det = -1) :
      exists period, 0 < period ∧ Function.Periodic
        (fun n => (reduceMatrix integerMatrix) ^ n *ᵥ reduceVector integerSeed)
        period := by
    let observedMatrix := reduceMatrix integerMatrix
    have observed_det : observedMatrix.det =
        Int.castRingHom (ZMod modulus) integerMatrix.det := by
      simpa [observedMatrix, reduceMatrix] using
        (RingHom.map_det (Int.castRingHom (ZMod modulus)) integerMatrix).symm
    have observed_det_is_unit : IsUnit observedMatrix.det := by
      rw [observed_det]
      rcases unimodular with hdet | hdet
      · rw [hdet]
        simp
      · rw [hdet]
        simp
    have observed_is_unit : IsUnit observedMatrix :=
      (Matrix.isUnit_iff_isUnit_det observedMatrix).mpr observed_det_is_unit
    let observedUnit := observed_is_unit.unit
    have observed_pow_period :
        observedMatrix ^ orderOf observedUnit = 1 := by
      rw [← observed_is_unit.unit_spec, ← Units.val_pow_eq_pow_val,
        pow_orderOf_eq_one, Units.val_one]
    refine ⟨orderOf observedUnit, orderOf_pos observedUnit, ?_⟩
    intro n
    change observedMatrix ^ (n + orderOf observedUnit) *ᵥ
        reduceVector integerSeed =
      observedMatrix ^ n *ᵥ reduceVector integerSeed
    rw [pow_add, observed_pow_period, mul_one]
  constructor
  · intro pell_unit
    have pell_unimodular : pellMatrix.det = 1 ∨ pellMatrix.det = -1 := by
      rcases pell_unit with hpell | hpell
      · left
        simpa [pellMatrix, Matrix.det_fin_two_of, pow_two, mul_assoc] using hpell
      · right
        simpa [pellMatrix, Matrix.det_fin_two_of, pow_two, mul_assoc] using hpell
    exact periodic_of_unimodular pellMatrix unitSeed pell_unimodular
  · intro recurrence_unimodular
    exact periodic_of_unimodular recurrence recurrenceSeed recurrence_unimodular

#print axioms pell_unit_and_unimodular_recurrences_are_locally_periodic

end D5.S3.PrimeForms.PellFamilies.LocalPellPeriodicity
