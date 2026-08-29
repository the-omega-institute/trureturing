/- GID: D5/S3/ConceptDynamics/ObservationOrder/TypedPrimeLanguageHierarchy
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/ObservationOrder/TypedPrimeLanguageHierarchy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Typed prime readouts are strictly ordered; degenerate cases collapse. -/
/- Library-search audit trail (2026-08-29):
   * Lean, Blueprint, digestion-atom, source-volume, and Library searches found no theorem
     stating either strict relation through the repository's canonical `Refines` predicate.
   * `PrimeExponentBijection` supplies `primeExponentLanguage`; its finite support is reused.
   * `DiagonalPhaseBlindness` proves a nearby observable fact, but not through `Refines`,
     `DensityState`, or `primeDephasing`; it therefore does not cover either theorem below.
   * Pinned Mathlib supplies the natural radical, matrix positivity, and finite supports.
     No exact typed language-hierarchy theorem was found. -/

import D5.S3.ConceptDynamics.ConceptJoinUniversal
import D5.S3.Factorization.ExponentCoordinates.PrimeExponentBijection
import D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
import D5.S3.Quantum.FixedAlgebra.PrimeDephasingRefinementAbsorption
import D5.S3.Quantum.QubitWitnesses
import Mathlib.RingTheory.Radical.NatInt

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ConceptDynamics.ObservationOrder.TypedPrimeLanguageHierarchy

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.Factorization.PrimePowers.PrimeExponentLanguageComplete
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.FiniteDimensional
open D5.S3.Quantum.FixedAlgebra.PrimeDephasingRefinementAbsorption
open D5.S3.Quantum.FixedAlgebra.SingletonRecordClassicality
open D5.S3.Quantum.QubitWitnesses
open UniqueFactorizationMonoid
open scoped CStarAlgebra ComplexOrder MatrixOrder

/-- The prime-support language forgets the nonzero multiplicities in the valuation language. -/
def primeSupportLanguage (n : ℕ+) : Finset ℕ :=
  (primeExponentLanguage n).support

/-- Two and four are the named same-radical, different-multiplicity witness. -/
def supportMultiplicityWitness : ℕ+ × ℕ+ :=
  (2, 4)

/-- The named arithmetic witness has one radical and support but distinct valuations. -/
theorem support_multiplicity_witness :
    let pair := supportMultiplicityWitness
    radical (pair.1 : ℕ) = radical (pair.2 : ℕ) ∧
      primeSupportLanguage pair.1 = primeSupportLanguage pair.2 ∧
      primeExponentLanguage pair.1 ≠ primeExponentLanguage pair.2 := by
  have hradicalTwo : radical (2 : ℕ) = 2 := by
    simpa using radical_of_prime (Nat.prime_iff.mp Nat.prime_two)
  have hradicalFour : radical (4 : ℕ) = 2 := by
    simpa using radical_pow_of_prime
      (Nat.prime_iff.mp Nat.prime_two) (n := 2) (by decide)
  have htwo :
      primeExponentLanguage (2 : ℕ+) = Finsupp.single 2 1 := by
    simpa [primeExponentLanguage] using
      Nat.Prime.factorization_pow (p := 2) (k := 1) Nat.prime_two
  have hfour :
      primeExponentLanguage (4 : ℕ+) = Finsupp.single 2 2 := by
    simpa [primeExponentLanguage] using
      Nat.Prime.factorization_pow (p := 2) (k := 2) Nat.prime_two
  dsimp only [supportMultiplicityWitness]
  change radical (2 : ℕ) = radical (4 : ℕ) ∧
    primeSupportLanguage 2 = primeSupportLanguage 4 ∧
      primeExponentLanguage 2 ≠ primeExponentLanguage 4
  refine ⟨hradicalTwo.trans hradicalFour.symm, ?_, ?_⟩
  · change (primeExponentLanguage 2).support =
      (primeExponentLanguage 4).support
    rw [htwo, hfour]
    simp
  · rw [htwo, hfour]
    intro hequal
    have hatTwo := DFunLike.congr_fun hequal 2
    norm_num at hatTwo

#print axioms support_multiplicity_witness

/-- On positive naturals, support is strictly coarser than the full valuation language. -/
theorem support_strictly_coarser_than_valuation :
    Refines
        (primeSupportLanguage : Concept ℕ+ (Finset ℕ))
        (primeExponentLanguage : Concept ℕ+ (ℕ →₀ ℕ)) ∧
      ¬Refines
        (primeExponentLanguage : Concept ℕ+ (ℕ →₀ ℕ))
        (primeSupportLanguage : Concept ℕ+ (Finset ℕ)) := by
  constructor
  · exact ⟨Finsupp.support, rfl⟩
  · rintro ⟨factor, hfactor⟩
    have hwitness := support_multiplicity_witness
    apply hwitness.2.2
    calc
      primeExponentLanguage supportMultiplicityWitness.1 =
          factor (primeSupportLanguage supportMultiplicityWitness.1) :=
        congrFun hfactor supportMultiplicityWitness.1
      _ = factor (primeSupportLanguage supportMultiplicityWitness.2) := by
        rw [hwitness.2.1]
      _ = primeExponentLanguage supportMultiplicityWitness.2 :=
        (congrFun hfactor supportMultiplicityWitness.2).symm

#print axioms support_strictly_coarser_than_valuation

/-- The one-prime profile that makes the requested qubit dephasing fully diagonal. -/
def qubitPrimeValuation : Fin 2 → Unit → Fin 2 :=
  fun i _ => i

/-- The prime-diagonal language on qubit density states. -/
def qubitPrimeDiagonalLanguage (rho : DensityState (Fin 2)) : QubitMatrix :=
  primeDephasing ({()} : Finset Unit) qubitPrimeValuation rho.1

/-- The full operator language remembers the entire density operator. -/
def qubitOperatorLanguage (rho : DensityState (Fin 2)) : QubitMatrix :=
  rho.1

private theorem equal_superposition_posSemidef :
    equalSuperpositionDensity.PosSemidef := by
  have hstarTwo : starRingEnd ℂ (2 : ℂ) = 2 := by
    rw [starRingEnd_apply, star_ofNat]
  have hpositive :=
    (Matrix.PosSemidef.one : (1 : QubitMatrix).PosSemidef).mul_mul_conjTranspose_same
      equalSuperpositionDensity
  convert hpositive using 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [equalSuperpositionDensity, Matrix.mul_apply, Fin.sum_univ_two,
      hstarTwo]

private theorem phase_flip_posSemidef :
    (qubitZ * equalSuperpositionDensity * qubitZ).PosSemidef := by
  have hpositive := equal_superposition_posSemidef.mul_mul_conjTranspose_same qubitZ
  rw [← Matrix.star_eq_conjTranspose, qubit_weyl_star.2.2.1] at hpositive
  exact hpositive

private theorem representative_has_profile
    {d : Nat} {Profile : Type*} (classOf : Fin d → Profile) (i : Fin d) :
    classOf (profileClassRepresentative classOf i) = classOf i := by
  classical
  have nonempty : (Finset.univ.filter fun j => classOf j = classOf i).Nonempty :=
    ⟨i, by simp⟩
  exact (Finset.mem_filter.mp (Finset.min'_mem _ nonempty)).2

private theorem qubit_prime_dephasing_eq_diagonal :
    primeDephasing ({()} : Finset Unit) qubitPrimeValuation =
      fun rho : QubitMatrix => Matrix.diagonal fun i => rho i i := by
  have hprofiles :
      restrictedPrimeProfile ({()} : Finset Unit) qubitPrimeValuation (0 : Fin 2) ≠
        restrictedPrimeProfile ({()} : Finset Unit) qubitPrimeValuation 1 := by
    intro hequal
    have hatUnit := congrFun hequal ⟨(), by simp⟩
    exact Fin.zero_ne_one hatUnit
  have hrepresentatives :
      profileClassRepresentative
          (restrictedPrimeProfile ({()} : Finset Unit) qubitPrimeValuation) 0 ≠
        profileClassRepresentative
          (restrictedPrimeProfile ({()} : Finset Unit) qubitPrimeValuation) 1 := by
    intro hequal
    apply hprofiles
    rw [← representative_has_profile
      (restrictedPrimeProfile ({()} : Finset Unit) qubitPrimeValuation) 0,
      ← representative_has_profile
        (restrictedPrimeProfile ({()} : Finset Unit) qubitPrimeValuation) 1,
      hequal]
  funext rho
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [primeDephasing, recordChannel, recordGram, orthogonalProfileRecord,
      hrepresentatives, Ne.symm hrepresentatives]

/-- Two density operators with equal diagonal and opposite relative phase. -/
def relativePhaseDensityWitness : DensityState (Fin 2) × DensityState (Fin 2) := by
  refine (⟨CStarMatrix.ofMatrixStarAlgEquiv equalSuperpositionDensity, ?_, ?_⟩,
    ⟨CStarMatrix.ofMatrixStarAlgEquiv
      (qubitZ * equalSuperpositionDensity * qubitZ), ?_, ?_⟩)
  · exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv equal_superposition_posSemidef.nonneg
  · change Matrix.trace equalSuperpositionDensity = 1
    norm_num [equalSuperpositionDensity, Matrix.trace, Fin.sum_univ_two]
  · exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv phase_flip_posSemidef.nonneg
  · change Matrix.trace (qubitZ * equalSuperpositionDensity * qubitZ) = 1
    norm_num [equalSuperpositionDensity, qubitZ, Matrix.trace, Matrix.mul_apply,
      Fin.sum_univ_two]

/-- The named density witness is prime-diagonally equal but operator-distinct. -/
theorem relative_phase_density_witness :
    let pair := relativePhaseDensityWitness
    pair.1 ≠ pair.2 ∧
      qubitPrimeDiagonalLanguage pair.1 = qubitPrimeDiagonalLanguage pair.2 ∧
      qubitOperatorLanguage pair.1 ≠ qubitOperatorLanguage pair.2 := by
  dsimp only
  have hoperator :
      qubitOperatorLanguage relativePhaseDensityWitness.1 ≠
        qubitOperatorLanguage relativePhaseDensityWitness.2 := by
    intro hequal
    have hentry := congrArg (fun matrix : QubitMatrix => matrix 0 1) hequal
    change equalSuperpositionDensity 0 1 =
      (qubitZ * equalSuperpositionDensity * qubitZ) 0 1 at hentry
    norm_num [equalSuperpositionDensity, qubitZ, Matrix.mul_apply,
      Fin.sum_univ_two] at hentry
  have hdiagonalEntry (i : Fin 2) :
      qubitOperatorLanguage relativePhaseDensityWitness.1 i i =
        qubitOperatorLanguage relativePhaseDensityWitness.2 i i := by
    change equalSuperpositionDensity i i =
      (qubitZ * equalSuperpositionDensity * qubitZ) i i
    fin_cases i <;>
      norm_num [equalSuperpositionDensity, qubitZ, Matrix.mul_apply,
        Fin.sum_univ_two]
  have hdiagonal :
      qubitPrimeDiagonalLanguage relativePhaseDensityWitness.1 =
        qubitPrimeDiagonalLanguage relativePhaseDensityWitness.2 := by
    rw [qubitPrimeDiagonalLanguage, qubitPrimeDiagonalLanguage,
      qubit_prime_dephasing_eq_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simpa [qubitOperatorLanguage] using hdiagonalEntry i
    · simp [hij]
  refine ⟨?_, hdiagonal, hoperator⟩
  intro hequal
  exact hoperator (congrArg qubitOperatorLanguage hequal)

#print axioms relative_phase_density_witness

/-- On qubit density states, the prime-diagonal language is strictly coarser than operators. -/
theorem prime_diagonal_strictly_coarser_than_operator :
    Refines
        (qubitPrimeDiagonalLanguage : Concept (DensityState (Fin 2)) QubitMatrix)
        (qubitOperatorLanguage : Concept (DensityState (Fin 2)) QubitMatrix) ∧
      ¬Refines
        (qubitOperatorLanguage : Concept (DensityState (Fin 2)) QubitMatrix)
        (qubitPrimeDiagonalLanguage : Concept (DensityState (Fin 2)) QubitMatrix) := by
  constructor
  · exact ⟨primeDephasing ({()} : Finset Unit) qubitPrimeValuation, rfl⟩
  · rintro ⟨factor, hfactor⟩
    have hwitness := relative_phase_density_witness
    apply hwitness.2.2
    calc
      qubitOperatorLanguage relativePhaseDensityWitness.1 =
          factor (qubitPrimeDiagonalLanguage relativePhaseDensityWitness.1) :=
        congrFun hfactor relativePhaseDensityWitness.1
      _ = factor (qubitPrimeDiagonalLanguage relativePhaseDensityWitness.2) := by
        rw [hwitness.2.1]
      _ = qubitOperatorLanguage relativePhaseDensityWitness.2 :=
        (congrFun hfactor relativePhaseDensityWitness.2).symm

#print axioms prime_diagonal_strictly_coarser_than_operator

/- Degenerate audit: exact equality, exponent zero, single-prime support, empty and singleton
   index types, constant maps, and identical quantum phases do not produce strictness. -/
example (n : ℕ+) :
    radical (n : ℕ) = radical (n : ℕ) ∧
      primeSupportLanguage n = primeSupportLanguage n ∧
      primeExponentLanguage n = primeExponentLanguage n :=
  ⟨rfl, rfl, rfl⟩

example : primeExponentLanguage (1 : ℕ+) = 0 := by
  simp [primeExponentLanguage]

example : (0 : ℕ).factorization = 0 := by
  simp

example : primeSupportLanguage (8 : ℕ+) = {2} := by
  have height : primeExponentLanguage (8 : ℕ+) = Finsupp.single 2 3 := by
    simpa [primeExponentLanguage] using
      Nat.Prime.factorization_pow (p := 2) (k := 3) Nat.prime_two
  change (primeExponentLanguage (8 : ℕ+)).support = {2}
  rw [height]
  simp

example :
    primeSupportLanguage supportMultiplicityWitness.1 =
        primeSupportLanguage supportMultiplicityWitness.2 ∧
      primeExponentLanguage supportMultiplicityWitness.1 ≠
        primeExponentLanguage supportMultiplicityWitness.2 :=
  support_multiplicity_witness.2

example (coarse fine : Empty → Unit) :
    Refines (coarse : Concept Empty Unit) (fine : Concept Empty Unit) ∧
      Refines (fine : Concept Empty Unit) (coarse : Concept Empty Unit) := by
  constructor <;> refine ⟨id, ?_⟩ <;> funext x <;> exact x.elim

example (coarse fine : Unit → Unit) :
    Refines (coarse : Concept Unit Unit) (fine : Concept Unit Unit) ∧
      Refines (fine : Concept Unit Unit) (coarse : Concept Unit Unit) := by
  constructor <;> refine ⟨id, ?_⟩ <;> funext x <;> exact Subsingleton.elim _ _

example {X : Type*} :
    Refines ((fun _ : X => ()) : Concept X Unit) (id : Concept X X) :=
  ⟨fun _ => (), rfl⟩

example (rho : DensityState (Fin 2)) :
    qubitPrimeDiagonalLanguage rho = qubitPrimeDiagonalLanguage rho ∧
      qubitOperatorLanguage rho = qubitOperatorLanguage rho :=
  ⟨rfl, rfl⟩

example (valuation : Fin 0 → Empty → Unit) :
    primeDephasing (∅ : Finset Empty) valuation = id :=
  prime_dephasing_empty valuation

end D5.S3.ConceptDynamics.ObservationOrder.TypedPrimeLanguageHierarchy
