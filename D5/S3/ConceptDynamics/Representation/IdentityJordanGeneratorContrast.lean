/- GID: D5/S3/ConceptDynamics/Representation/IdentityJordanGeneratorContrast
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Representation/IdentityJordanGeneratorContrast
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Identity and Jordan actions differ; charpoly and degenerate cases are audited. -/

import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Ring.Action.ConjAct
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/- Library-search audit trail (2026-08-25):
   * The host exposed no `lean_loogle`, `lean_leansearch`, or `lean_local_search` tool,
     so no LSP-search hit is claimed. The Lean skill's pinned local search was used.
   * Searches for `Matrix.minpoly`, `LinearMap.minpoly`, `minpoly`, `Matrix.IsConj`,
     `Matrix.charpoly`, and `Module.End.eigenvalue` found `minpoly.one`,
     `minpoly.two_le_natDegree_iff`, `Matrix.minpoly_dvd_charpoly`,
     `Matrix.charpoly_one`, and `Matrix.charpoly_fin_two`.
   * Mathlib defines matrix similarity through the generic `IsConj`. No pinned theorem
     stating invariance of `minpoly` under `IsConj` was found, so the short missing step
     below uses `minpoly.algEquiv_eq` for the existing unit-conjugation algebra equivalence.
   * No semisimplification interface was found. The fourth source assertion is therefore
     represented by the common split characteristic polynomial `(X - 1)^2`; in this
     two-dimensional rational example it records the two trivial composition factors.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Representation.IdentityJordanGeneratorContrast

open Matrix Polynomial

/-- The concrete two-dimensional matrix carrier over the rational field. -/
abbrev GeneratorMatrix := Matrix (Fin 2) (Fin 2) ℚ

/-- The chosen generator of the free cyclic group `Multiplicative ℤ`. -/
def cycleGenerator : Multiplicative ℤ :=
  Multiplicative.ofAdd 1

/-- The identity generator action. -/
def rhoZeroGenerator : GeneratorMatrix :=
  !![1, 0; 0, 1]

/-- The unipotent Jordan generator action with nonzero nilpotent part. -/
def rhoUnipotentGenerator : GeneratorMatrix :=
  !![1, 1; 0, 1]

/-- The identity generator on the one-dimensional comparison carrier. -/
def rhoZeroGeneratorOne : Matrix (Fin 1) (Fin 1) ℚ :=
  1

/-- The one-dimensional Jordan analogue; no nonzero off-diagonal entry exists. -/
def rhoUnipotentGeneratorOne : Matrix (Fin 1) (Fin 1) ℚ :=
  1

/-- The identity action of the free cyclic group. -/
def rhoZero : Multiplicative ℤ →* GeneratorMatrix where
  toFun := fun _ => 1
  map_one' := rfl
  map_mul' := by simp

/-- The Jordan generator together with its explicit inverse. -/
def rhoUnipotentUnit : GeneratorMatrixˣ where
  val := rhoUnipotentGenerator
  inv := !![1, -1; 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [rhoUnipotentGenerator, Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [rhoUnipotentGenerator, Matrix.mul_apply, Fin.sum_univ_two]

/-- The free cyclic action determined by the unipotent Jordan generator. -/
def rhoUnipotent : Multiplicative ℤ →* GeneratorMatrix :=
  (Units.coeHom GeneratorMatrix).comp
    (zpowersHom (GeneratorMatrixˣ) rhoUnipotentUnit)

private theorem rho_zero_at_generator :
    rhoZero cycleGenerator = rhoZeroGenerator := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem rho_zero_generator_eq_one :
    rhoZeroGenerator = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem rho_unipotent_at_generator :
    rhoUnipotent cycleGenerator = rhoUnipotentGenerator := by
  simp [rhoUnipotent, cycleGenerator, rhoUnipotentUnit]

private theorem rho_unipotent_charpoly_aux :
    rhoUnipotentGenerator.charpoly = (X - 1) ^ 2 := by
  rw [Matrix.charpoly_fin_two]
  norm_num [rhoUnipotentGenerator, Matrix.trace, Matrix.det_fin_two,
    Polynomial.C_ofNat]
  ring

private theorem linear_factor_natDegree :
    (X - 1 : ℚ[X]).natDegree = 1 := by
  simpa using Polynomial.natDegree_X_sub_C (1 : ℚ)

private theorem square_factor_natDegree :
    ((X - 1 : ℚ[X]) ^ 2).natDegree = 2 := by
  calc
    ((X - 1 : ℚ[X]) ^ 2).natDegree = 2 * (X - 1 : ℚ[X]).natDegree := by
      exact (monic_X_sub_C (1 : ℚ)).natDegree_pow 2
    _ = 2 := by rw [linear_factor_natDegree]

private theorem minpoly_eq_of_isConj {left right : GeneratorMatrix}
    (conjugate : IsConj left right) :
    minpoly ℚ left = minpoly ℚ right := by
  obtain ⟨unit, semiconjugate⟩ := conjugate
  let conjugation : GeneratorMatrix ≃ₐ[ℚ] GeneratorMatrix :=
    MulSemiringAction.toAlgEquiv ℚ GeneratorMatrix
      (ConjAct.toConjAct unit)
  have conjugationApply : conjugation left = right := by
    change (ConjAct.toConjAct unit : ConjAct GeneratorMatrixˣ) • left = right
    rw [ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct]
    calc
      (unit : GeneratorMatrix) * left * ↑unit⁻¹ =
          (right * unit) * ↑unit⁻¹ :=
        congrArg (· * ↑unit⁻¹) semiconjugate.eq
      _ = right := by rw [Matrix.mul_assoc, unit.mul_inv, mul_one]
  rw [← conjugationApply, minpoly.algEquiv_eq]

/-- The identity generator has minimal polynomial `X - 1`. -/
theorem rho_zero_minpoly :
    minpoly ℚ (rhoZero cycleGenerator) = X - 1 := by
  rw [rho_zero_at_generator]
  rw [rho_zero_generator_eq_one]
  exact minpoly.one ℚ GeneratorMatrix
#print axioms rho_zero_minpoly

/-- The unipotent Jordan generator has minimal polynomial `(X - 1)^2`. -/
theorem rho_unipotent_minpoly :
    minpoly ℚ (rhoUnipotent cycleGenerator) = (X - 1) ^ 2 := by
  rw [rho_unipotent_at_generator]
  have integral : IsIntegral ℚ rhoUnipotentGenerator := Matrix.isIntegral _
  have notScalar :
      rhoUnipotentGenerator ∉
        (algebraMap ℚ GeneratorMatrix).range := by
    rintro ⟨scalar, hScalar⟩
    have entry := congrArg (fun matrix : GeneratorMatrix => matrix 0 1) hScalar
    norm_num [rhoUnipotentGenerator, Matrix.algebraMap_matrix_apply] at entry
  have lower : 2 ≤ (minpoly ℚ rhoUnipotentGenerator).natDegree :=
    (minpoly.two_le_natDegree_iff integral).2 notScalar
  have targetMonic : ((X - 1 : ℚ[X]) ^ 2).Monic :=
    (monic_X_sub_C 1).pow 2
  have divides : minpoly ℚ rhoUnipotentGenerator ∣ (X - 1) ^ 2 := by
    simpa only [rho_unipotent_charpoly_aux] using
      Matrix.minpoly_dvd_charpoly rhoUnipotentGenerator
  have upper : (minpoly ℚ rhoUnipotentGenerator).natDegree ≤ 2 := by
    calc
      (minpoly ℚ rhoUnipotentGenerator).natDegree ≤
          ((X - 1 : ℚ[X]) ^ 2).natDegree :=
        Polynomial.natDegree_le_of_dvd divides targetMonic.ne_zero
      _ = 2 := square_factor_natDegree
  have degree : (minpoly ℚ rhoUnipotentGenerator).natDegree = 2 :=
    Nat.le_antisymm upper lower
  symm
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le
  · exact minpoly.monic integral
  · exact targetMonic
  · exact divides
  · rw [square_factor_natDegree, degree]
#print axioms rho_unipotent_minpoly

/-- The two cyclic representations are not isomorphic: their generators are not conjugate. -/
theorem representations_not_isomorphic :
    ¬ IsConj (rhoZero cycleGenerator) (rhoUnipotent cycleGenerator) := by
  intro conjugate
  have equalMinpoly := minpoly_eq_of_isConj conjugate
  rw [rho_zero_minpoly, rho_unipotent_minpoly] at equalMinpoly
  have degreeEquality := congrArg Polynomial.natDegree equalMinpoly
  rw [linear_factor_natDegree, square_factor_natDegree] at degreeEquality
  omega
#print axioms representations_not_isomorphic

/-- Both generators have characteristic polynomial `(X - 1)^2`.

Pinned Mathlib has no semisimplification interface. Over `ℚ`, this split polynomial records
two copies of the sole eigenvalue `1`, which is the semisimple data `1 ⊕ 1` in this example. -/
theorem same_semisimplification_charpoly :
    (rhoZero cycleGenerator).charpoly = (X - 1) ^ 2 ∧
      (rhoUnipotent cycleGenerator).charpoly = (X - 1) ^ 2 := by
  rw [rho_zero_at_generator, rho_unipotent_at_generator]
  constructor
  · rw [rho_zero_generator_eq_one]
    simpa using
      (Matrix.charpoly_one (n := Fin 2) (R := ℚ))
  · exact rho_unipotent_charpoly_aux
#print axioms same_semisimplification_charpoly

/-- Conjugacy is necessary in the private invariance lemma: without it, minpolys can differ. -/
theorem conjugacy_hypothesis_is_necessary :
    ¬ IsConj (rhoZero cycleGenerator) (rhoUnipotent cycleGenerator) ∧
      minpoly ℚ (rhoZero cycleGenerator) ≠ minpoly ℚ (rhoUnipotent cycleGenerator) := by
  constructor
  · exact representations_not_isomorphic
  · intro equalMinpoly
    have degreeEquality := congrArg Polynomial.natDegree equalMinpoly
    rw [rho_zero_minpoly, rho_unipotent_minpoly, linear_factor_natDegree,
      square_factor_natDegree] at degreeEquality
    omega
#print axioms conjugacy_hypothesis_is_necessary

/-- Positive generator powers have nilpotent entry `n`; at `n = 0` the action is identity. -/
theorem generator_power_degenerate_audit :
    (∀ n : ℕ,
        rhoUnipotent (cycleGenerator ^ n) =
          !![1, (n : ℚ); 0, 1]) ∧
      rhoUnipotent (cycleGenerator ^ 0) = rhoZero cycleGenerator := by
  have powerFormula : ∀ n : ℕ, rhoUnipotentGenerator ^ n = !![1, (n : ℚ); 0, 1] := by
    intro n
    induction n with
    | zero =>
        ext i j
        fin_cases i <;> fin_cases j <;> rfl
    | succ n inductionHypothesis =>
        rw [pow_succ, inductionHypothesis]
        ext i j
        fin_cases i <;> fin_cases j
        all_goals
          norm_num [rhoUnipotentGenerator, Matrix.mul_apply, Fin.sum_univ_two]
        all_goals ring
  constructor
  · intro n
    rw [map_pow, rho_unipotent_at_generator]
    exact powerFormula n
  · simp [rhoZero]
#print axioms generator_power_degenerate_audit

/-- The identity action is self-conjugate and constant; zero cannot be a group action. -/
theorem trivial_action_degenerate_audit :
    IsConj (rhoZero cycleGenerator) (rhoZero cycleGenerator) ∧
      (∀ z : Multiplicative ℤ, rhoZero z = 1) ∧
        ¬ IsUnit (0 : GeneratorMatrix) := by
  constructor
  · exact ⟨1, by simp⟩
  · constructor
    · intro z
      rfl
    · have detZero : Matrix.det (0 : GeneratorMatrix) = 0 :=
        Matrix.det_zero (by infer_instance)
      rw [Matrix.isUnit_iff_isUnit_det, detZero]
      exact not_isUnit_zero
#print axioms trivial_action_degenerate_audit

/-- Empty matrices collapse zero and identity; the one-dimensional analogues also coincide. -/
theorem low_dimension_degenerate_audit :
    (0 : Matrix Empty Empty ℚ) = 1 ∧
      rhoZeroGeneratorOne = rhoUnipotentGeneratorOne := by
  constructor
  · ext i
    exact i.elim
  · rfl
#print axioms low_dimension_degenerate_audit

end D5.S3.ConceptDynamics.Representation.IdentityJordanGeneratorContrast
