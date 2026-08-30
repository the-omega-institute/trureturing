/- GID: D5/S3/ConceptDynamics/Representation/IdentityJordanFullGroupTrace
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Representation/IdentityJordanFullGroupTrace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Integer Jordan powers and equal traces include zero and negative audits. -/

import D5.S3.ConceptDynamics.Representation.IdentityJordanGeneratorContrast
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/- Library-search audit trail (2026-08-30):
   * Repository searches by object name, conventional name, digest, nearby module, general
     shape, and alternate character vocabulary found no full integer-power or trace theorem.
   * Loogle for integer powers found `zpowersHom_apply`, `map_zpow`, and
     `Units.val_zpow_eq_zpow_val`; its matrix-trace query found `Matrix.trace_fin_two_of`.
   * LeanSearch for a two-by-two unipotent integer power found the exact upstream result
     `ModularGroup.coe_T_zpow`; a trace query also found `Matrix.trace_fin_two_of`.
   * The proof maps `coe_T_zpow` from integer to rational matrices and reuses the existing
     rational cyclic representations. No new power induction or competing representation is made.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Representation.IdentityJordanFullGroupTrace

open Matrix
open D5.S3.ConceptDynamics.Representation.IdentityJordanGeneratorContrast

/-- Every integer power of the rational Jordan generator has the stated closed form. -/
theorem rho_unipotent_integer_power (m : ℤ) :
    rhoUnipotent (Multiplicative.ofAdd m) = !![1, (m : ℚ); 0, 1] := by
  have generatorUnit :
      rhoUnipotentUnit = Matrix.SpecialLinearGroup.mapGL ℚ ModularGroup.T := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [rhoUnipotentUnit, rhoUnipotentGenerator,
        Matrix.SpecialLinearGroup.mapGL_coe_matrix, ModularGroup.T, Matrix.map_apply]
  change ((rhoUnipotentUnit ^ m : GeneratorMatrixˣ) : GeneratorMatrix) = _
  rw [generatorUnit, ← map_zpow]
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix,
    Matrix.SpecialLinearGroup.map_apply_coe, ModularGroup.coe_T_zpow]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num
#print axioms rho_unipotent_integer_power

/-- Both cyclic representations have trace two at every integer group element. -/
theorem full_group_trace_two (m : ℤ) :
    (rhoUnipotent (Multiplicative.ofAdd m)).trace = 2 ∧
      (rhoZero (Multiplicative.ofAdd m)).trace = 2 := by
  constructor
  · rw [rho_unipotent_integer_power, Matrix.trace_fin_two_of]
    norm_num
  · norm_num [rhoZero, Matrix.trace_fin_two_of]
#print axioms full_group_trace_two

/-- At exponent zero both actions are the identity matrix. -/
theorem zero_exponent_audit :
    rhoUnipotent (Multiplicative.ofAdd 0) = 1 ∧
      rhoUnipotent (Multiplicative.ofAdd 0) = rhoZero (Multiplicative.ofAdd 0) := by
  constructor
  · rw [rho_unipotent_integer_power]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  · rw [rho_unipotent_integer_power]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
#print axioms zero_exponent_audit

/-- Exponent negative one gives the explicit inverse and still has trace two. -/
theorem negative_exponent_audit :
    rhoUnipotent (Multiplicative.ofAdd (-1)) = !![1, (-1 : ℚ); 0, 1] ∧
      (rhoUnipotent (Multiplicative.ofAdd (-1))).trace = 2 := by
  constructor
  · exact rho_unipotent_integer_power (-1)
  · exact (full_group_trace_two (-1)).1
#print axioms negative_exponent_audit

/-- Equal traces on the whole group do not make these two representations isomorphic. -/
theorem same_full_trace_but_not_isomorphic :
    (∀ m : ℤ,
        (rhoUnipotent (Multiplicative.ofAdd m)).trace =
          (rhoZero (Multiplicative.ofAdd m)).trace) ∧
      ¬ IsConj (rhoZero cycleGenerator) (rhoUnipotent cycleGenerator) := by
  constructor
  · intro m
    exact (full_group_trace_two m).1.trans (full_group_trace_two m).2.symm
  · exact representations_not_isomorphic
#print axioms same_full_trace_but_not_isomorphic

end D5.S3.ConceptDynamics.Representation.IdentityJordanFullGroupTrace
