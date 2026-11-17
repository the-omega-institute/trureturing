/- GID: D5/S3/ContinuousObservables/LaurentLoopFactorization
   generality: G
   mirror-B: D5/B/S3/ContinuousObservables/LaurentLoopFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=none
   digest: Exact ordered rank-one factorization of special-unitary Laurent loops. -/

import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

noncomputable section

open scoped BigOperators ComplexConjugate
open LaurentPolynomial

namespace D5.S3.ContinuousObservables.LaurentLoopFactorization

abbrev M₂ := Matrix (Fin 2) (Fin 2) ℂ
abbrev Loop := Matrix (Fin 2) (Fin 2) (LaurentPolynomial ℂ)

/-- The matrix at one Laurent exponent. -/
def coefficient (F : Loop) (j : ℤ) : M₂ := fun a b => (F a b).coeff j

/-- Entrywise scalar Laurent evaluation, defined only at nonzero complex arguments. -/
def evaluate (F : Loop) (z : ℂˣ) : M₂ :=
  (LaurentPolynomial.eval₂ (RingHom.id ℂ) z).mapMatrix F

/-- A finitely supported matrix coefficient family, in entrywise Laurent coordinates. -/
def ofCoefficients (C : ℤ →₀ M₂) : Loop := fun a b =>
  AddMonoidAlgebra.ofCoeff (C.mapRange (fun A => A a b) rfl)

/-- Constant matrices embedded in the Laurent matrix ring. -/
def constant (A : M₂) : Loop := LaurentPolynomial.C.mapMatrix A

/-- The primitive factor associated to an orthogonal projector. -/
def primitive (P : M₂) : Loop :=
  (LaurentPolynomial.T 1 : LaurentPolynomial ℂ) • constant P +
    (LaurentPolynomial.T (-1) : LaurentPolynomial ℂ) • constant (1 - P)

/-- Both projector laws and its exact complex rank. -/
def RankOneProjector (P : M₂) : Prop := Pᴴ = P ∧ P * P = P ∧ P.rank = 1

/-- The complete circle-valued special-unitary condition. -/
def CircleSU (F : Loop) : Prop := ∀ z : ℂˣ, ‖(z : ℂ)‖ = 1 →
  (evaluate F z)ᴴ * evaluate F z = 1 ∧ (evaluate F z).det = 1

/-- Symmetric support bound and exponent parity; actual degree is separate. -/
def InClass (n : ℕ) (F : Loop) : Prop :=
  (∀ j : ℤ, (n : ℤ) < |j| ∨ j % 2 ≠ (n : ℤ) % 2 → coefficient F j = 0) ∧ CircleSU F

def ActualDegree (n : ℕ) (F : Loop) : Prop :=
  coefficient F n ≠ 0 ∨ coefficient F (-(n : ℤ)) ≠ 0

/-- Matrix conjugate transpose together with inversion of the Laurent variable. -/
def adjoint (F : Loop) : Loop := fun a b =>
  LaurentPolynomial.invert (AddMonoidAlgebra.mapRingHom ℤ (starRingEnd ℂ) (F b a))

private theorem coefficient_ofCoefficients (C : ℤ →₀ M₂) (j : ℤ) :
    coefficient (ofCoefficients C) j = C j := rfl

private theorem coefficient_ext {F G : Loop} (h : ∀ j, coefficient F j = coefficient G j) :
    F = G := by
  ext a b j
  exact congrFun (congrFun (h j) a) b

private theorem evaluate_mul (F G : Loop) (z : ℂˣ) :
    evaluate (F * G) z = evaluate F z * evaluate G z :=
  map_mul _ _ _

private theorem evaluate_constant (A : M₂) (z : ℂˣ) : evaluate (constant A) z = A := by
  ext a b
  simp [evaluate, constant]

-- Temporary API probes; removed before a source handoff.
#synth Infinite Circle
#check Circle.coe_injective
#check Circle.norm_coe
#check Circle.toUnits
#check Set.infinite_range_of_injective
#check LaurentPolynomial.toLaurent_injective
#check Polynomial.toLaurent_injective
#check Matrix.rank_eq_iff
#check Matrix.rank_eq_zero
#check Matrix.rank_lt_iff_det_eq_zero
#check Matrix.rank_lt_card_iff_det_eq_zero
#check Matrix.trace_conjTranspose_mul_self_eq_zero_iff
#synth StarOrderedRing ℂ

end D5.S3.ContinuousObservables.LaurentLoopFactorization
