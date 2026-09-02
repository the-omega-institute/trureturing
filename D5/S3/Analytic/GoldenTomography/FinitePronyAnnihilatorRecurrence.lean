/- GID: D5/S3/Analytic/GoldenTomography/FinitePronyAnnihilatorRecurrence
   generality: G
   mirror-B: D5/B/S3/Analytic/GoldenTomography/FinitePronyAnnihilatorRecurrence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The reciprocal denominator of a finite Prony generating function is a monic degree-m annihilator whose coefficients give an exact moment recurrence. -/

import D5.S3.Analytic.GoldenTomography.FinitePronyRationalGeneratingFunction
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic

/-!
# Finite Prony denominator and annihilator recurrence

For finitely many nodes `q_j`, the generating-function denominator is

`Q(z) = product j, (1 - q_j z)`.

Its reciprocal characteristic polynomial is

`P(X) = product j, (X - q_j)`.

The roots of `P` are the transport nodes themselves, and the coefficient
functional of `P` annihilates every shifted finite Prony moment window. This is
the exact noiseless algebra behind Prony elimination, linear prediction, Pade
identification, matrix-pencil methods, and finite Koopman realizations.

The module proves no numerical stability, noisy root recovery, confluent-mode
formula, or infinite Hankel-operator statement.
-/

/- Library-search audit trail (2026-09-03):
   * Current-tree searches for a Prony annihilator recurrence and for a finite
     exponential-moment recurrence found no declaration on `dev`.
   * The open source atom is
     `8cfd29a4812f2b98d385ec5e78138041665e6ff3060f1671a3fd4e4001269113`,
     formulas (1295.3)--(1295.4).
   * Pinned Mathlib supplies polynomial products, `eval_eq_sum`, monicity of
     `X - C a`, and finite-sum algebra. These owners are reused below.
   * A former broad draft contained the same algebra mixed with Hankel-rank and
     unknown-node claims. This owner isolates only the denominator-to-recurrence
     layer and reuses the existing `finitePronyMoment` source of truth. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.GoldenTomography.FinitePronyAnnihilatorRecurrence

open scoped BigOperators
open Polynomial
open D5.S3.Analytic.GoldenTomography.FinitePronyRationalGeneratingFunction

/-- Formula (1295.3): the denominator of the finite rational generating
function. -/
def finitePronyDenominator {m : ℕ} (nodes : Fin m → ℂ) : ℂ[X] :=
  ∏ j, (1 - C (nodes j) * X)

/-- The reciprocal characteristic polynomial. Its roots are the transport
nodes rather than their reciprocal pole locations. -/
def finitePronyAnnihilator {m : ℕ} (nodes : Fin m → ℂ) : ℂ[X] :=
  ∏ j, (X - C (nodes j))

/-- The shifted coefficient functional whose vanishing is the Prony linear
recurrence. -/
def finitePronyRecurrenceResidual {m : ℕ}
    (nodes weights : Fin m → ℂ) (time : ℕ) : ℂ :=
  ∑ degree in (finitePronyAnnihilator nodes).support,
    (finitePronyAnnihilator nodes).coeff degree *
      finitePronyMoment nodes weights (time + degree)

/-- The generating-function denominator has constant term one. -/
@[simp]
theorem finite_prony_denominator_eval_zero {m : ℕ}
    (nodes : Fin m → ℂ) :
    (finitePronyDenominator nodes).eval 0 = 1 := by
  classical
  simp [finitePronyDenominator]

/-- Every nonzero transport node gives a reciprocal zero of the generating
function denominator. -/
@[simp]
theorem finite_prony_denominator_eval_inverse_node {m : ℕ}
    (nodes : Fin m → ℂ) (mode : Fin m) (hNode : nodes mode ≠ 0) :
    (finitePronyDenominator nodes).eval (nodes mode)⁻¹ = 0 := by
  classical
  simp [finitePronyDenominator, hNode]

/-- Every transport node is a zero of the reciprocal annihilator. -/
@[simp]
theorem finite_prony_annihilator_eval_node {m : ℕ}
    (nodes : Fin m → ℂ) (mode : Fin m) :
    (finitePronyAnnihilator nodes).eval (nodes mode) = 0 := by
  classical
  simp [finitePronyAnnihilator]

/-- The reciprocal annihilator is monic. -/
theorem finite_prony_annihilator_monic {m : ℕ}
    (nodes : Fin m → ℂ) :
    (finitePronyAnnihilator nodes).Monic := by
  classical
  unfold finitePronyAnnihilator
  apply Polynomial.monic_prod_of_monic
  intro mode _
  exact Polynomial.monic_X_sub_C (nodes mode)

/-- The reciprocal annihilator has degree exactly equal to the indexed mode
count, including when one of the nodes is zero. -/
theorem finite_prony_annihilator_natDegree {m : ℕ}
    (nodes : Fin m → ℂ) :
    (finitePronyAnnihilator nodes).natDegree = m := by
  classical
  unfold finitePronyAnnihilator
  calc
    (∏ mode : Fin m, (X - C (nodes mode))).natDegree =
        ∑ mode : Fin m, (X - C (nodes mode)).natDegree := by
      apply Polynomial.natDegree_prod_of_monic
      intro mode _
      exact Polynomial.monic_X_sub_C (nodes mode)
    _ = m := by simp

/-- Formula (1295.4), in reciprocal-characteristic coefficient order: every
shifted finite Prony moment window is annihilated by the coefficients of the
monic degree-`m` polynomial whose roots are the nodes. -/
theorem finite_prony_moment_annihilator_recurrence {m : ℕ}
    (nodes weights : Fin m → ℂ) (time : ℕ) :
    finitePronyRecurrenceResidual nodes weights time = 0 := by
  classical
  unfold finitePronyRecurrenceResidual
  let p := finitePronyAnnihilator nodes
  change ∑ degree in p.support, p.coeff degree *
      (∑ mode, weights mode * nodes mode ^ (time + degree)) = 0
  calc
    (∑ degree in p.support, p.coeff degree *
        (∑ mode, weights mode * nodes mode ^ (time + degree))) =
        ∑ degree in p.support, ∑ mode,
          p.coeff degree *
            (weights mode * nodes mode ^ (time + degree)) := by
      apply Finset.sum_congr rfl
      intro degree hDegree
      rw [Finset.mul_sum]
    _ = ∑ mode, ∑ degree in p.support,
          p.coeff degree *
            (weights mode * nodes mode ^ (time + degree)) := by
      rw [Finset.sum_comm]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro mode hMode
      calc
        (∑ degree in p.support,
            p.coeff degree *
              (weights mode * nodes mode ^ (time + degree))) =
            weights mode * nodes mode ^ time *
              (∑ degree in p.support,
                p.coeff degree * nodes mode ^ degree) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro degree hDegree
          rw [pow_add]
          ring
        _ = weights mode * nodes mode ^ time * p.eval (nodes mode) := by
          rw [eval_eq_sum]
        _ = 0 := by
          rw [show p.eval (nodes mode) = 0 by
            simpa [p] using finite_prony_annihilator_eval_node nodes mode]
          ring

/-- The complete exact denominator-to-recurrence interface. -/
theorem finite_prony_denominator_recurrence_package {m : ℕ}
    (nodes weights : Fin m → ℂ) :
    (finitePronyDenominator nodes).eval 0 = 1 ∧
    (finitePronyAnnihilator nodes).Monic ∧
    (finitePronyAnnihilator nodes).natDegree = m ∧
    ∀ time : ℕ, finitePronyRecurrenceResidual nodes weights time = 0 :=
  ⟨finite_prony_denominator_eval_zero nodes,
    finite_prony_annihilator_monic nodes,
    finite_prony_annihilator_natDegree nodes,
    finite_prony_moment_annihilator_recurrence nodes weights⟩

-- A concrete one-mode family inhabits the interfaces and carries a genuine
-- first-order recurrence.
example (time : ℕ) :
    finitePronyRecurrenceResidual
        (fun _ : Fin 1 => (2 : ℂ))
        (fun _ : Fin 1 => (3 : ℂ))
        time = 0 :=
  finite_prony_moment_annihilator_recurrence
    (fun _ : Fin 1 => (2 : ℂ))
    (fun _ : Fin 1 => (3 : ℂ))
    time

#print axioms finite_prony_denominator_eval_zero
#print axioms finite_prony_denominator_eval_inverse_node
#print axioms finite_prony_annihilator_eval_node
#print axioms finite_prony_annihilator_monic
#print axioms finite_prony_annihilator_natDegree
#print axioms finite_prony_moment_annihilator_recurrence
#print axioms finite_prony_denominator_recurrence_package

end D5.S3.Analytic.GoldenTomography.FinitePronyAnnihilatorRecurrence
