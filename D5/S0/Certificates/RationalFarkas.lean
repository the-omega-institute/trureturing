/- GID: D5/S0/Certificates/RationalFarkas
   generality: G
   mirror-B: D5/B/S0/Certificates/RationalFarkas
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact nonnegative rational dual weights certify infeasibility of finite linear inequality systems. -/

import Mathlib

/- Library-search audit trail (2026-09-01):
   * Pinned Mathlib supplies exact rational arithmetic, finite sums, and ordered
     ring inequalities, but repository searches found no finite rational Farkas
     refutation interface.
   * The certificate is intentionally proof carrying. External LP software only
     proposes rational weights; Lean checks nonnegativity, coefficient
     annihilation, and strict negativity of the combined right-hand side.
   * No floating-point optimizer result enters the theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.RationalFarkas

open scoped BigOperators

/-- Feasibility of a finite rational system `A x <= b`. -/
def LinearFeasible
    {Constraint Variable : Type*}
    [Fintype Constraint] [Fintype Variable]
    (A : Constraint -> Variable -> ℚ) (b : Constraint -> ℚ)
    (x : Variable -> ℚ) : Prop :=
  forall constraint,
    (∑ variable, A constraint variable * x variable) <= b constraint

/-- A Farkas refutation uses nonnegative row weights, annihilates every primal
variable coefficient, and gives a strictly negative weighted right-hand side. -/
structure Certificate
    {Constraint Variable : Type*}
    [Fintype Constraint] [Fintype Variable]
    (A : Constraint -> Variable -> ℚ) (b : Constraint -> ℚ) where
  weight : Constraint -> ℚ
  nonnegative : forall constraint, 0 <= weight constraint
  annihilates : forall variable,
    (∑ constraint, weight constraint * A constraint variable) = 0
  negativeRhs : (∑ constraint, weight constraint * b constraint) < 0

/-- Exact rational Farkas certificates rule out every feasible primal point. -/
theorem infeasible_of_certificate
    {Constraint Variable : Type*}
    [Fintype Constraint] [Fintype Variable]
    (A : Constraint -> Variable -> ℚ) (b : Constraint -> ℚ)
    (certificate : Certificate A b) :
    ¬Exists fun x : Variable -> ℚ => LinearFeasible A b x := by
  rintro ⟨x, feasible⟩
  have weighted (constraint : Constraint) :
      certificate.weight constraint *
          (∑ variable, A constraint variable * x variable) <=
        certificate.weight constraint * b constraint :=
    mul_le_mul_of_nonneg_left (feasible constraint)
      (certificate.nonnegative constraint)
  have summed :
      (∑ constraint,
          certificate.weight constraint *
            (∑ variable, A constraint variable * x variable)) <=
        ∑ constraint, certificate.weight constraint * b constraint :=
    Finset.sum_le_sum fun constraint _ => weighted constraint
  have leftZero :
      (∑ constraint,
          certificate.weight constraint *
            (∑ variable, A constraint variable * x variable)) = 0 := by
    calc
      (∑ constraint,
          certificate.weight constraint *
            (∑ variable, A constraint variable * x variable)) =
          ∑ constraint, ∑ variable,
            certificate.weight constraint *
              (A constraint variable * x variable) := by
        apply Finset.sum_congr rfl
        intro constraint _
        rw [Finset.mul_sum]
      _ = ∑ variable, ∑ constraint,
            certificate.weight constraint *
              (A constraint variable * x variable) := by
        rw [Finset.sum_comm]
      _ = ∑ variable,
            (∑ constraint,
              certificate.weight constraint * A constraint variable) *
                x variable := by
        apply Finset.sum_congr rfl
        intro variable _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro constraint _
        ring
      _ = 0 := by
        simp [certificate.annihilates]
  rw [leftZero] at summed
  exact (not_lt_of_ge summed) certificate.negativeRhs

/-- The certificate theorem in implication form, convenient for generated
finite LP witnesses. -/
theorem certificate_implies_no_solution
    {Constraint Variable : Type*}
    [Fintype Constraint] [Fintype Variable]
    {A : Constraint -> Variable -> ℚ} {b : Constraint -> ℚ}
    (certificate : Certificate A b) :
    forall x : Variable -> ℚ, ¬LinearFeasible A b x := by
  intro x feasible
  exact infeasible_of_certificate A b certificate ⟨x, feasible⟩

#print axioms infeasible_of_certificate
#print axioms certificate_implies_no_solution

end D5.S0.Certificates.RationalFarkas
