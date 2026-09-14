/- GID: D5/S0/Certificates/Polynomials/QProductNecessityRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/Polynomials/QProductNecessityRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.Coeff, mathlib/module/Mathlib.Algebra.BigOperators.Fin]
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/Polynomials/QProductNecessityRefutation.claim; result=D5/S0/Certificates/Polynomials/QProductNecessityRefutation.result; claim=D5/S0/Certificates/Polynomials/QProductNecessityRefutation.claim
   digest: The necessity clause of arXiv:2605.12822v1 Conjecture 5.4 is false at r=3, k=6, all a_i=2, b=2. -/

import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.Polynomials.QProductNecessityRefutation

open Polynomial
open scoped BigOperators

/-!
Connelly--Ito--Martinez--Shevchenko--Yang, Conjecture 5.4, section 5.2:
"Moreover, if k <= 3 or r <= 3, this condition is also necessary."
Corollary 4.3 says "r divides a_i for some"; the conjecture explicitly
generalizes that corollary. Thus its "for any" divisibility branch is existential.
The following computational remark only covers k <= 5. The paper's separate
example has k = r = 4, so it does not contradict this necessity clause.

The claim retains every parameter and positivity restriction. Natural division
is the floor on this domain. Unimodality uses weak inequalities, permitting a
plateau and retaining internal zero coefficients. Polynomial coefficients after
the degree are zero; for these nonnegative polynomials, adjoining that zero tail
is equivalent to the usual finite coefficient-sequence definition.
-/

/-- The finite geometric polynomial [a]_q. -/
noncomputable def qInteger (a : ℕ) : ℕ[X] :=
  ∑ j ∈ Finset.range a, X ^ j

/-- The polynomial [b]_(q^r), with every exponent multiplied by r. -/
noncomputable def qStride (r b : ℕ) : ℕ[X] :=
  ∑ j ∈ Finset.range b, X ^ (r * j)

/-- The entire product in Conjecture 5.4; Fin k indexes all k factors. -/
noncomputable def qProduct {k : ℕ} (r : ℕ) (a : Fin k → ℕ) (b : ℕ) : ℕ[X] :=
  (∏ i, qInteger (a i)) * qStride r b

/-- Coefficients weakly rise to some peak and weakly fall thereafter. -/
def Unimodal (p : ℕ[X]) : Prop :=
  ∃ m : ℕ, (∀ i, i < m → p.coeff i ≤ p.coeff (i + 1)) ∧
    ∀ i, m ≤ i → p.coeff (i + 1) ≤ p.coeff i

/-- The disjunction whose necessity the paper conjectures. -/
def necessaryCondition {k : ℕ} (r : ℕ) (a : Fin k → ℕ) (b : ℕ) : Prop :=
  (∃ i, r ∣ a i) ∨ b ≤ 1 + ∑ i, a i / r

/-- Precisely the universal necessity clause, including the disjunctive smallness premise. -/
def claim : Prop :=
  ∀ (r k : ℕ) (a : Fin k → ℕ) (b : ℕ),
    2 ≤ r → 1 ≤ k → (∀ i, 1 ≤ a i) → 1 ≤ b → (k ≤ 3 ∨ r ≤ 3) →
    Unimodal (qProduct r a b) → necessaryCondition r a b

private theorem family_eq (k : ℕ) :
    qProduct 3 (fun _ : Fin k => 2) 2 = (1 + X) ^ k * (1 + X ^ 3) := by
  simp [qProduct, qInteger, qStride, Finset.sum_range_succ]

private theorem family_coeff (k n : ℕ) :
    (qProduct 3 (fun _ : Fin k => 2) 2).coeff n =
      k.choose n + if 3 ≤ n then k.choose (n - 3) else 0 := by
  rw [family_eq, mul_add, mul_one, coeff_add, coeff_mul_X_pow']
  simp only [coeff_one_add_X_pow, Nat.cast_id]

private theorem six_unimodal : Unimodal (qProduct 3 (fun _ : Fin 6 => 2) 2) := by
  refine ⟨3, ?_, ?_⟩
  · intro i hi
    interval_cases i <;> norm_num [family_coeff, Nat.choose]
  · intro i hi
    by_cases h : i ≤ 9
    · interval_cases i <;> norm_num [family_coeff, Nat.choose]
    · have h1 : 6 < i := by omega
      have h2 : 6 < i + 1 := by omega
      have h3 : 6 < i - 3 := by omega
      have h4 : 6 < i - 2 := by omega
      simp [family_coeff, Nat.choose_eq_zero_of_lt h1, Nat.choose_eq_zero_of_lt h2,
        Nat.choose_eq_zero_of_lt h3, Nat.choose_eq_zero_of_lt h4]

/-- The eligible unimodal product at (r,k,a,b) = (3,6,2,2) refutes the necessity clause. -/
theorem result : ¬ claim := by
  intro h
  have hc := h 3 6 (fun _ => 2) 2 (by decide) (by decide) (by decide)
    (by decide) (Or.inr (by decide)) six_unimodal
  norm_num [necessaryCondition] at hc

#print axioms claim
#print axioms result

end D5.S0.Certificates.Polynomials.QProductNecessityRefutation
