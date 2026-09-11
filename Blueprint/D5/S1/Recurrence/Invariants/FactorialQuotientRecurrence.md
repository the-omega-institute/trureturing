# The Factorial-Quotient Recurrence of OEIS A372991

## Abstract

The factorial-quotient sequence satisfies Mathar's linear recurrence and is integral.

All indices are natural numbers and a takes values in the rationals. Factorials and natural witnesses k are cast to the rationals in equalities. The quotient defining a is rational division. In the coefficient 2n(2n-1), n is cast to the rationals before arithmetic; subtraction in the index n-3 is natural subtraction. The hypothesis n >= 3 makes this the displayed formula of Mathar's conjecture.

**Definition 1.1 (The factorial-quotient sequence).**

$$\begin{aligned}a: \mathbb{N} \to \mathbb{Q}\\a\left(0\right) = 1\\a\left(1\right) = 1\\\forall n \in \mathbb{N}, a\left(n + 2\right) = \frac{(2 \cdot (n + 2))!}{a\left(n + 1\right) \cdot a\left(n\right)}\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Invariants/FactorialQuotientRecurrence.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The rational definition follows the name of OEIS A372991 with initial values a(0)=a(1)=1. Integrality is proved below, rather than assumed when forming the quotient.

**Lemma 1.2 (Every term is positive).**

$$\forall n \in \mathbb{N}, 0 < a\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/FactorialQuotientRecurrence.a_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two-step induction combines positivity of the factorial with positivity of the two preceding terms. Thus every factor later cancelled is nonzero.

**Lemma 1.3 (The consecutive triple product).**

$$\forall n \in \mathbb{N}, a\left(n + 2\right) \cdot a\left(n + 1\right) \cdot a\left(n\right) = (2 \cdot (n + 2))!$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/FactorialQuotientRecurrence.triple_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiply the defining rational quotient by its nonzero denominator. The positivity theorem justifies this cancellation at every index.

**Theorem 1.4 (Mathar's conjectured linear recurrence).**

$$\forall n \in \mathbb{N}, 3 \le n \implies a\left(n\right) = 2 \cdot n \cdot (2 \cdot n - 1) \cdot a\left(n - 3\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/FactorialQuotientRecurrence.mathar_recurrence` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a372991-factorial-quotient-linear-recurrence` (proved) by `D5/S1/Recurrence/Invariants/FactorialQuotientRecurrence.mathar_recurrence`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a372991-factorial-quotient-linear-recurrence","declaration_gid":"D5/S1/Recurrence/Invariants/FactorialQuotientRecurrence.mathar_recurrence","resolution_kind":"proved"} -->

*Citation.* Clark Kimberling; R. J. Mathar (2024). *OEIS A372991, a(n) = (2n)!/(a(n-1)*a(n-2))*. URL: <https://oeis.org/A372991>.

*Commentary.*

Consecutive triple products share two positive factors. Cancelling those factors telescopes the quotient to (2n)!/(2n-2)!. Two applications of the factorial successor identity give the coefficient 2n(2n-1). This proves the conjecture for every n at least three.

**Theorem 1.5 (Every term is a natural number).**

$$\forall n \in \mathbb{N}, \exists k \in \mathbb{N}, a\left(n\right) = k$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/FactorialQuotientRecurrence.a_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strong induction uses the linear recurrence and the natural witness 2n(2n-1)k obtained from the witness k at n-3. The three base cases are discharged inside the induction proof. This is an unbounded integrality theorem, not a finite table of sequence values.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/FactorialQuotientRecurrence.a`
- Truth anchor: `D5/S1/Recurrence/Invariants/FactorialQuotientRecurrence.a_integral`
- Truth anchor: `D5/S1/Recurrence/Invariants/FactorialQuotientRecurrence.a_pos`
- Truth anchor: `D5/S1/Recurrence/Invariants/FactorialQuotientRecurrence.mathar_recurrence`
- Truth anchor: `D5/S1/Recurrence/Invariants/FactorialQuotientRecurrence.triple_product`
