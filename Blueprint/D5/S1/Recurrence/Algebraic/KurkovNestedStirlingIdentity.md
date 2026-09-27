# Kurkov's Nested Stirling Identity

## Abstract

Kurkov's full nested rational sum equals the unsigned Stirling number.

The target is Mikhail Kurkov's May 24, 2026 conjecture in OEIS A132393. All parameters are natural numbers, with n at least zero and m at least one. All displayed summand arithmetic is rational except natural indices, factorials, falling factorials and the sign exponent. The falling factorial is descending. No determinant evaluation or other mathematical conclusion is assumed in the theorem.

**Definition 1.1 (The literal nested summation domain).**

Lean statement: `D5/S1/Recurrence/Algebraic/KurkovNestedStirlingIdentity.Chain`

*Formalization.* `D5/S1/Recurrence/Algebraic/KurkovNestedStirlingIdentity.Chain` (`✓ std3`).

*Citation.* Mikhail Kurkov (2026). *OEIS A132393: Kurkov's nested sum for unsigned Stirling numbers*. URL: <https://oeis.org/A132393>.

*Commentary.*

A chain is an antitone function from Fin m to Fin (n+1). Thus its coordinates satisfy n >= j_1 >= ... >= j_m >= 0. The finite sum counts every such chain once, exactly as the nested sums.

**Definition 1.2 (The source summand).**

Lean statement: `D5/S1/Recurrence/Algebraic/KurkovNestedStirlingIdentity.sourceTerm`

*Formalization.* `D5/S1/Recurrence/Algebraic/KurkovNestedStirlingIdentity.sourceTerm` (`✓ std3`).

*Citation.* Mikhail Kurkov (2026). *OEIS A132393: Kurkov's nested sum for unsigned Stirling numbers*. URL: <https://oeis.org/A132393>.

*Commentary.*

The formal position i represents t=i+1. The numerator is the descending factorial of n+i of length j_t. Rational Vandermonde differences are j_q-j_p+p-q. The denominator factors are (n-j_t+t)^(m+1) and (j_t+m-t)!, each positive on the chain domain. Consequently the natural subtractions in the indices agree with ordinary integer subtraction.

**Definition 1.3 (The full rational expression).**

Lean statement: `D5/S1/Recurrence/Algebraic/KurkovNestedStirlingIdentity.sourceRHS`

*Formalization.* `D5/S1/Recurrence/Algebraic/KurkovNestedStirlingIdentity.sourceRHS` (`✓ std3`).

*Citation.* Mikhail Kurkov (2026). *OEIS A132393: Kurkov's nested sum for unsigned Stirling numbers*. URL: <https://oeis.org/A132393>.

*Commentary.*

The finite chain sum is multiplied by (n+m)! and the product of (n+i)^i for positions i from one through m. No finite cutoff or fixed-m specialization enters this definition.

**Theorem 1.4 (The full unbounded Kurkov identity).**

Lean statement: `D5/S1/Recurrence/Algebraic/KurkovNestedStirlingIdentity.result`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/KurkovNestedStirlingIdentity.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a132393-kurkov-nested-stirling-identity` (proved) by `D5/S1/Recurrence/Algebraic/KurkovNestedStirlingIdentity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a132393-kurkov-nested-stirling-identity","declaration_gid":"D5/S1/Recurrence/Algebraic/KurkovNestedStirlingIdentity.result","resolution_kind":"proved"} -->

*Citation.* Mikhail Kurkov (2026). *OEIS A132393: Kurkov's nested sum for unsigned Stirling numbers*. URL: <https://oeis.org/A132393>.

*Commentary.*

Put N=n+m and l_t=n-j_t+t. This gives a proved bijection with m-element subsets of 1,...,N. Factorial and sign normalization, the attributed rectangular Cauchy-Binet proof and Mathlib's Vandermonde determinant turn the literal sum into a signed moment determinant. Moment indices are integers. Frozen Stirling inclusion-exclusion supplies the zero and negative moments; Pascal's identity gives the moment recurrence. Row reversal cancels the global sign. A unit triangular column operation and a boundary cofactor give the determinant recurrence. The node-count rank bound supplies its vanishing boundary. Multiplying by N! yields exactly the unsigned Stirling recurrence and initial values. All classical identities remain proof-local; the only public theorem is this source assertion.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/KurkovNestedStirlingIdentity.Chain`
- Truth anchor: `D5/S1/Recurrence/Algebraic/KurkovNestedStirlingIdentity.result`
- Truth anchor: `D5/S1/Recurrence/Algebraic/KurkovNestedStirlingIdentity.sourceRHS`
- Truth anchor: `D5/S1/Recurrence/Algebraic/KurkovNestedStirlingIdentity.sourceTerm`
- Dependency: [D5/S1/Recurrence/Parity/StirlingPowerFactorialPrimePeriod](../Parity/StirlingPowerFactorialPrimePeriod.md)
