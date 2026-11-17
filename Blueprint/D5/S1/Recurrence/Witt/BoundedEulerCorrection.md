# Bounded corrections for arbitrary integer ghost weights

## Abstract

Bounded corrections for arbitrary integer ghost weights

For an arbitrary integer sequence w, the Euler exponent at n is the Euclidean quotient of w(n) minus the proper-divisor ghost, and the correction is its residue modulo n. Only n>0 is constrained. The value at zero is unused by the actual exponential. The proof constructs the integer account by strong recursion, then reuses the existing Euler and Gauss machinery to establish actual integrality and positive-index uniqueness.

**Definition 1.1 (ledger).**

Lean statement: `D5/S1/Recurrence/Witt/BoundedEulerCorrection.ledger`

*Formalization.* `D5/S1/Recurrence/Witt/BoundedEulerCorrection.ledger` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Strong recursion uses only proper divisors. Division here is integer Euclidean division; the denominator at zero has no mathematical role.

**Definition 1.2 (properGhost).**

Lean statement: `D5/S1/Recurrence/Witt/BoundedEulerCorrection.properGhost`

*Formalization.* `D5/S1/Recurrence/Witt/BoundedEulerCorrection.properGhost` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite sum uses the actual proper divisors of n and their integer Euler exponents.

**Definition 1.3 (correction).**

Lean statement: `D5/S1/Recurrence/Witt/BoundedEulerCorrection.correction`

*Formalization.* `D5/S1/Recurrence/Witt/BoundedEulerCorrection.correction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The remainder selects the unique representative from zero through n-1 at every positive index.

**Definition 1.4 (IsCorrection).**

Lean statement: `D5/S1/Recurrence/Witt/BoundedEulerCorrection.IsCorrection`

*Formalization.* `D5/S1/Recurrence/Witt/BoundedEulerCorrection.IsCorrection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The predicate combines positive-index bounds with integrality of every coefficient of the literal rational formal exponential.

**Theorem 1.5 (correction equation).**

Lean statement: `D5/S1/Recurrence/Witt/BoundedEulerCorrection.correction_equation`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Witt/BoundedEulerCorrection.correction_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Euclidean quotient and remainder give the exact divisor-sum ghost equation. This is a derived identity for the constructed account.

**Theorem 1.6 (correction integral).**

Lean statement: `D5/S1/Recurrence/Witt/BoundedEulerCorrection.correction_integral`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Witt/BoundedEulerCorrection.correction_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constructed account satisfies the existing divisor-ghost Gauss congruences. The canonical integrality theorem identifies the actual exponential with an integer Euler series.

**Theorem 1.7 (correction unique).**

Lean statement: `D5/S1/Recurrence/Witt/BoundedEulerCorrection.correction_unique`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Witt/BoundedEulerCorrection.correction_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a competing bounded correction, the existing integral-input ledger theorem supplies integer exponents. Strong induction on proper divisors makes both the residue and quotient rigid. No equality at index zero is claimed.

**Definition 1.8 (moebiusTransform).**

Lean statement: `D5/S1/Recurrence/Witt/BoundedEulerCorrection.moebiusTransform`

*Formalization.* `D5/S1/Recurrence/Witt/BoundedEulerCorrection.moebiusTransform` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite integer sum is the uncorrected Mobius transform of the arbitrary weight.

**Theorem 1.9 (moebius identity).**

Lean statement: `D5/S1/Recurrence/Witt/BoundedEulerCorrection.moebius_identity`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Witt/BoundedEulerCorrection.moebius_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mobius inversion applies to the exact constructed ghost equation, producing the correction term with mu(n/d).

**Theorem 1.10 (logarithmic error).**

Lean statement: `D5/S1/Recurrence/Witt/BoundedEulerCorrection.logarithmic_error`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Witt/BoundedEulerCorrection.logarithmic_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The absolute Mobius value is at most one and each positive-index correction is less than its index. Complementary divisors convert the normalized divisor sum into reciprocal divisors, bounded by the harmonic sum and one plus the natural logarithm. No positivity assumption on the original weights is used.

## References

- Truth anchor: `D5/S1/Recurrence/Witt/BoundedEulerCorrection.IsCorrection`
- Truth anchor: `D5/S1/Recurrence/Witt/BoundedEulerCorrection.correction`
- Truth anchor: `D5/S1/Recurrence/Witt/BoundedEulerCorrection.correction_equation`
- Truth anchor: `D5/S1/Recurrence/Witt/BoundedEulerCorrection.correction_integral`
- Truth anchor: `D5/S1/Recurrence/Witt/BoundedEulerCorrection.correction_unique`
- Truth anchor: `D5/S1/Recurrence/Witt/BoundedEulerCorrection.ledger`
- Truth anchor: `D5/S1/Recurrence/Witt/BoundedEulerCorrection.logarithmic_error`
- Truth anchor: `D5/S1/Recurrence/Witt/BoundedEulerCorrection.moebiusTransform`
- Truth anchor: `D5/S1/Recurrence/Witt/BoundedEulerCorrection.moebius_identity`
- Truth anchor: `D5/S1/Recurrence/Witt/BoundedEulerCorrection.properGhost`
- Dependency: [D5/S1/Recurrence/Witt/HannaDiagonalGhostPowerIntegrality](HannaDiagonalGhostPowerIntegrality.md)
