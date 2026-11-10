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

For any integer weight w and positive n, write c(n)=ledger(w,n), a(n)=correction(w,n), M_w(n)=sum_{d|n} mu(n/d)w(d), and E_w(n)=sum_{d|n} mu(n/d)a(d). The exact ghost equation above is w(m)-a(m)=sum_{d|m} d*c(d) for every positive m. Apply ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq to the function m*c(m), and reindex with Nat.sum_divisorsAntidiagonal'. Distributing the subtraction gives n*c(n)=M_w(n)-E_w(n). This is an application of Mobius inversion to the constructed account.

The residue bounds give 0<=a(d)<d for every divisor d of positive n. Using ArithmeticFunction.abs_moebius_le_one and Finset.abs_sum_le_sum_abs gives |E_w(n)|<=sum_{d|n} d. Complementary divisors, via Nat.sum_div_divisors, give (sum_{d|n} d)/n=sum_{d|n} 1/d. Each such divisor lies in {1,...,n}; all reciprocal terms are nonnegative. Thus this sum is at most the harmonic sum H_n, and harmonic_le_one_add_log bounds H_n by 1+log(n). Dividing the inversion identity by positive n proves |c(n)-M_w(n)/n|<=1+log(n). The absolute value and logarithm are over the reals, using the canonical casts of the integer sums. No sign restriction on w or condition on w(0) occurs, and no estimate at n=0 is asserted.

For integer s>=0, set w_s(d)=(d:Z)^(s.toNat). HannaUniformCorrection.weight_cast identifies its rational image with (d:Q)^s, including d=0. Then HannaUniformCorrection.a(s)=correction(w_s) and HannaUniformCorrection.c(s)=ledger(w_s). The finite Jordan sum is J_s(n)=sum_{d|n} mu(n/d)*d^s, namely M_{w_s}(n); for s>=1 this is the usual Jordan totient. Consequently n*c_s(n)=J_s(n)-sum_{d|n} mu(n/d)*a_s(d) and |c_s(n)-J_s(n)/n|<=1+log(n) for every n>0. These formulas also use the same finite-sum definition for s=0, and include s=1 and the square case s=2. Neither this substitution nor the error estimate asserts positive Euler exponents for s=0 or s=1. The separate positivity result requires s>=2. The free zeroth correction remains outside every sum and uniqueness claim.

## References

- Truth anchor: `D5/S1/Recurrence/Witt/BoundedEulerCorrection.IsCorrection`
- Truth anchor: `D5/S1/Recurrence/Witt/BoundedEulerCorrection.correction`
- Truth anchor: `D5/S1/Recurrence/Witt/BoundedEulerCorrection.correction_equation`
- Truth anchor: `D5/S1/Recurrence/Witt/BoundedEulerCorrection.correction_integral`
- Truth anchor: `D5/S1/Recurrence/Witt/BoundedEulerCorrection.correction_unique`
- Truth anchor: `D5/S1/Recurrence/Witt/BoundedEulerCorrection.ledger`
- Truth anchor: `D5/S1/Recurrence/Witt/BoundedEulerCorrection.moebiusTransform`
- Truth anchor: `D5/S1/Recurrence/Witt/BoundedEulerCorrection.properGhost`
- Dependency: [D5/S1/Recurrence/Witt/HannaDiagonalGhostPowerIntegrality](HannaDiagonalGhostPowerIntegrality.md)
