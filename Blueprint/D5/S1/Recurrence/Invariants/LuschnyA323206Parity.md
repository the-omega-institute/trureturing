# Luschny's A323206 Parity Conjecture

## Abstract

Ballot coefficients and Catalan parity prove Luschny's A323206 conjecture.

All array indices are natural numbers, including zero. The coefficient ordinaryHypergeometricCoefficient uses ascending Pochhammer polynomials and the reciprocal factorial. Only the finite range j < k+1 occurs; no infinite hypergeometric value is used. Powers with exponent zero, including 0^0, equal one.

**Definition 1.1 (The terminating hypergeometric array).**

$$\forall n: \mathbb{N}, \forall k: \mathbb{N}, \operatorname{A}\left(n, k\right) = \sum_{j \in \operatorname{Finset}.\operatorname{range}\left(k + 1\right)} \operatorname{ordinaryHypergeometricCoefficient}\left(-(k: \mathbb{Q}), (k: \mathbb{Q}) + 1, -(k: \mathbb{Q}) - 1, j\right) \cdot (n: \mathbb{Q})^{j}$$

*Formalization.* `D5/S1/Recurrence/Invariants/LuschnyA323206Parity.A` (`✓ std3`).

*Citation.* Peter Luschny (2019). *OEIS A323206, terminating hypergeometric array and parity conjecture*. URL: <https://oeis.org/A323206>.

*Commentary.*

OEIS A323206 NAME (revision 52, no page number): "A(n, k) = hypergeometric([-k, k+1], [-k-1], n), square array read by ascending antidiagonals for n,k >= 0." The displayed finite sum expands this terminating hypergeometric notation over the rationals. The lower Pochhammer parameter is -k-1 and each index satisfies j <= k, so every denominator factor is nonzero.

**Definition 1.2 (The integral parity proposition).**

$$\operatorname{claim} = (\forall n: \mathbb{N}, \forall k: \mathbb{N}, \exists a: \mathbb{Z}, ((a: \mathbb{Q}) = \operatorname{A}\left(n, k\right)) \land (\operatorname{Odd}\left(a\right) \iff (\operatorname{Even}\left(n\right) \lor ((\operatorname{Odd}\left(n\right)) \land (\exists e: \mathbb{N}, (0 < e) \land (k + 2 = 2^{e}))))))$$

*Formalization.* `D5/S1/Recurrence/Invariants/LuschnyA323206Parity.claim` (`✓ std3`).

*Citation.* Peter Luschny (2019). *OEIS A323206, terminating hypergeometric array and parity conjecture*. URL: <https://oeis.org/A323206>.

*Commentary.*

OEIS A323206 COMMENTS (revision 52, no page number): "Conjecture: A(n, k) is odd if and only if n is even or (n is odd and k + 2 = 2^j for some j > 0)." The integer a expresses the integrality of A(n,k); the source's exponent j is named e here. Odd is applied to a in the integers, and Even and Odd applied to n are predicates on natural numbers.

**Theorem 1.3 (The parity classification).**

$$\forall n: \mathbb{N}, \forall k: \mathbb{N}, \exists a: \mathbb{Z}, ((a: \mathbb{Q}) = \operatorname{A}\left(n, k\right)) \land (\operatorname{Odd}\left(a\right) \iff (\operatorname{Even}\left(n\right) \lor ((\operatorname{Odd}\left(n\right)) \land (\exists e: \mathbb{N}, (0 < e) \land (k + 2 = 2^{e})))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/LuschnyA323206Parity.result` (`✓ std3`). ∎

*Resolves.* `Problems/luschny-a323206` (proved) by `D5/S1/Recurrence/Invariants/LuschnyA323206Parity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"luschny-a323206","declaration_gid":"D5/S1/Recurrence/Invariants/LuschnyA323206Parity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Peter Luschny (2019). *OEIS A323206, terminating hypergeometric array and parity conjecture*. URL: <https://oeis.org/A323206>.

*Commentary.*

The degree-j coefficient equals one at j=0 and otherwise equals choose(k+j,j)-choose(k+j,j-1), with subtraction in the integers. Thus the finite sum has an integer value. At an even argument its reduction modulo two is the constant coefficient one; at an odd argument it is the coefficient sum. The two hockey-stick sums give the Catalan number catalan(k+1). The binary support theorem for the shifted Catalan series then gives k+2=2^e, and k+2>=2 forces e>0.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/LuschnyA323206Parity.A`
- Truth anchor: `D5/S1/Recurrence/Invariants/LuschnyA323206Parity.claim`
- Truth anchor: `D5/S1/Recurrence/Invariants/LuschnyA323206Parity.result`
- Dependency: [D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity](CatalanCompositionSquareParity.md)
