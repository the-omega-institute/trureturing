# Odd-index squares in the A113249 family

## Abstract

Every odd-index term in Dement's fourth-order integer family is a square.

The parameter m and index n are natural numbers, including zero. The values of a are integers, and every displayed cast (m : ℤ) is the natural parameter regarded as an integer. Index arithmetic is natural arithmetic; value arithmetic is integer arithmetic. IsSquare is Mathlib's predicate asserting the existence of an integer r with the value equal to r*r.

**Definition 1.1 (The fourth-order family).**

$$\begin{aligned}\operatorname{a}: \mathbb{N} \to \mathbb{N} \to \mathbb{Z}\\\forall m \in \mathbb{N},\; \operatorname{a}\left(m, 0\right) = -1\\\forall m \in \mathbb{N},\; \operatorname{a}\left(m, 1\right) = 4\\\forall m \in \mathbb{N},\; \operatorname{a}\left(m, 2\right) = -13 + 6 \cdot ((m: \mathbb{Z}) - 1) + 3 \cdot ((m: \mathbb{Z}) - 1)^{2}\\\forall m \in \mathbb{N},\; \operatorname{a}\left(m, 3\right) = (-8 + (m: \mathbb{Z})^{2})^{2}\\\forall m \in \mathbb{N},\; \forall n \in \mathbb{N},\; \operatorname{a}\left(m, n + 4\right) = (m: \mathbb{Z})^{4} \cdot \operatorname{a}\left(m, n\right) + (2 \cdot (m: \mathbb{Z}))^{2} \cdot \operatorname{a}\left(m, n + 1\right) - 4 \cdot \operatorname{a}\left(m, n + 3\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/OEISA113249OddIndexSquares.a` (`✓ std3`).

*Citation.* Creighton Dement (2005). *OEIS A113249: odd-index squares in a fourth-order recurrence family*. URL: <https://oeis.org/A113249>.

*Commentary.*

OEIS A113249, unpaginated Name (%N): "Corresponds to m = 3 in a family of 4th-order linear recurrence sequences given by a(m,n) = m^4*a(n-4) + (2*m)^2*a(n-3) - 4*a(n-1), a(m,0) = -1, a(m,1) = 4, a(m,2) = -13 + 6*(m-1) + 3*(m-1)^2, a(m,3) = (-8+m^2)^2." The family parameter is m : ℕ, the sequence index is n : ℕ, and the values lie in ℤ. The recurrence is displayed at n+4. In the initial value at index 2, m-1 is integer subtraction, also at m=0.

**Definition 1.2 (Dement's conjecture).**

$$\operatorname{claim} = (\forall m \in \mathbb{N},\; \forall n \in \mathbb{N},\; \operatorname{IsSquare}\left(\operatorname{a}\left(m, 2 \cdot n + 1\right)\right))$$

*Formalization.* `D5/S1/Recurrence/OEISA113249OddIndexSquares.claim` (`✓ std3`).

*Citation.* Creighton Dement (2005). *OEIS A113249: odd-index squares in a fourth-order recurrence family*. URL: <https://oeis.org/A113249>.

*Commentary.*

OEIS A113249, unpaginated Comments (%C): "Conjecture: a(m, 2*n+1) is a perfect square for all m, n." The variables m and n range over ℕ, including zero, and IsSquare is taken over ℤ. The source lists family parameters m=0 through m=10; the proposition quantifies over every natural m.

**Theorem 1.3 (All odd-index terms are squares).**

$$\forall m \in \mathbb{N},\; \forall n \in \mathbb{N},\; \operatorname{IsSquare}\left(\operatorname{a}\left(m, 2 \cdot n + 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/OEISA113249OddIndexSquares.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Creighton Dement (2005). *OEIS A113249: odd-index squares in a fourth-order recurrence family*. URL: <https://oeis.org/A113249>.

*Commentary.*

The auxiliary integer sequence starts at 2 and m²-8 and satisfies b(n+2)=-4b(n+1)-m²b(n). The subsequence a(m,2n+1) and the squares of these auxiliary terms satisfy the same order-three recurrence, with coefficients 16-m², m⁴-16m², and m⁶. They agree at n=0, 1, 2. Induction preserves this window of three identities, so each auxiliary term is an integer square root of the corresponding odd-index term. The argument includes every natural m without a nonzero or distinct-root hypothesis.

## References

- Truth anchor: `D5/S1/Recurrence/OEISA113249OddIndexSquares.a`
- Truth anchor: `D5/S1/Recurrence/OEISA113249OddIndexSquares.claim`
- Truth anchor: `D5/S1/Recurrence/OEISA113249OddIndexSquares.result`
