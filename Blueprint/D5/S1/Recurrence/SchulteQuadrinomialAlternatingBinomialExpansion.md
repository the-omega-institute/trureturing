# Schulte's quadrinomial alternating-binomial expansion

## Abstract

Schulte's conjectured A008287 alternating-binomial expansion is proved.

The symbols ℕ and ℤ denote the naturals (including zero) and integers; ℤ[X] is the integer polynomial ring in X. The indices n, k, and j are natural numbers, and T(n,k) is an integer. The operator coeff(P,k) extracts the coefficient of X^k in P; binom(a,b) is the natural binomial coefficient, and intCast maps its natural value to ℤ. Powers of −2 and the entire sum are in ℤ. All index subtractions, including 3n−2j and k−j, are truncated natural subtraction; binom(n,j)=0 when j>n. The sum over Finset.range(k+1) has exactly the indices j=0,...,k. The scope is only Schulte's 2015 A008287 conjectured %F formula; the Shevelev 2010 and Bala 2013 formulas are different and are not asserted. The proof shape is bind-only under the open-problem-resolution basis: factorisation, the binomial theorem, and coefficient extraction normalize to this expansion.

**Definition 1.1 (The quadrinomial coefficient T(n,k)).**

$$\forall n \in \mathbb{N}, k \in \mathbb{N},\; \operatorname{T}\left(n, k\right) = \operatorname{coeff}\left((1 + X + X^{2} + X^{3})^{n}, k\right)$$

*Formalization.* `D5/S1/Recurrence/SchulteQuadrinomialAlternatingBinomialExpansion.T` (`✓ std3`).

*Citation.* Werner Schulte (2015). *OEIS A008287, quadrinomial coefficients, with the conjectured expansion T(n,k) = Sum_{j=0..k} (-2)^j binomial(n,j) binomial(3n-2j,k-j)*. URL: <https://oeis.org/A008287>.

*Commentary.*

For each pair of natural indices, T(n,k) extracts degree k from the n-th power of 1+X+X²+X³ in ℤ[X].

**Theorem 1.2 (Schulte's alternating-binomial identity).**

$$\forall n \in \mathbb{N}, k \in \mathbb{N},\; (k \le 3 \cdot n) \Rightarrow (\operatorname{T}\left(n, k\right) = \sum_{j = 0}^{k} (-2)^{j} \cdot \operatorname{intCast}\left(\operatorname{binom}\left(n, j\right)\right) \cdot \operatorname{intCast}\left(\operatorname{binom}\left(3 \cdot n - 2 \cdot j, k - j\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/SchulteQuadrinomialAlternatingBinomialExpansion.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a008287-schulte-quadrinomial-alternating-binomial` (proved) by `D5/S1/Recurrence/SchulteQuadrinomialAlternatingBinomialExpansion.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a008287-schulte-quadrinomial-alternating-binomial","declaration_gid":"D5/S1/Recurrence/SchulteQuadrinomialAlternatingBinomialExpansion.result","resolution_kind":"proved"} -->

*Citation.* Werner Schulte (2015). *OEIS A008287, quadrinomial coefficients, with the conjectured expansion T(n,k) = Sum_{j=0..k} (-2)^j binomial(n,j) binomial(3n-2j,k-j)*. URL: <https://oeis.org/A008287>.

*Commentary.*

For every n and k with k≤3n, T(n,k) equals the finite integer sum with natural binomial coefficients cast into ℤ. The factorisation 1+X+X²+X³=(1+X)³−2X(1+X), the binomial theorem, coefficient extraction, and range reindexing give the identity. The proof shape is bind-only; the named open problem is settled under issue #8204 without an escape witness.

## References

- Truth anchor: `D5/S1/Recurrence/SchulteQuadrinomialAlternatingBinomialExpansion.T`
- Truth anchor: `D5/S1/Recurrence/SchulteQuadrinomialAlternatingBinomialExpansion.result`
