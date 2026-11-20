# O'Dorney's Padé junction determinant

## Abstract

The determinant in O'Dorney's Conjecture 4.7 vanishes at k=5, i=4, a=b=3.

**Definition 1.1 (The universal determinant implication).**

$$\forall (a,b:\mathbb{Z}) (k,i:\mathbb{N}), a\neq 0 \longrightarrow b\neq 0 \longrightarrow 0<\operatorname{discriminant}(a,b) \longrightarrow 1\leq i \longrightarrow i<k \longrightarrow \operatorname{upsilon}(a,b,k,i)=0 \longrightarrow k=4 \land i=3 \land a^{2}=b$$

*Formalization.* `D5/S1/Depth/ContinuedFractions/ODorneyPadeJunctionRefutation.claim` (`✓ std3`).

*Citation.* Evan M. O'Dorney (2026). *Two-point Padé approximation and patterns in continued fractions for (F_{n+1}/F_n)^k*. DOI: [10.48550/arXiv.2611.01029](https://doi.org/10.48550/arXiv.2611.01029). URL: <https://arxiv.org/pdf/2611.01029v1#page=16>.

*Commentary.*

On p. 16, O'Dorney writes, “The only solution to Υₖ,ᵢ(α) = 0 with a, b nonzero integers and D = a² + 4b > 0 occurs at k = 4, i = 3, a² = b, corresponding to the unique invisible junction in a⁴(Fₙ₊₁/Fₙ)⁴.”

The discriminant is a²+4b with a and b cast from the integers to the reals. Set alpha=(a+sqrt(discriminant))/2 and h(X)=X²-aX-b. For 1≤i<k, beta at the integer index j is the coefficient of X^(2i-j) in h(X)^(i-1)(X-alpha)² when 0≤j≤2i, and zero otherwise. The entry in row r and column c of the (k-i) by (k-i) matrix is beta at the signed index i+c-r. The determinant is upsilon(a,b,k,i).

**Theorem 1.2 (The determinant vanishes outside the proposed exception).**

$$\neg (\forall (a,b:\mathbb{Z}) (k,i:\mathbb{N}), a\neq 0 \longrightarrow b\neq 0 \longrightarrow 0<\operatorname{discriminant}(a,b) \longrightarrow 1\leq i \longrightarrow i<k \longrightarrow \operatorname{upsilon}(a,b,k,i)=0 \longrightarrow k=4 \land i=3 \land a^{2}=b)$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/ContinuedFractions/ODorneyPadeJunctionRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/odorney-pade-conjecture-4-7` (refuted) by `D5/S1/Depth/ContinuedFractions/ODorneyPadeJunctionRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"odorney-pade-conjecture-4-7","declaration_gid":"D5/S1/Depth/ContinuedFractions/ODorneyPadeJunctionRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Evan M. O'Dorney (2026). *Two-point Padé approximation and patterns in continued fractions for (F_{n+1}/F_n)^k*. DOI: [10.48550/arXiv.2611.01029](https://doi.org/10.48550/arXiv.2611.01029). URL: <https://arxiv.org/pdf/2611.01029v1#page=16>.

*Commentary.*

Take a=b=3, k=5 and i=4. The discriminant is 21 and the sole matrix entry is beta at index 4. By the one-by-one determinant identity, upsilon is the coefficient of X⁴ in (X²-3X-3)³(X-alpha)².

The coefficients of X⁴, X³ and X² in (X²-3X-3)³ are 18, 27 and -54. Multiplication by (X-alpha)² therefore gives -54-54 alpha+18 alpha². Since alpha=(3+sqrt(21))/2 and sqrt(21)²=21, alpha²-3 alpha-3=0. Substitution gives zero for the coefficient of X⁴. The conclusion would force k=4, whereas this determinant has k=5.

Lean certifies the determinant refutation. For this witness, the six Toeplitz determinants Δ₅,ᵢ from Lemma 2.1 are 1, 171, 1296, 1701, −189, and 1 in index order. Since a > 0, D = 21 is nonsquare, 3 divides 9, and all six determinants are nonzero, Exercise 4.1(b) gives an eventual patch-junction decomposition of the fifth powers of consecutive ratios in the recurrence with a = b = 3, u₀ = 0 and u₁ = 1. Exercise 4.6 gives an empty fourth junction and equal adjacent patches after renormalization for all sufficiently large n. The words, period values and general classification remain open here.

## References

- Truth anchor: `D5/S1/Depth/ContinuedFractions/ODorneyPadeJunctionRefutation.claim`
- Truth anchor: `D5/S1/Depth/ContinuedFractions/ODorneyPadeJunctionRefutation.result`
