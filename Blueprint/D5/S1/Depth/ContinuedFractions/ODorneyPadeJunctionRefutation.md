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

*Source.* Repository-derived.

*Acknowledgement.* Evan M. O'Dorney (2026). *Two-point Padé approximation and patterns in continued fractions for (F_{n+1}/F_n)^k*. DOI: [10.48550/arXiv.2611.01029](https://doi.org/10.48550/arXiv.2611.01029). URL: <https://arxiv.org/pdf/2611.01029v1#page=16>.

*Commentary.*

Take a=b=3, k=5 and i=4. The discriminant is 21 and the sole matrix entry is beta at index 4. By the one-by-one determinant identity, upsilon is the coefficient of X⁴ in (X²-3X-3)³(X-alpha)².

The coefficients of X⁴, X³ and X² in (X²-3X-3)³ are 18, 27 and -54. Multiplication by (X-alpha)² therefore gives -54-54 alpha+18 alpha². Since alpha=(3+sqrt(21))/2 and sqrt(21)²=21, alpha²-3 alpha-3=0. Substitution gives zero for the coefficient of X⁴. The conclusion would force k=4, whereas this determinant has k=5.

This resolves the determinant implication. The existence and classification of invisible junctions in actual continued-fraction decompositions are separate questions.

## References

- Truth anchor: `D5/S1/Depth/ContinuedFractions/ODorneyPadeJunctionRefutation.claim`
- Truth anchor: `D5/S1/Depth/ContinuedFractions/ODorneyPadeJunctionRefutation.result`
