# Collinear Triple Fixed Point Census

## Abstract

Nonidentity translations fix precisely the cosets of an admissible three-cycle.

For every positive modulus n, let G(n) be ZMod(n) times ZMod(n). Let T(n) consist of unordered finite subsets S of G(n) with exactly three elements, with both coordinate projections injective on S, and with the following determinant identity for every choice of points in S:

$\forall p,q,r \in S, (q_{1}-p_{1})(r_{2}-p_{2}) = (r_{1}-p_{1})(q_{2}-p_{2})$

Write F(n,t) for the members of T(n) fixed by translation by t. Addition to a set denotes its pointwise translate; its cardinality counts each unordered set once. The identity translation is excluded only from the zero-count and quartet assertions. No prime-modulus hypothesis is used.

The displayed floor of n squared divided by three denotes natural Euclidean division, with any remainder discarded.

**Theorem 1.1 (Three-cycle classification, exact fibers, and census).**

$$\begin{aligned}\forall n \in \mathbb{N}, 0 < n \implies\\{}[\forall t \in \operatorname{G}\left(n\right), 3t = 0 \implies t_{1} \neq 0 \implies t_{2} \neq 0 \implies\\\exists C \in \operatorname{T}\left(n\right), C = \{0,t,2t\} \land\\(\forall S \in \operatorname{T}\left(n\right), (t+S = S \iff \exists p \in \operatorname{G}\left(n\right), p+C = S)) \land\\(\forall p,q \in \operatorname{G}\left(n\right), (p+C = q+C \iff p-q \in C)) \land\\\operatorname{card}\left(\operatorname{F}\left(n, t\right)\right) = \left\lfloor\frac{n^{2}}{3}\right\rfloor] \land\\{}[\forall t \in \operatorname{G}\left(n\right), t \neq 0 \implies \neg(3t = 0 \land t_{1} \neq 0 \land t_{2} \neq 0) \implies \operatorname{card}\left(\operatorname{F}\left(n, t\right)\right) = 0] \land\\{}[\forall m \in \mathbb{N}, 0 < m \implies n = 3m \implies\\\forall t \in \operatorname{G}\left(n\right), t \neq 0 \implies \operatorname{card}\left(\operatorname{F}\left(n, t\right)\right) = \begin{cases}\left\lfloor\frac{n^{2}}{3}\right\rfloor&t \in \{(m,m),(m,2m),(2m,m),(2m,2m)\}\\0&\neg(t \in \{(m,m),(m,2m),(2m,m),(2m,2m)\})\end{cases}]\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/CollinearTripleFixedPointCensus.fixed_point_census` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If three times t is zero and both coordinates of t are nonzero, each coordinate has additive order three. The set C of its first three multiples consequently has three points and both coordinate maps are injective. Differences of multiples of the same vector have zero determinant, so C belongs to T(n). Translation by t cyclically permutes C.

If t fixes S, choose p in S. Invariance places all three points of p+C in S; equality follows from their common cardinality three. Conversely, every translate of C is fixed. A translation stabilizes C exactly when its vector belongs to C: necessity follows by translating zero, and sufficiency follows from the cyclic permutation. This gives the displayed exact fibers and a stabilizer of cardinality three. Orbit-stabilizer then gives n squared divided by three fixed triples.

For any nonzero fixing vector, summing the three points forces three times the vector to vanish. A zero first or second coordinate would contradict the corresponding injectivity, because a nonzero translation cannot fix an individual point. For n=3m, the standard representative of a coordinate annihilated by three is zero, m, or 2m. Keeping both coordinates nonzero gives exactly the four displayed pairs. Every other nonzero translation fixes no member of T(n).

## References

- Truth anchor: `D5/S3/Factorization/CollinearTripleFixedPointCensus.fixed_point_census`
- Dependency: [D5/S3/Factorization/CollinearTripleTranslationOrbits](CollinearTripleTranslationOrbits.md)
