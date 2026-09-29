# Collinear Triple Fixed-Point Census

## Abstract

Fixed-point census and the exact three-torsion residue for collinear triples.

A Triple is an unordered three-point set in the square grid modulo n, with distinct first and second coordinates and zero difference determinant. Translation is the additive group action on these sets.

**Theorem 1.1 (Exact count for an eligible translation).**

$$0 < n, 3\operatorname{fst}\left(t\right) = 0, 3\operatorname{snd}\left(t\right) = 0, \operatorname{fst}\left(t\right) \neq 0, \operatorname{snd}\left(t\right) \neq 0 \implies \operatorname{card}\left(\operatorname{fixedBy}\left(\operatorname{Triple}\left(n\right), t\right)\right) = \frac{n^{2}}{3}$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/CollinearTripleFixedPointCensus.card_fixedBy_three_torsion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If three times each coordinate of t is zero and neither coordinate is zero, every triple fixed by t is a translate of {0,t,2t}. Conversely every such translate is fixed. The canonical cycle has a three-element translation stabilizer, so orbit-stabilizer gives exactly n squared divided by three fixed triples. The statement requires a positive modulus.

**Theorem 1.2 (Exact residue for multiples of three).**

$$0 < m \implies \exists q \in \mathbb{N}, \operatorname{card}\left(\operatorname{Triple}\left(3m\right)\right) = (3m)^{2}q + 2\frac{(3m)^{2}}{3}$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/CollinearTripleFixedPointCensus.exact_three_torsion_residue` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n=3m, exactly four nonzero translations can fix a triple, and each fixes n squared divided by three triples. Every other nonzero translation fixes none; the identity fixes all A(n) triples. Burnside gives A(n)+4n squared/3=n squared times the number of translation orbits. That orbit count is at least two, yielding the displayed natural-number formula with q equal to the orbit count minus two.

## References

- Truth anchor: `D5/S3/Factorization/CollinearTripleFixedPointCensus.card_fixedBy_three_torsion`
- Truth anchor: `D5/S3/Factorization/CollinearTripleFixedPointCensus.exact_three_torsion_residue`
- Dependency: [D5/S3/Factorization/CollinearTripleThreeTorsion](CollinearTripleThreeTorsion.md)
