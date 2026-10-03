# Three-Torsion Directions of Collinear Triples

## Abstract

Nontrivial symmetries of collinear triples have two cyclic directions.

A Triple is an unordered three-point subset of the square grid modulo n, with distinct coordinates and zero difference determinant. In the first and third statements n=3m and m is positive.

**Theorem 1.1 (Four possible stabilizing vectors).**

$$\operatorname{translate}\left(t, S\right) = S, t \neq 0 \implies t \in \{(m, m), (m, 2m), (2m, m), (2m, 2m)\}$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/CollinearTripleThreeTorsion.stabilizer_direction_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Summing the three points shows 3t=0. Distinct coordinates exclude a zero coordinate of any nonzero stabilizer, leaving four vectors.

**Theorem 1.2 (Order-three cycles are collinear triples).**

$$3\operatorname{fst}\left(t\right) = 0, 3\operatorname{snd}\left(t\right) = 0, \operatorname{fst}\left(t\right) \neq 0, \operatorname{snd}\left(t\right) \neq 0 \implies \operatorname{IsCollinearTriple}\left(\{0, t, 2t\}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/CollinearTripleThreeTorsion.three_cycle_collinear` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both coordinates of t must be nonzero and annihilated by three. The three points 0, t, and 2t then have distinct coordinates; their difference determinants vanish.

**Theorem 1.3 (Both standard directions occur).**

$$\operatorname{IsCollinearTriple}\left(\{0, (m, m), 2(m, m)\}\right) \land \operatorname{IsCollinearTriple}\left(\{0, (m, 2m), 2(m, 2m)\}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/CollinearTripleThreeTorsion.two_canonical_cycles_collinear` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each positive m, the two order-three vectors (m,m) and (m,2m) produce admissible triples through the origin.

## References

- Truth anchor: `D5/S3/Factorization/CollinearTripleThreeTorsion.stabilizer_direction_four`
- Truth anchor: `D5/S3/Factorization/CollinearTripleThreeTorsion.three_cycle_collinear`
- Truth anchor: `D5/S3/Factorization/CollinearTripleThreeTorsion.two_canonical_cycles_collinear`
- Dependency: [D5/S3/Factorization/CollinearTripleTranslationOrbits](CollinearTripleTranslationOrbits.md)
- Dependency: [D5/S3/Factorization/FiniteTranslationStabilizer](FiniteTranslationStabilizer.md)
- Dependency: [D5/S3/Factorization/ThreeTorsionZMod](ThreeTorsionZMod.md)
