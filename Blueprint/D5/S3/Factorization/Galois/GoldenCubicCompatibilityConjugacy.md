# Golden Cubic Compatibility Conjugacy

## Abstract

The actual compatibility automorphism has a two-element conjugacy class over the rationals.

**Theorem 1.1 (Two rational conjugates and the Galois-group order).**

Lean statement: `D5/S3/Factorization/Galois/GoldenCubicCompatibilityConjugacy.actual_conjugacy_data`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/GoldenCubicCompatibilityConjugacy.actual_conjugacy_data` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the actual radical and cyclotomic compositum, complex conjugation changes the selected automorphism on the real cube root of two. Automorphisms fixing the cubic cyclotomic base form an abelian subgroup of index two. Thus the rational conjugacy class consists of the selected automorphism and its distinct conjugate.

The class has size two. Linear disjointness of the actual radical and cyclotomic fields gives rational Galois-group order equal to the totient of the modulus times 3 to the power twice the earlier support size plus two.

## References

- Truth anchor: `D5/S3/Factorization/Galois/GoldenCubicCompatibilityConjugacy.actual_conjugacy_data`
- Dependency: [D5/S3/Factorization/Galois/GoldenCubicCompatibilityCompositum](GoldenCubicCompatibilityCompositum.md)
