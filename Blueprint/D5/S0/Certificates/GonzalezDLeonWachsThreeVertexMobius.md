# Three-Vertex Weighted Bond Mobius Computation

## Abstract

The literal three-vertex weighted bond posets have explicit Mobius polynomials.

**Theorem 1.1 (The triangle source polynomial).**

$$sourceMobiusPolynomial\left(triangleThree\right) = 2 + 5 \cdot X + 2 \cdot X^{2}$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/GonzalezDLeonWachsThreeVertexMobius.triangle_three_source_mobius_polynomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

The proof classifies every connected weighted partition of K3, identifies the actual order intervals, and evaluates the incidence-algebra recurrence.

**Theorem 1.2 (The path source polynomial).**

$$sourceMobiusPolynomial\left(pathThree\right) = 1 + 3 \cdot X + 1 \cdot X^{2}$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/GonzalezDLeonWachsThreeVertexMobius.path_three_source_mobius_polynomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

The same source-faithful classification for P3 retains exactly its two graph edges and evaluates the actual maximal weighted-partition sum.

## References

- Truth anchor: `D5/S0/Certificates/GonzalezDLeonWachsThreeVertexMobius.path_three_source_mobius_polynomial`
- Truth anchor: `D5/S0/Certificates/GonzalezDLeonWachsThreeVertexMobius.triangle_three_source_mobius_polynomial`
- Dependency: [D5/S0/Certificates/GonzalezDLeonWachsWeightedBondSource](GonzalezDLeonWachsWeightedBondSource.md)
