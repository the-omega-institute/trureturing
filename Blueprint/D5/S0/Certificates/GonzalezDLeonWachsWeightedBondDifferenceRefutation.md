# Weighted Bond Difference Counterexample

## Abstract

Three disjoint triangles and three spanning paths refute Conjecture 4.13(2).

**Definition 1.1 (The literal all-graphs conjecture).**

$$claim = ConjecturePartTwo\left(\right)$$

*Formalization.* `D5/S0/Certificates/GonzalezDLeonWachsWeightedBondDifferenceRefutation.claim` (`✓ std3`).

*Citation.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

For every finite graph G and spanning subgraph H with the same number of connected components, the sign-corrected difference of their literal source Mobius polynomials is asserted to split over the reals. This is part (2) as written; no connected-only premise is added.

**Theorem 1.2 (The nine-vertex witness refutes part (2)).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/GonzalezDLeonWachsWeightedBondDifferenceRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/gonzalez-dleon-wachs-conjecture-4-13-2-refutation` (refuted) by `D5/S0/Certificates/GonzalezDLeonWachsWeightedBondDifferenceRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"gonzalez-dleon-wachs-conjecture-4-13-2-refutation","declaration_gid":"D5/S0/Certificates/GonzalezDLeonWachsWeightedBondDifferenceRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Rafael S. Gonzalez D'Leon; Michelle L. Wachs (2026). *Weighted bond posets and a new chromatic symmetric function*. DOI: [10.48550/arXiv.2608.08692](https://doi.org/10.48550/arXiv.2608.08692). URL: <https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13>.

*Commentary.*

On Fin 3 x Fin 3, G is three triangle fibers and H is three path fibers. Both have three components and H is proper. Restriction and gluing give the source-poset product, hence polynomials A^3 and B^3. Their difference is (X+1)^2 times a quartic with no real root, so it does not split.

## References

- Truth anchor: `D5/S0/Certificates/GonzalezDLeonWachsWeightedBondDifferenceRefutation.claim`
- Truth anchor: `D5/S0/Certificates/GonzalezDLeonWachsWeightedBondDifferenceRefutation.result`
- Dependency: [D5/S0/Certificates/GonzalezDLeonWachsThreeVertexMobius](GonzalezDLeonWachsThreeVertexMobius.md)
