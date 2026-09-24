# Degeneracy Graph Monomial Basis

## Abstract

Actual source monomials form a basis in every commutative complex algebra with complete orthogonal leaf projectors.

The basis owner contains the complete public inventory: sourceNodeProjector sums the actual descendant leaf projectors, sourceGenerator uses the literal node labels, and sourceMonomial is the literal generator-product monomial. The final theorem constructs P : Basis (Bottom T) Complex A to B : Basis (Columns T) Complex A, proves B m = sourceMonomial T P m, gives the forward RawM expansion (2.29), and gives the inverse projector expansion (2.30) with coefficient (SourceSquare T)^-1 ((bottomColumnEquiv T).symm m) b. The algebra is arbitrary [CommRing A] [Algebra Complex A]; no semisimplicity or evaluation-isomorphism assumption is introduced.

This is the exact source resolution of the monomial-basis clause (3.6), joined to the determinant bridge through the accepted factorization theorem.

**Definition 1.1 (sourceNodeProjector).**

Lean statement: `D5/S3/Quantum/Algebra/DegeneracyGraphMonomialBasis.sourceNodeProjector`

*Formalization.* `D5/S3/Quantum/Algebra/DegeneracyGraphMonomialBasis.sourceNodeProjector` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Garreth Kemp and Sanjaye Ramgoolam (2026). *Gauge-string duality, monomial bases and graph determinants*. URL: <https://arxiv.org/html/2603.05259v2>.

*Commentary.*

This public declaration is the actual arbitrary-algebra source bridge. It is projected from Lean without replacing the source monomial, projector, or coefficient orientation by a postulated evaluation equivalence.

**Definition 1.2 (sourceGenerator).**

Lean statement: `D5/S3/Quantum/Algebra/DegeneracyGraphMonomialBasis.sourceGenerator`

*Formalization.* `D5/S3/Quantum/Algebra/DegeneracyGraphMonomialBasis.sourceGenerator` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Garreth Kemp and Sanjaye Ramgoolam (2026). *Gauge-string duality, monomial bases and graph determinants*. URL: <https://arxiv.org/html/2603.05259v2>.

*Commentary.*

This public declaration is the actual arbitrary-algebra source bridge. It is projected from Lean without replacing the source monomial, projector, or coefficient orientation by a postulated evaluation equivalence.

**Definition 1.3 (sourceMonomial).**

Lean statement: `D5/S3/Quantum/Algebra/DegeneracyGraphMonomialBasis.sourceMonomial`

*Formalization.* `D5/S3/Quantum/Algebra/DegeneracyGraphMonomialBasis.sourceMonomial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Garreth Kemp and Sanjaye Ramgoolam (2026). *Gauge-string duality, monomial bases and graph determinants*. URL: <https://arxiv.org/html/2603.05259v2>.

*Commentary.*

This public declaration is the actual arbitrary-algebra source bridge. It is projected from Lean without replacing the source monomial, projector, or coefficient orientation by a postulated evaluation equivalence.

**Theorem 1.4 (source_monomial_basis_and_expansions).**

Lean statement: `D5/S3/Quantum/Algebra/DegeneracyGraphMonomialBasis.source_monomial_basis_and_expansions`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/DegeneracyGraphMonomialBasis.source_monomial_basis_and_expansions` (`✓ std3`). ∎

*Resolves.* `Problems/kemp-ramgoolam-degeneracy-graph-determinant-and-monomial-basis` (proved) by `D5/S3/Quantum/Algebra/DegeneracyGraphMonomialBasis.source_monomial_basis_and_expansions`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kemp-ramgoolam-degeneracy-graph-determinant-and-monomial-basis","declaration_gid":"D5/S3/Quantum/Algebra/DegeneracyGraphMonomialBasis.source_monomial_basis_and_expansions","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Garreth Kemp and Sanjaye Ramgoolam (2026). *Gauge-string duality, monomial bases and graph determinants*. URL: <https://arxiv.org/html/2603.05259v2>.

*Commentary.*

This public declaration is the actual arbitrary-algebra source bridge. It is projected from Lean without replacing the source monomial, projector, or coefficient orientation by a postulated evaluation equivalence.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/DegeneracyGraphMonomialBasis.sourceGenerator`
- Truth anchor: `D5/S3/Quantum/Algebra/DegeneracyGraphMonomialBasis.sourceMonomial`
- Truth anchor: `D5/S3/Quantum/Algebra/DegeneracyGraphMonomialBasis.sourceNodeProjector`
- Truth anchor: `D5/S3/Quantum/Algebra/DegeneracyGraphMonomialBasis.source_monomial_basis_and_expansions`
- Dependency: [D5/S3/Quantum/Algebra/DegeneracyGraphDeterminantFactorization](DegeneracyGraphDeterminantFactorization.md)
