# All-map obstruction for a triple tensor

## Abstract

An all-map trace obstruction for three polynomial contragredient translation modules along a finite additive embedding.

Let K be any field and write V_d for the ordinary dual of the polynomials of degree less than d, with contragredient translation action. For natural n,m,k put N=n+m+k and T=((V_(n+1) tensor V_(m+1)) tensor V_(k+1)), with this actual left parenthesization. When E is a finite additive group and alpha:E->K is injective and additive, all actions are restricted along alpha. K and E have independent universes; K is not required to be finite.

**Theorem 1.1 (Expand the actual triple action).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTripleTensorObstruction.triple_action_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTripleTensorObstruction.triple_action_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The diagonal action at translation parameter -a is the sum, for r from 0 to N, of a^r times tripleCoefficient(r). This coefficient is obtained by grouping the actual binary tensor coefficient and the third-factor coefficient by their total degree. The identity holds before restricting to any finite subgroup.

**Theorem 1.2 (The highest coefficient has one-dimensional range).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTripleTensorObstruction.triple_coefficient_top_range`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTripleTensorObstruction.triple_coefficient_top_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The highest coefficient sends every vector into the line spanned by the actual tensor of the three highest dual-basis vectors. This rank-one range is a statement about the action coefficient, not a claim that every intertwiner factors through the multiplication dual.

**Theorem 1.3 (Normalize the binary multiplication dual).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTripleTensorObstruction.delta_top`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTripleTensorObstruction.delta_top` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The map delta:V_(n+m+1)->V_(n+1) tensor V_(m+1) is defined by dualizing actual polynomial multiplication and using the dual-tensor equivalence. It sends the highest dual-basis vector exactly to the tensor of the highest dual-basis vectors. No scalar normalization or factorial inverse is introduced.

**Theorem 1.4 (Normalize the iterated multiplication dual).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTripleTensorObstruction.embedded_triple_delta_top`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTripleTensorObstruction.embedded_triple_delta_top` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

First apply delta for degrees n+m and k, then tensor delta for degrees n and m with the third identity. After restriction along any additive alpha, the resulting map from V_(N+1) to T sends the highest dual-basis vector to the same specified highest triple tensor. This normalization does not need finiteness or injectivity of alpha.

**Theorem 1.5 (Recover coefficient intertwining from finite samples).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTripleTensorObstruction.restricted_triple_intertwines_coefficients`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTripleTensorObstruction.restricted_triple_intertwines_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If N+1<=card E, every equivariant f:V_(N+1)->T intertwines each action coefficient. The proof compares the polynomial action expansions at the distinct samples alpha(e). It does not assume that E fills K or that K itself is finite.

**Theorem 1.6 (The canonical triple map has zero trace pairing).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTripleTensorObstruction.embedded_canonical_trace_zero`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTripleTensorObstruction.embedded_canonical_trace_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume N+2<=card E and choose(n+m,n) times choose(N,n+m)=0 in K. Every equivariant return map g:T->V_(N+1) has trace zero after composition with the iterated multiplication dual. If the first binomial vanishes, equivariant partial trace tensors its binary zero-pairing obstruction with the third factor. If the second vanishes, the second binary obstruction applies directly.

**Theorem 1.7 (Every equivariant forward and return pairing vanishes).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTripleTensorObstruction.embedded_composition_trace_zero`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTripleTensorObstruction.embedded_composition_trace_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same size and vanishing-product assumptions, trace(g composed with f)=0 for every equivariant f:V_(N+1)->T and g:T->V_(N+1). Coefficient recovery places the image of the highest vector under f on the canonical highest line. Subtracting the corresponding scalar multiple of the canonical map kills that vector. The existing constant-diagonal endomorphism theorem then makes its composite with g trace zero, giving the result for arbitrary f.

For example, over F27 with n=m=k=3, the first coefficient choose(6,3)=20 is nonzero in characteristic three, while choose(9,6)=84 is zero. A transient exact application checks the resulting obstruction for the actual triple V4 tensor V4 tensor V4. Thus a valid first binary step does not prevent a new obstruction when the third factor is added.

This is a three-factor extension of the corrected binary Elmer--Kadr analysis, whose external anchor is Conjecture 3.7 of Some formulae relating modular representations of elementary abelian p-groups, DOI 10.1007/s13366-026-00855-9. The paper's displayed conjecture is binary; no externally posed triple conjecture or worldwide novelty is claimed. The partial-trace tensor-ideal mechanism is classical. These trace statements supply an obstruction only: they do not identify the trace radical with the original relative-factorization ideal.

## References

- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTripleTensorObstruction.delta_top`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTripleTensorObstruction.embedded_canonical_trace_zero`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTripleTensorObstruction.embedded_composition_trace_zero`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTripleTensorObstruction.embedded_triple_delta_top`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTripleTensorObstruction.restricted_triple_intertwines_coefficients`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTripleTensorObstruction.triple_action_expansion`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTripleTensorObstruction.triple_coefficient_top_range`
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/BoundedTensorPolarization](BoundedTensorPolarization.md)
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/EmbeddedOriginalClassification](EmbeddedOriginalClassification.md)
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/EquivariantPartialTrace](EquivariantPartialTrace.md)
