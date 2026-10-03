# Seven Ground Sections and Finite Label Capacity

## Abstract

Seven nonzero ground sections span every six-bit finite label, with one relation.

Let E be the three-dimensional vector space over F_2 and let f satisfy the finite sign-table equations. The label space is E times its coordinate dual, and the ground section sends g to (g, f(g,-)).

**Theorem 1.1 (Six independent sections and the seven-point relation).**

Lean statement: `D5/S3/VertexAlgebra/MonsterFusionSpan.fusion_span_and_capacity`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/MonsterFusionSpan.fusion_span_and_capacity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tathagata Basak (2017). *The octonions as a twisted group algebra*. URL: <https://arxiv.org/abs/1702.05705>.

*Commentary.*

For every sign table, six of the seven nonzero ground sections give a bijection from six binary coefficients to all labels. The sum of all seven sections is zero, and a relation among them forces all seven coefficients to agree. Thus this is the unique nonzero relation. There are 64 finite labels, with eight character values over each coarse defect. A three-bit encoding exists and no injective two-bit encoding of one fiber exists. The proof constructs the three missing character directions from the determinant carries, then uses the cubic-table classification to establish the seven-point relation. Basak's twisted-group-algebra calculation is historical context. The result does not establish a VOA realization or an actual fusion rule; the physical closure claim in the theory source remains conditional on that rule.

## References

- Truth anchor: `D5/S3/VertexAlgebra/MonsterFusionSpan.fusion_span_and_capacity`
- Dependency: [D5/S3/VertexAlgebra/MonsterCharacterCarry](MonsterCharacterCarry.md)
