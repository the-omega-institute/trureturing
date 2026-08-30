# Icosahedral Axis Normalizer Decomposition

## Abstract

The three finite projective axis classes form the complete 6/10/15 decomposition and have normalizer orders 10/6/4.

**Theorem 1.1 (The finite axis decomposition has the stated normalizers).**

$$\begin{aligned}\operatorname{union}(\operatorname{union}(P_{5}, P_{3}), P_{2}) = \operatorname{univ}\left(FiniteProjectivePlane\right) \land \operatorname{Disjoint}\left(P_{5}, P_{3}\right) \land \operatorname{Disjoint}\left(P_{5}, P_{2}\right) \land \operatorname{Disjoint}\left(P_{3}, P_{2}\right) \land\\\operatorname{card}(P_{5}) = 6 \land \operatorname{card}(P_{3}) = 10 \land \operatorname{card}(P_{2}) = 15 \land\\\operatorname{card}(P_{5}) = \operatorname{card}(A_{5}) \land \operatorname{card}(P_{3}) = \operatorname{card}(A_{3}) \land \operatorname{card}(P_{2}) = \operatorname{card}(A_{2}) \land\\\operatorname{card}(A_{5}) = 6 \land \operatorname{card}(A_{3}) = 10 \land \operatorname{card}(A_{2}) = 15 \land\\\forall g, h: A_{5}, \operatorname{axesAreConjugate}\left(5, g, h\right) \land\\\forall g, h: A_{3}, \operatorname{axesAreConjugate}\left(3, g, h\right) \land\\\forall g, h: A_{2}, \operatorname{axesAreConjugate}\left(2, g, h\right) \land\\\forall g: A_{5}, \operatorname{card}(\operatorname{cyclicAxisNormalizer}\left(5, g\right)) = 10 \land\\\forall g: A_{3}, \operatorname{card}(\operatorname{cyclicAxisNormalizer}\left(3, g\right)) = 6 \land\\\forall g: A_{2}, \operatorname{card}(\operatorname{cyclicAxisNormalizer}\left(2, g\right)) = 4 \land\\\forall g: A_{2}, \operatorname{cyclicAxisNormalizer}\left(2, g\right) = \operatorname{elementCentralizer}\left(g\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/IcosahedralAxisNormalizerDecomposition.finite_icosahedral_axis_decomposition_with_normalizers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The projective classes and cyclic-axis families are the canonical objects from the finite axis decomposition. The statement publishes their partition, cardinalities, cardinality bridges, normalizer orders, and the twofold normalizer-centralizer identification together.

## References

- Truth anchor: `D5/S3/Arith/IcosahedralAxisNormalizerDecomposition.finite_icosahedral_axis_decomposition_with_normalizers`
- Dependency: [D5/S3/Arith/IcosahedralAxisDecomposition](IcosahedralAxisDecomposition.md)
