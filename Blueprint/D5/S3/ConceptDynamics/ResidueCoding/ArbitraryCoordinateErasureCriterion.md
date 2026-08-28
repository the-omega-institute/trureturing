# Arbitrary Coordinate Erasure Criterion

## Abstract

Worst-case residue erasure capacity is the product of the smallest survivors.

**Theorem 1.1 (Every coordinate erasure pattern is faithful at prefix capacity).**

$$\begin{gathered}\forall m: \mathbb{N} \to \mathbb{N}, n, K: \mathbb{N},\\{}s: \operatorname{Fin}(n + 1),\\{}\forall i<n, 2 \le m(i) \land\\{}\forall i, j<n, i < j \Rightarrow m(i) < m(j) \land\\{}\forall i, j<n, i \neq j \Rightarrow \operatorname{Coprime}(m(i), m(j)) \Rightarrow\\{}{{\forall R: \operatorname{Finset}(\operatorname{Fin}(n)), \operatorname{card}(R) = n - s \Rightarrow \operatorname{Injective}(\operatorname{jointReadout}(\Lambda i: R, \Lambda x: \operatorname{Fin}(K), \operatorname{castZMod}(\operatorname{val}(x), m(\operatorname{val}(i)))))} \iff K \le \prod_{i: \operatorname{Fin}(n - s)} m(i)} \land\\{}\forall R: \operatorname{Finset}(\operatorname{Fin}(n)), \operatorname{card}(R) = n - s \Rightarrow \prod_{i: \operatorname{Fin}(n - s)} m(i) \le \prod_{i\in R} m(\operatorname{val}(i)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ResidueCoding/ArbitraryCoordinateErasureCriterion.arbitrary_coordinate_erasure_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The readout on each retained coordinate set is the canonical joint readout of the corresponding residue channels.

The retained-set recovery criterion reduces injectivity to product capacity. Sortedness then proves that the first surviving prefix has no larger product than any equally sized set.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ResidueCoding/ArbitraryCoordinateErasureCriterion.arbitrary_coordinate_erasure_criterion`
- Dependency: [D5/S3/Arith/Coding/ResidueCodeDynamicRange](../../Arith/Coding/ResidueCodeDynamicRange.md)
- Dependency: [D5/S3/ConceptDynamics/ResidueCoding/RetainedResidueRecoveryCriterion](RetainedResidueRecoveryCriterion.md)
