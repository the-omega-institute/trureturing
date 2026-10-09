# FourVectorSignSumBound

## Abstract

FourVectorSignSumBound: exact analytic statements for four-qubit white-noise compatibility.

**Definition 1.1 (signedSum).**

$$\forall E \in Type,\; [\operatorname{NormedAddCommGroup}\left(E\right)], [\operatorname{InnerProductSpace}\left(\mathbb{R}, E\right)], \forall x \in \operatorname{Fin}\left(4\right) \to E,\; \forall e \in \operatorname{Fin}\left(4\right) \to Bool,\; \operatorname{signedSum}\left(x, e\right) = \sum_{(i: \operatorname{Fin}\left(4\right))} (\operatorname{sgn}\left(e\left(i\right)\right)) \cdot (x\left(i\right))$$

*Formalization.* `D5/S3/Geometry/FourVectorSignSumBound.signedSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A sign tuple assigns a coefficient +1 or −1 to each of the four vectors.

**Definition 1.2 (maxNorm).**

$$\forall E \in Type,\; [\operatorname{NormedAddCommGroup}\left(E\right)], [\operatorname{InnerProductSpace}\left(\mathbb{R}, E\right)], \forall x \in \operatorname{Fin}\left(4\right) \to E,\; \operatorname{maxNorm}\left(x\right) = \operatorname{Finset.sup}'\left(\operatorname{Finset.univ}, fun (e: \operatorname{Fin}\left(4\right) \to Bool) \mapsto \left\lVert \operatorname{signedSum}\left(x, e\right) \right\rVert\right)$$

*Formalization.* `D5/S3/Geometry/FourVectorSignSumBound.maxNorm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The maximum ranges over all sixteen sign tuples.

**Theorem 1.3 (signedSum_le_max).**

$$\forall E \in Type,\; [\operatorname{NormedAddCommGroup}\left(E\right)], [\operatorname{InnerProductSpace}\left(\mathbb{R}, E\right)], \forall x \in \operatorname{Fin}\left(4\right) \to E,\; \forall e \in \operatorname{Fin}\left(4\right) \to Bool,\; \left\lVert \operatorname{signedSum}\left(x, e\right) \right\rVert \le \operatorname{maxNorm}\left(x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FourVectorSignSumBound.signedSum_le_max` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each signed sum is bounded by the finite maximum.

**Theorem 1.4 (four_vector_inequality).**

$$\forall x \in \operatorname{Fin}\left(4\right) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right),\; \sum_{(i: \operatorname{Fin}\left(4\right))} \left\lVert x\left(i\right) \right\rVert \le \frac{\sqrt{13}}{2} \cdot \operatorname{maxNorm}\left(x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FourVectorSignSumBound.four_vector_inequality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Singular Gram positivity and a triangle decomposition of the four-sign constraints yield the universal bound. Zero columns are handled separately. The coefficient is attained by three planar trine vectors of length three and a perpendicular vector of length four.

## References

- Truth anchor: `D5/S3/Geometry/FourVectorSignSumBound.four_vector_inequality`
- Truth anchor: `D5/S3/Geometry/FourVectorSignSumBound.maxNorm`
- Truth anchor: `D5/S3/Geometry/FourVectorSignSumBound.signedSum`
- Truth anchor: `D5/S3/Geometry/FourVectorSignSumBound.signedSum_le_max`
- Dependency: [D5/S3/Combinatorics/IsingUniquenessSets](../Combinatorics/IsingUniquenessSets.md)
