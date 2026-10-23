# Qubit Incompatibility Radial Reduction

## Abstract

Relative cosines reduce incompatible volume to ordered-root coordinates.

**Definition 1.1 (Ordered-root density).**

$$\forall p : (\mathbb{R} \times \mathbb{R}), \forall q : (\mathbb{R} \times \mathbb{R}), \operatorname{rootDensity}\left(p, q\right) = \operatorname{ite}\left(0 < 1 - (p).1 - (q).1, \frac{(((p).1 - (p).2) \cdot ((q).1 - (q).2)) \cdot (\operatorname{Real.sqrt}\left((1 - (p).1 - (q).1) \cdot (1 - (p).2 - (q).2)\right))}{(\operatorname{OrderedRootCoordinates.xCoord}\left((p).1, (p).2\right)) \cdot (\operatorname{OrderedRootCoordinates.xCoord}\left((q).1, (q).2\right))}, 0\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/QubitIncompatibilityRadialReduction.rootDensity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The density vanishes unless 1-u-U is positive. Its remaining factors are the two root differences and the two square roots.

**Definition 1.2 (Ordered-root integral).**

$$rootI = \int^{-}_{p: (\mathbb{R} \times \mathbb{R}) \in \operatorname{OrderedRootCoordinates.rootDomain}} (\int^{-}_{q: (\mathbb{R} \times \mathbb{R}) \in \operatorname{OrderedRootCoordinates.rootDomain}} (\operatorname{ENNReal.ofReal}\left(\operatorname{rootDensity}\left(p, q\right)\right)) d\operatorname{MeasureTheory.volume}) d\operatorname{MeasureTheory.volume}$$

*Formalization.* `D5/S3/Quantum/Measurement/QubitIncompatibilityRadialReduction.rootI` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Integrate the nonnegative part of rootDensity over two copies of rootDomain.

**Theorem 1.3 (Exact incompatible volume).**

$$\operatorname{MeasureTheory.volume}\left(\operatorname{OrderedRootCoordinates.NJM}\right) = (\operatorname{ENNReal.ofReal}\left((4) \cdot ((\operatorname{Real.pi})^{2})\right)) \cdot (rootI)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/QubitIncompatibilityRadialReduction.volume_NJM_rootI` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Relative-cosine integration and the ordered-root Jacobian cancel the radial factors. The incompatible volume is 4π² times rootI.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/QubitIncompatibilityRadialReduction.rootDensity`
- Truth anchor: `D5/S3/Quantum/Measurement/QubitIncompatibilityRadialReduction.rootI`
- Truth anchor: `D5/S3/Quantum/Measurement/QubitIncompatibilityRadialReduction.volume_NJM_rootI`
- Dependency: [D5/S3/Quantum/Measurement/OrderedRootCoordinates](OrderedRootCoordinates.md)
