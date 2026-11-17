# Strict reverse ordering of exclusion-ball centres

## Abstract

The common effect that separates two pure points orders the centres of their complete exclusion balls in the reverse direction.

**Theorem 1.1 (Weak centre bounds and strict reverse ordering).**

$$\operatorname{SeparationData}(d) \Rightarrow\\\operatorname{CentreEffect}(d, cp) \le \frac{1}{2} \land \left(\frac{1}{2} \le \operatorname{CentreEffect}(d, cq) \land \operatorname{CentreEffect}(d, cp) < \operatorname{CentreEffect}(d, cq)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/OriginExclusionCenterReverse.strict_centre_reverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The structure SeparationData records two complete exclusion balls, their centres, two pure points, the two reflected points, one linear effect, and the endpoint and uniqueness conditions used by the source argument.

The reflection identities are r = 2 c_p - q and s = 2 c_q - p. Applying the global effect bounds to these points gives f(c_p) at most one half and one half at most f(c_q).

If equality held between the centre values, both would be one half and the first reflected point would attain value one. Its membership in the second complete ball and the unique-maximizer hypothesis would identify it with the pure point excluded from the first ball, contradicting its recorded membership there. Thus the weak bounds sharpen to the strict inequality.

This module isolates the reflection and unique-maximum algebraic core. It does not encode the finite-dimensional convex classification or claim a physical realization.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/OriginExclusionCenterReverse.strict_centre_reverse`
