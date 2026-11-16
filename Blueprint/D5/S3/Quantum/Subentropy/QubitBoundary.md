# Qubit subentropy near a pure state

## Abstract

A determinant expansion with a quantitative logarithmic remainder at the pure qubit boundary.

Let A be a complex two by two positive semidefinite matrix with trace one, let delta be the real part of its determinant, and let Q(A) be the determinant-integral subentropy. All logarithms are natural. The two eigenvalues are nonnegative, sum to one, and have product delta, so 0<=delta<=1/4.

**Theorem 1.1 (The determinant remainder).**

$$\forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \left(\operatorname{PosSemidef}\left(A\right) \land \operatorname{trace}\left(A\right) = 1\right) \Rightarrow \left(0 \le \operatorname{Re}\left(\operatorname{det}\left(A\right)\right) \land \left(\operatorname{Re}\left(\operatorname{det}\left(A\right)\right) \le \frac{1}{4} \land \left(\left(\operatorname{Re}\left(\operatorname{det}\left(A\right)\right) = 0 \Rightarrow \operatorname{Q}\left(A\right) = 0\right) \land \left(0 < \operatorname{Re}\left(\operatorname{det}\left(A\right)\right) \Rightarrow \left(0 \le \operatorname{Re}\left(\operatorname{det}\left(A\right)\right) - \operatorname{Q}\left(A\right) \land \operatorname{Re}\left(\operatorname{det}\left(A\right)\right) - \operatorname{Q}\left(A\right) \le \frac{\operatorname{Re}\left(\operatorname{det}\left(A\right)\right)^{2} \cdot \operatorname{log}\left(\frac{1}{\operatorname{Re}\left(\operatorname{det}\left(A\right)\right)}\right)}{1 - \operatorname{Re}\left(\operatorname{det}\left(A\right)\right)}\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Subentropy/QubitBoundary.qubit_subentropy_near_pure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For t>0 the determinant kernel is delta t/((1+t)(t squared+t+delta)). Subtracting it from delta/(1+t) squared gives the nonnegative remainder delta squared/((1+t) squared(t squared+t+delta)). Its denominator is at least (t+delta)(t+1), because their difference is t(t+1)(t squared+2t+delta), which is nonnegative.

When delta>0, the comparison function is delta squared/(1-delta) times the convergent reciprocal difference 1/(t+delta)-1/(t+1). Its integral is delta squared log(1/delta)/(1-delta). The inverse-square comparison has integral delta, and the density kernel is integrable, so integral monotonicity proves both bounds. When delta=0 the original determinant kernel vanishes pointwise on t>0 and Q(A)=0; no logarithmic formula at zero is used.

The error bound implies Q(A)=delta+O(delta squared times the absolute value of log delta) as delta decreases to zero through positive values, and Q(A)/delta tends to one. This supplies the leading term for any density family whose determinant is already known: delta asymptotic to epsilon squared/9 gives Q asymptotic to epsilon squared/9, while delta=sin(theta) squared/4 gives Q asymptotic to theta squared/4 as theta tends to zero. The determinant identities and normalization of those families are separate premises.

The result concerns finite density matrices. It makes no claim about a continuum path measure, tunneling probabilities, the emergence of time, or a physical realization of an early/late history model.

## References

- Truth anchor: `D5/S3/Quantum/Subentropy/QubitBoundary.qubit_subentropy_near_pure`
- Dependency: [D5/S3/Quantum/Subentropy/DensityKernel](DensityKernel.md)
