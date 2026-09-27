# Parity Affinities and the Positive Perron Vector

## Abstract

The two parity-class affinities determine a unique positive scalar root and an explicit positive eigenvector of the geometrically symmetrized parity kernel.

**Definition 1.1 (Parity classes).**

$$C_{p} = \{x \mid \operatorname{chi}(x) = p\}$$

*Formalization.* `D5/S3/Estimation/TimeArrow/ParityAffinityPerron.parityClass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The class C_p consists of the sign vectors whose parity character equals the real sign p.

**Definition 1.2 (Class affinity).**

$$eta_{p}(b) = \frac{\sum_{x \in C_{p}} \sqrt{1 - \operatorname{b}(x)^{2}}}{2^{d - 1}}$$

*Formalization.* `D5/S3/Estimation/TimeArrow/ParityAffinityPerron.classAffinity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The affinity of a parity class is the normalized cross product of its positive and negative square-root vectors.

**Definition 1.3 (Positive square-root vector).**

$$u_{p}(x) = \mathbf{1}_{C_{p}}(x) \sqrt{1 + \operatorname{b}(x)}$$

*Formalization.* `D5/S3/Estimation/TimeArrow/ParityAffinityPerron.classU` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The vector u_p is supported on C_p and has coordinate sqrt(1+b(x)) there.

**Definition 1.4 (Negative square-root vector).**

$$v_{p}(x) = \mathbf{1}_{C_{p}}(x) \sqrt{1 - \operatorname{b}(x)}$$

*Formalization.* `D5/S3/Estimation/TimeArrow/ParityAffinityPerron.classV` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The vector v_p is supported on C_p and has coordinate sqrt(1-b(x)) there.

**Definition 1.5 (Geometric symmetrization).**

$$R(x, y) = \sqrt{P_{chib}(x, y) P_{chib}(y, x)}$$

*Formalization.* `D5/S3/Estimation/TimeArrow/ParityAffinityPerron.affinityKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The affinity kernel is the entrywise geometric mean of the parity kernel and its transpose, with profile x mapped to chi(x)b(x).

**Definition 1.6 (Explicit four-vector).**

$$h = \frac{eta_{+}(eta_{-}^{2} + z)}{z} u_{+} + \frac{eta_{-}z(1 + z)}{z} u_{-} + (eta_{-}^{2} + z)v_{+} + z(1 + z)v_{-}$$

*Formalization.* `D5/S3/Estimation/TimeArrow/ParityAffinityPerron.affinityPerronVector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The candidate vector is the prescribed positive linear combination of the four class-supported square-root vectors.

**Theorem 1.7 (Unique positive affinity root).**

$$0 < eta_{+} \leq 1 \land 0 < eta_{-} \leq 1 \Rightarrow \exists z, 0 < z \leq 1 \land z^{2}(1 + z)^{2} = (z + eta_{+}^{2})(z + eta_{-}^{2}) \land \forall w, (0 < w \land w^{2}(1 + w)^{2} = (w + eta_{+}^{2})(w + eta_{-}^{2})) \Rightarrow w = z$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/ParityAffinityPerron.affinityEquation_unique_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive eta_+ and eta_- at most one, the quartic affinity equation has a root in (0,1], and every positive root equals it.

The difference of the two sides is negative at zero and nonnegative at one. Continuity gives a root, while the quotient of the left side by the right side is strictly increasing on the positive half-line.

**Theorem 1.8 (Positive eigenvector from the affinity root).**

$$1 \leq d \land \forall x, \lvert \operatorname{b}(x) \rvert < 1 \land \sum_{x \in C_{+}} \operatorname{b}(x) = 0 \land \sum_{x \in C_{-}} \operatorname{b}(x) = 0 \land eta_{+} = eta_{+}(b) \land eta_{-} = eta_{-}(b) \land 0 < z \land z^{2}(1 + z)^{2} = (z + eta_{+}^{2})(z + eta_{-}^{2}) \Rightarrow\\{}(\forall x, 0 < \operatorname{h}(x)) \land (\forall x, \sum_{y} R(x, y)\operatorname{h}(y) = \frac{1 + z}{2}\operatorname{h}(x))$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/ParityAffinityPerron.affinity_perronVector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume d is positive, the profile has absolute value below one, and its sum vanishes on each parity class. Let eta_+ and eta_- be the two class affinities, and let z be a positive root of the affinity equation.

The proper-coordinate law at the empty coordinate set gives zero total parity, so both classes have 2^(d-1) vertices. The zero sums then give the two squared norms and the class cross products. These identities evaluate the rank-four action of R, and the root equation supplies the final coefficient identity. Every surviving square root and every coefficient is positive, so h is entrywise positive and has eigenvalue (1+z)/2.

## References

- Truth anchor: `D5/S3/Estimation/TimeArrow/ParityAffinityPerron.affinityEquation_unique_root`
- Truth anchor: `D5/S3/Estimation/TimeArrow/ParityAffinityPerron.affinityKernel`
- Truth anchor: `D5/S3/Estimation/TimeArrow/ParityAffinityPerron.affinityPerronVector`
- Truth anchor: `D5/S3/Estimation/TimeArrow/ParityAffinityPerron.affinity_perronVector`
- Truth anchor: `D5/S3/Estimation/TimeArrow/ParityAffinityPerron.classAffinity`
- Truth anchor: `D5/S3/Estimation/TimeArrow/ParityAffinityPerron.classU`
- Truth anchor: `D5/S3/Estimation/TimeArrow/ParityAffinityPerron.classV`
- Truth anchor: `D5/S3/Estimation/TimeArrow/ParityAffinityPerron.parityClass`
- Dependency: [D5/S3/Estimation/TimeArrow/ParityKernelSubcoordinates](ParityKernelSubcoordinates.md)
