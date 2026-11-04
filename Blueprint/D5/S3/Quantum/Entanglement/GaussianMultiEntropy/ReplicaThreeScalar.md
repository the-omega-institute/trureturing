# Replica-three scalar expression and squeezing

## Abstract

The order-three Gaussian expression has a symmetric scalar extension to positive real party sizes. Its logarithmic quotient is strictly negative for positive squeezing and strictly decreases as squeezing increases; at vacuum it is zero. Real coordinates in this scalar extension do not represent fractional physical modes.

Scientific source: Haobo Ma then Wenlin Zhang, An exact balancing law for order-three Gaussian multi-entropy, released 4 November 2026 under CC BY 4.0. The fully symmetric physical family and equal-party observation are due to Camargo and Nishida. Classical majorization is credited to Marshall, Olkin and Arnold. The actual integral bridge belongs to the companion ReplicaThree module; the existing all-replica Fourier theorem and replica-four results retain their original scope and credits.

**Definition 1.1 (The pair sum).**

$$s=xy+xz+yz$$

*Formalization.* `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeScalar.pairSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The second elementary symmetric polynomial s = xy + xz + yz of the three labelled coordinates.

**Definition 1.2 (A labelled cut factor).**

$$D_{x}=1+kx(y+z)$$

*Formalization.* `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeScalar.cut` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D_x = 1 + k x(y + z). The three factors D_x, D_y and D_z are labelled occurrences: equal numerical values are retained with multiplicity.

**Definition 1.3 (The scalar value).**

$$V(k,x,y,z)=\frac{2\log(1+ks)-\log D_{x}-\log D_{y}-\log D_{z}}{12}$$

*Formalization.* `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeScalar.value` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

V(k,x,y,z) = (2 log(1 + ks) - log D_x - log D_y - log D_z)/12, with natural logarithms. For nonnegative coordinates and k >= 0 all four logarithm arguments are positive.

**Theorem 1.4 (Swap symmetry).**

$$V(k,x,y,z)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeScalar.value_swap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all real k,x,y,z, V(k,x,y,z)=V(k,y,x,z). Exchanging the first two party labels preserves all three cut factors with their multiplicities.

**Theorem 1.5 (Cyclic symmetry).**

$$V(k,x,y,z)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeScalar.value_cycle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all real k,x,y,z, V(k,x,y,z)=V(k,y,z,x). The majorization proof consumes this helper to order any three distinct party indices without dropping labelled multiplicities.

**Theorem 1.6 (The logarithmic quotient).**

$$V(k,x,y,z)=\frac{\log\frac{(1+ks)^2}{D_{x}D_{y}D_{z}}}{12}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeScalar.value_eq_log_ratio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real k,x,y,z >= 0, the scalar value equals log((1 + ks)^2/(D_x D_y D_z))/12. Positivity justifies splitting the logarithm of the product; no cut factor is removed at ties.

**Theorem 1.7 (Strict negativity away from vacuum).**

$$V(k,x,y,z)<0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeScalar.value_neg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For k > 0 and x,y,z > 0 the value is strictly negative. The denominator minus (1 + ks)^2 factors as k^2 xyz [N + k(Ns - xyz)], where N = x + y + z. Every factor is positive. Empty-party boundary points and k = 0 are excluded from this strict inequality.

**Theorem 1.8 (Vacuum and strict squeezing decrease).**

$$V(0,x,y,z)=0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeScalar.parameter_behavior` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every fixed x,y,z > 0, V(0,x,y,z) = 0 and k -> V(k,x,y,z) is strictly decreasing on the whole ray k >= 0. Indeed the sum of the three cut coefficients is 2s, and every cut coefficient is strictly smaller than s. For k > 0 this makes the squeezing derivative strictly negative. No negative derivative at vacuum is asserted; all triples tie there.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeScalar.cut`
- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeScalar.pairSum`
- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeScalar.parameter_behavior`
- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeScalar.value`
- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeScalar.value_cycle`
- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeScalar.value_eq_log_ratio`
- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeScalar.value_neg`
- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeScalar.value_swap`
