# Quaternion norms and projective ternion laws

## Abstract

Integer Hamilton quaternions, the projective ternion heap and the signed spinor kernel for Chapter 32, section 32.8 and Appendix Q.

**Theorem 1.1 (Quaternion multiplication multiplies squared norms).**

$$\forall a \in Quaternion, b \in Quaternion,\; \operatorname{normSq}\left(\operatorname{mul}\left(a, b\right)\right) = \operatorname{normSq}\left(a\right) \cdot \operatorname{normSq}\left(b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaTernionHeap.normSq_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The squared norm is the sum of the four squared integer coordinates. The identity holds for all input pairs.

**Theorem 1.2 (Left absorption of rays).**

$$\forall x \in Quaternion, z \in Quaternion,\; \left(\operatorname{Nonzero}\left(x\right) \land \operatorname{Nonzero}\left(z\right)\right) \Rightarrow \operatorname{RayEquiv}\left(\operatorname{triad}\left(x, x, z\right), z\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaTernionHeap.triad_left_absorption` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplying x by its conjugate leaves the scalar squared norm, so the repeated pair contributes a nonzero signed scale.

**Theorem 1.3 (Right absorption of rays).**

$$\forall x \in Quaternion, z \in Quaternion,\; \left(\operatorname{Nonzero}\left(x\right) \land \operatorname{Nonzero}\left(z\right)\right) \Rightarrow \operatorname{RayEquiv}\left(\operatorname{triad}\left(x, z, z\right), x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaTernionHeap.triad_right_absorption` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The conjugate of z followed by z gives the same central scalar squared norm.

**Theorem 1.4 (Nested ternion products agree as rays).**

$$\forall x \in Quaternion, y \in Quaternion, z \in Quaternion, u \in Quaternion, v \in Quaternion,\; \left(\operatorname{Nonzero}\left(x\right) \land \left(\operatorname{Nonzero}\left(y\right) \land \left(\operatorname{Nonzero}\left(z\right) \land \left(\operatorname{Nonzero}\left(u\right) \land \operatorname{Nonzero}\left(v\right)\right)\right)\right)\right) \Rightarrow \operatorname{RayEquiv}\left(\operatorname{triad}\left(\operatorname{triad}\left(x, y, z\right), u, v\right), \operatorname{triad}\left(x, y, \operatorname{triad}\left(z, u, v\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaTernionHeap.triad_assoc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both nestings multiply x, the conjugate of y, z, the conjugate of u and v in the same order.

**Theorem 1.5 (The four-dimensional Lagrange identity).**

$$\forall a \in Quaternion, b \in Quaternion,\; \operatorname{normSq}\left(a\right) \cdot \operatorname{normSq}\left(b\right) - \operatorname{dot}\left(a, b\right) \cdot \operatorname{dot}\left(a, b\right) = \operatorname{minorSquares}\left(a, b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaTernionHeap.lagrange_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The right side sums the squares of the six minors a_i b_j minus a_j b_i, one for each coordinate pair i < j.

**Theorem 1.6 (Projective fidelity is bounded by one).**

$$\forall a \in Quaternion, b \in Quaternion,\; \left(\operatorname{Nonzero}\left(a\right) \land \operatorname{Nonzero}\left(b\right)\right) \Rightarrow \operatorname{kappa}\left(a, b\right) \le 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaTernionHeap.kappa_le_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The denominator is the product of squared norms. The Lagrange identity gives the nonnegative difference between that product and the squared dot product.

**Theorem 1.7 (Common heap translation preserves fidelity).**

$$\forall a \in Quaternion, b \in Quaternion, u \in Quaternion, v \in Quaternion,\; \left(\operatorname{Nonzero}\left(u\right) \land \operatorname{Nonzero}\left(v\right)\right) \Rightarrow \operatorname{Equivalent}\left(\operatorname{kappa}\left(\operatorname{triad}\left(a, u, v\right), \operatorname{triad}\left(b, u, v\right)\right), \operatorname{kappa}\left(a, b\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaTernionHeap.kappa_heap_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The common right factor is the conjugate of u times v. Its squared norm scales each squared norm and the dot product by the same positive factor.

**Theorem 1.8 (The Cayley lift numerator has squared norm equal to squared radius).**

$$\forall a \in \mathbb{Z}, b \in \mathbb{Z}, c \in \mathbb{Z}, d \in \mathbb{Z},\; \operatorname{normSq}\left(\operatorname{liftNum}\left(a, b, c, d\right)\right) = \operatorname{liftRadius}\left(a, b, c, d\right) \cdot \operatorname{liftRadius}\left(a, b, c, d\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaTernionHeap.lift_normSq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The homogeneous lift uses numerator (a²−s, 2ab, 2ac, 2ad) and radius a²+s, where s=b²+c²+d². Every nonzero quadruple gives a positive radius.

**Theorem 1.9 (The signed kernel determines the ray kernel).**

$$\forall p \in PythSpinor, q \in PythSpinor,\; \operatorname{Equivalent}\left(\operatorname{kappaProj}\left(p, q\right), \left(2 \cdot \operatorname{kappaSpin}\left(p, q\right) - 1\right) \cdot \left(2 \cdot \operatorname{kappaSpin}\left(p, q\right) - 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaTernionHeap.quadratic_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Twice the signed fidelity minus one is the signed dot product divided by the product of the two radii. Squaring gives projective fidelity.

## References

- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaTernionHeap.kappa_heap_invariant`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaTernionHeap.kappa_le_one`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaTernionHeap.lagrange_identity`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaTernionHeap.lift_normSq`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaTernionHeap.normSq_mul`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaTernionHeap.quadratic_kernel`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaTernionHeap.triad_assoc`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaTernionHeap.triad_left_absorption`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaTernionHeap.triad_right_absorption`
