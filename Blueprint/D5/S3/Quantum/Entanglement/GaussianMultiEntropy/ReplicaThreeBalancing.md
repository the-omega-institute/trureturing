# Strict pair balancing at replica three

## Abstract

Every proper convex mixing of unequal positive scalar coordinates strictly decreases the replica-three value. Identity, full swap and tied pairs account for exactly all equalities. Real coordinates here are a scalar extension, not fractional physical modes.

Scientific source: Haobo Ma then Wenlin Zhang, An exact balancing law for order-three Gaussian multi-entropy, 4 November 2026, CC BY 4.0. The physical family is due to Camargo and Nishida; classical majorization is credited to Marshall, Olkin and Arnold.

**Theorem 1.1 (Pair mixing and its complete equality classification).**

$$V(k,x',y',z)\le V(k,x,y,z);V(k,x',y',z)=V(k,x,y,z) \iff t=0 \lor t=1 \lor x=y$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeBalancing.pair_mixing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every k,x,y,z > 0 and 0 <= t <= 1, set x' = (1-t)x + ty and y' = tx + (1-t)y. Then V(k,x',y',z) <= V(k,x,y,z), with equality if and only if t = 0, t = 1, or x = y. In particular a proper mixing of unequal coordinates strictly lowers V while preserving x+y+z and positivity. The proof compares the positive logarithmic quotients at fixed x+y and z. Their cross difference factors as k^2 z (x'y' - xy) times a strictly positive polynomial; x'y' - xy = t(1-t)(x-y)^2. This establishes the local balancing law without assuming Schur convexity.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeBalancing.pair_mixing`
- Dependency: [D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeScalar](ReplicaThreeScalar.md)
