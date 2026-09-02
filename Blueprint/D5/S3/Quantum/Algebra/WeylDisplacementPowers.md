# Powers of Weyl Displacement Words

## Abstract

Powers of a Weyl displacement word accumulate the triangular composition phase.

**Theorem 1.1 (Power law).**

$$\forall M: \mathbb{N},\ [\operatorname{NeZero}(M)],\ \forall a, b: \operatorname{ZMod}(M),\ \forall n: \mathbb{N},\ \operatorname{displacement}\left(M, a, b\right)^{n} = \operatorname{windowRoot}\left(M\right)^{\operatorname{val}\left(\operatorname{choose}\left(n, 2\right) \cdot a \cdot b\right)} \cdot \operatorname{displacement}\left(M, {n \cdot a}, {n \cdot b}\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/WeylDisplacementPowers.displacement_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The n-th power of a displacement word is the word at the n-fold index, scaled by one root of unity whose exponent is n.choose 2 times the product of the two indices.

At step k, composition contributes k * a * b to the exponent. These contributions sum to the triangular number n.choose 2 times a * b. The proof is an induction on n resting on the frozen composition law.

The frozen displacement_sq result is the n = 2 instance of this law. It remains exactly as frozen, and this module neither restates nor amends it.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/WeylDisplacementPowers.displacement_pow`
- Dependency: [D5/S3/Quantum/Algebra/WeylDisplacement](WeylDisplacement.md)
- Dependency: [D5/S3/Quantum/Algebra/WeylPhaseArithmetic](WeylPhaseArithmetic.md)
