# Arithmetic of the Weyl Window Root

## Abstract

Arithmetic of powers and products of the finite window root.

**Theorem 1.1 (Window-root powers depend only on the exponent modulo the window).**

$$\forall M: \mathbb{N},\ [\operatorname{NeZero}(M)],\ \forall n: \mathbb{N},\ \operatorname{windowRoot}\left(M\right)^{\operatorname{mod}\left(n, M\right)} = \operatorname{windowRoot}\left(M\right)^{n}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/WeylPhaseArithmetic.windowRoot_pow_mod` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The powers of the window root depend only on the exponent modulo M, because the root is a primitive M-th root of unity.

The frozen WeylDisplacement module holds an equivalent of this first lemma behind private, so it cannot be imported, and frozen modules are not amended; this module is the single public home so that consumers import it rather than keeping a private copy each.

**Theorem 1.2 (Window-root phases multiply by adding their indices).**

$$\forall M: \mathbb{N},\ [\operatorname{NeZero}(M)],\ \forall x, y: \operatorname{ZMod}(M),\ \operatorname{windowRoot}\left(M\right)^{\operatorname{val}\left(x + y\right)} = \operatorname{windowRoot}\left(M\right)^{\operatorname{val}\left(x\right)} \cdot \operatorname{windowRoot}\left(M\right)^{\operatorname{val}\left(y\right)}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/WeylPhaseArithmetic.windowRoot_pow_val_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two phases multiply by adding their indices in ZMod M: the value of the sum is the exponent of the product of the two phases.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/WeylPhaseArithmetic.windowRoot_pow_mod`
- Truth anchor: `D5/S3/Quantum/Algebra/WeylPhaseArithmetic.windowRoot_pow_val_add`
- Dependency: [D5/S3/Observer/WindowRegister](../../Observer/WindowRegister.md)
