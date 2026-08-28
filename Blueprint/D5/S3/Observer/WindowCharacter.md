# Absence of Characters on Nontrivial Finite Windows

## Abstract

Nontrivial finite window matrix algebras have no complex-algebra character.

**Theorem 1.1 (Nontrivial finite window algebras have no character).**

$$\forall M \in \mathbb{N}_{>1},\ [\operatorname{NeZero}(M)],\ \operatorname{IsEmpty}(M_{M}(\mathbb{C})\to_{\mathbb{C}\text{-alg}}\mathbb{C})$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/WindowCharacter.window_algebra_has_no_character` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let M be a window cardinality greater than one, and suppose that phi is a unital complex-algebra homomorphism from the M-by-M window matrix algebra to the complex numbers. Applying phi to the finite Weyl relation and using commutativity of the target gives (1 - omega_M) phi(V_M) phi(U_M) = 0.

The window phase is a primitive M-th root. Since M is greater than one, omega_M is not one, so the two generator images have zero product. On the other hand, the M-th powers of both window generators are the identity. Their images therefore have M-th power one and are both nonzero, a contradiction. The strict inequality on M supplies exactly the nontriviality of the primitive phase; no statement is made here for a one-address window or for matrix algebras with unrelated index sets.

## References

- Truth anchor: `D5/S3/Observer/WindowCharacter.window_algebra_has_no_character`
- Dependency: [D5/S3/Observer/WindowRegister](WindowRegister.md)
