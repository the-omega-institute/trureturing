# Additive Section Carry Identity

## Abstract

The kernel-valued carry of an additive section satisfies the cocycle identity.

**Theorem 1.1 (An additive section carry satisfies the cocycle identity).**

$$\begin{gathered}\forall X, B, [\operatorname{AddCommGroup}\left(X\right)], [\operatorname{AddCommGroup}\left(B\right)],\\{}q: \operatorname{AddMonoidHom}\left(X, B\right), s: B \to X,\\{}\operatorname{RightInverse}\left(s, q\right) \Rightarrow \forall a, b, c\in B,\\{}\kappa_{q,s}(a, b) + \kappa_{q,s}(a+b, c) =\\{}\kappa_{q,s}(b, c) + \kappa_{q,s}(a, b+c).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/Cocycles/AdditiveCarryCocycleIdentity.additive_section_carry_cocycle_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let q be an additive homomorphism between commutative additive groups and let s be a right-inverse section of q. The named carry is the existing kernel-valued construction s(a)+s(b)-s(a+b).

For every a, b, and c in the quotient carrier, the two bracketings accumulate equal kernel-valued carries.

## References

- Truth anchor: `D5/S1/Deficit/Cocycles/AdditiveCarryCocycleIdentity.additive_section_carry_cocycle_identity`
- Dependency: [D5/S1/Deficit/Cocycles/AdditiveCarryCocycle](AdditiveCarryCocycle.md)
