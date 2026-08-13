# Contracting Axis Sign and Depth

## Abstract

Contracting-axis powers split into parity sign and inverse-golden depth.

**Theorem 1.1 (Contracting powers separate sign and depth).**

$$\forall n\in\mathbb{N},\ \operatorname{contractingEigenvalue}^{n} = (-1)^{n} \varphi^{-n}$$

*Proof.* Machine-checked in Lean as `D5/S1/Eigenstructure/ContractingAxisSignDepth.contracting_axis_power_sign_depth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The contracting eigenvalue is minus the reciprocal golden ratio. Its nth power therefore factors into the parity sign (-1)^n and inverse-golden magnitude phi^(-n).

The proof is a thin normalization wrapper over the standard power lemmas for negation, inverses, and integer exponents.

This is a partial closure of the contracting-axis sign-reversal clause. The expanding-axis assignment and global spiral interpretation remain open.

## References

- Truth anchor: `D5/S1/Eigenstructure/ContractingAxisSignDepth.contracting_axis_power_sign_depth`
- Dependency: [D5/S1/Scale/FibonacciEigen](../Scale/FibonacciEigen.md)
