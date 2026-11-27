# A parity formula for the mass difference

## Abstract

Mass differences on a finite Boolean cube with equal deletion marginals.

**Theorem 1.1 (Agreement after deleting each coordinate).**

$$\begin{aligned}\forall (I: \operatorname{Type})[\operatorname{Fintype}(I)][\operatorname{DecidableEq}(I)](\mu: (I \to \operatorname{Bool}) \to \mathbb{R})(\nu: (I \to \operatorname{Bool}) \to \mathbb{R}),\\\operatorname{let} s((x: I \to \operatorname{Bool})):=\prod_{i \in I}(-1)^{x(i)},\\\operatorname{let} d:=\sum_{x \in (I \to \operatorname{Bool})}(\mu(x)-\nu(x))s(x) \operatorname{in}\\(\forall (i: I)(x: I \to \operatorname{Bool}),\mu(x[i \mapsto 0])+\mu(x[i \mapsto 1])=\nu(x[i \mapsto 0])+\nu(x[i \mapsto 1])) \longrightarrow\\(\forall (x: I \to \operatorname{Bool}),\mu(x)-\nu(x)=\frac{d}{2^{\left|I\right|}}s(x)) \land \operatorname{TV}(\mu,\nu)=\frac{\left|d\right|}{2}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/BooleanDeletionParity.boolean_deletion_mass_difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take two real mass functions on a finite indexed Boolean cube. For each coordinate and assignment of the other bits, assume the two functions have equal sums over the two values of the omitted bit. Write d for the full parity sign moment of the first function minus that of the second. In the formula, x[i mapped to b] updates only coordinate i, and the exponent uses the bit value zero or one. At each vector, the mass difference is d divided by the size of the cube, times the vector's parity sign. Total variation is half the absolute value of d.

Equal deletion marginals force the mass difference to change sign at each single-bit flip. Flipping the coordinates in the support of a vector recovers its difference from the value at the all-zero vector. Summation against the parity sign fixes the coefficient. For a minimal dependent group of binary outputs, the joint law and the product of its marginals agree after every deletion, so this identity gives the distance between those two laws.

## References

- Truth anchor: `D5/S3/TotalVariation/BooleanDeletionParity.boolean_deletion_mass_difference`
- Dependency: [D5/S3/TotalVariation/Pinsker](Pinsker.md)
