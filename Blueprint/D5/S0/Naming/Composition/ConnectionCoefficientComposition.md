# Connection Coefficient Multiplication

## Abstract

Connection coefficients multiply along a two-step completion path, with the Ramanujan 541 radical split into Gaussian, exponential, and scale factors.

**Theorem 1.1 (Connection coefficients multiply along completion paths).**

$$\left(\forall a \in \mathbb{R}, b \in \mathbb{R}, X \in \mathbb{R}, Y \in \mathbb{R}, Z \in \mathbb{R},\; Y = a \cdot X \Rightarrow \left(Z = b \cdot Y \Rightarrow Z = (a \cdot b) \cdot X\right)\right) \land \left(\forall x \in \mathbb{R},\; 0 < x \Rightarrow \operatorname{sqrt}\left(\frac{\pi \cdot \operatorname{exp}\left(x\right)}{2 \cdot x}\right) = \operatorname{sqrt}\left(\frac{\pi}{2}\right) \cdot \operatorname{exp}\left(\frac{x}{2}\right) \cdot x^{\frac{-1}{2}}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Naming/Composition/ConnectionCoefficientComposition.connection_coefficient_multiplication` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first conjunct formalizes the two-step scalar path: if Y is aX and Z is bY, then Z is (ab)X. The real field supplies the commutative rearrangement used by the Lean proof.

The second conjunct records the Ramanujan 541 factorization on the positive real domain. It separates the Gaussian total mass, exponential flow, and scale Jacobian exactly as displayed in the source.

The first conjunct is discharged by elementary ring normalization. The second is assembled from pinned Mathlib square-root, exponential, and real-power identities; no unproved hypothesis or replacement object is introduced.

## References

- Truth anchor: `D5/S0/Naming/Composition/ConnectionCoefficientComposition.connection_coefficient_multiplication`
