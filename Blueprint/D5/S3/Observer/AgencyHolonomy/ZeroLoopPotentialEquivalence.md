# Zero Loop Potential Equivalence

## Abstract

An additive cost on a connected path groupoid has zero closed-path sums exactly when it is the difference of a vertex potential.

**Theorem 1.1 (Zero closed-path costs are exactly potential differences).**

$$\forall Z: Type, K: Type, C: (\forall x, y: Z, Hom\left(x, y\right) \to K), Groupoid\left(Z\right) \land IsConnected\left(Z\right) \land AddCommGroup\left(K\right) \land (\forall x, y, z: Z, f: Hom\left(x, y\right), g: Hom\left(y, z\right), C\left(compose\left(f, g\right)\right) = C\left(f\right) + C\left(g\right)) \land (\forall x, y: Z, f: Hom\left(x, y\right), C\left(inv\left(f\right)\right) = - C\left(f\right)) \Rightarrow ((\forall z: Z, loop: Hom\left(z, z\right), C\left(loop\right) = 0) \iff (\exists potential: Z \to K, \forall x, y: Z, edge: Hom\left(x, y\right), C\left(edge\right) = potential\left(y\right) - potential\left(x\right))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/ZeroLoopPotentialEquivalence.closed_path_zero_iff_exists_potential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cost is additive under path composition and changes sign under inversion. A potential therefore telescopes around every closed path, giving zero total cost.

Conversely, choose a base object and one path from it to every object. The cost of the chosen path defines the potential. Closing the comparison path with the inverse chosen path shows that every edge cost is the corresponding potential difference.

## References

- Truth anchor: `D5/S3/Observer/AgencyHolonomy/ZeroLoopPotentialEquivalence.closed_path_zero_iff_exists_potential`
