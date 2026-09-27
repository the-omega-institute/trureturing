# Lifting a Label Law at Equal Total-Variation Distance

## Abstract

A prescribed label law Q lifts to a world law exactly when every label of positive Q-mass has a nonempty fiber, and then some lift is as close to the original world law as Q is to its label law.

**Definition 1.1 (The label kernel).**

$$K_{w,z} = [\lambda(w) = z]$$

*Formalization.* `D5/S3/TotalVariation/Equality/FiberwiseEqualDistanceLift.labelKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The deterministic kernel of the label map; applying it to a world law gives the pushforward label law.

**Theorem 1.2 (Equal-distance lift).**

$$\rho, Q \text{ probability laws on }W, Z, P = \lambda_{*} \rho \Rightarrow\\{}(\exists \widetilde{\rho} \text{ probability }, \lambda_{*} \widetilde{\rho} = Q) \iff (\forall z, Q(z) > 0 \Rightarrow \exists w, \lambda(w) = z) \land\\{}(\forall z, Q(z) > 0 \Rightarrow \exists w, \lambda(w) = z) \Rightarrow \exists \widetilde{\rho} \text{ probability }, \lambda_{*} \widetilde{\rho} = Q \land \operatorname{TV}(\rho, \widetilde{\rho}) = \operatorname{TV}(P, Q).$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Equality/FiberwiseEqualDistanceLift.fiberwise_equal_distance_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let rho be a probability law on the finite world W, lambda : W -> Z a label map, P the pushforward of rho and Q a probability law on Z. A lift of Q puts mass Q(z) on the fiber of z, so labels of positive Q-mass need nonempty fibers. Conversely, on a fiber with P(z) > 0 put tilde-rho(w) = Q(z) rho(w) / P(z), and on a fiber with P(z) = 0 put the mass Q(z) on one chosen element. This is a probability law with pushforward Q. On a fiber with P(z) > 0 all changes have the sign of Q(z) - P(z), and on a fiber with P(z) = 0 the law rho vanishes, so mass only increases. No fiber mixes an increase with a decrease, and the equality criterion for total-variation contraction under a channel gives TV(rho, tilde-rho) = TV(P, Q).

## References

- Truth anchor: `D5/S3/TotalVariation/Equality/FiberwiseEqualDistanceLift.fiberwise_equal_distance_lift`
- Truth anchor: `D5/S3/TotalVariation/Equality/FiberwiseEqualDistanceLift.labelKernel`
- Dependency: [D5/S3/TotalVariation/Equality/DataProcessingEquality](DataProcessingEquality.md)
