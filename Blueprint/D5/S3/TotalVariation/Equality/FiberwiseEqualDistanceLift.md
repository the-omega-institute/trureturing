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

$$\forall W, Z: Type, [\operatorname{Fintype}\left(W\right)] [\operatorname{Fintype}\left(Z\right)] [\operatorname{DecidableEq}\left(Z\right)] \forall \rho: W \to \mathbb{R}, (\forall w, 0 \leq \rho(w)) \Rightarrow ((\sum_{w} \rho(w) = 1) \Rightarrow (\forall \lambda: W \to Z, \forall Q: Z \to \mathbb{R}, (\forall z, 0 \leq Q(z)) \Rightarrow ((\sum_{z} Q(z) = 1) \Rightarrow (((\exists \rho': W \to \mathbb{R}, (\forall w, 0 \leq \rho'(w)) \land ((\sum_{w} \rho'(w) = 1) \land (\operatorname{channelOutput}\left(\operatorname{labelKernel}\left(\lambda\right), \rho'\right) = Q))) \iff (\forall z, Q(z) > 0 \Rightarrow \exists w, \lambda(w) = z)) \land\\{}((\forall z, Q(z) > 0 \Rightarrow \exists w, \lambda(w) = z) \Rightarrow \exists \rho': W \to \mathbb{R}, (\forall w, 0 \leq \rho'(w)) \land ((\sum_{w} \rho'(w) = 1) \land ((\operatorname{channelOutput}\left(\operatorname{labelKernel}\left(\lambda\right), \rho'\right) = Q) \land (\operatorname{TV}(\rho, \rho') = \operatorname{TV}(\operatorname{channelOutput}\left(\operatorname{labelKernel}\left(\lambda\right), \rho\right), Q))))).))))$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Equality/FiberwiseEqualDistanceLift.fiberwise_equal_distance_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let rho be a probability law on the finite world W, lambda : W -> Z a label map, P the pushforward of rho and Q a probability law on Z. A lift of Q puts mass Q(z) on the fiber of z, so labels of positive Q-mass need nonempty fibers. Conversely, on a fiber with P(z) > 0 put tilde-rho(w) = Q(z) rho(w) / P(z), and on a fiber with P(z) = 0 put the mass Q(z) on one chosen element. This is a probability law with pushforward Q. On a fiber with P(z) > 0 all changes have the sign of Q(z) - P(z), and on a fiber with P(z) = 0 the law rho vanishes, so mass only increases. No fiber mixes an increase with a decrease, and the equality criterion for total-variation contraction under a channel gives TV(rho, tilde-rho) = TV(P, Q).

## References

- Truth anchor: `D5/S3/TotalVariation/Equality/FiberwiseEqualDistanceLift.fiberwise_equal_distance_lift`
- Truth anchor: `D5/S3/TotalVariation/Equality/FiberwiseEqualDistanceLift.labelKernel`
- Dependency: [D5/S3/TotalVariation/Equality/DataProcessingEquality](DataProcessingEquality.md)
