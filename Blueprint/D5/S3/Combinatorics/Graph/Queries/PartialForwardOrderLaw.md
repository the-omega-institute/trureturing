# Partial observations of binary forward orders

## Abstract

Likelihood and posterior for partial observations of independent binary orders.

**Theorem 1.1 (One factor of one half per observed position).**

Lean statement: `D5/S3/Combinatorics/Graph/Queries/PartialForwardOrderLaw.partial_forward_order_likelihood`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Queries/PartialForwardOrderLaw.partial_forward_order_likelihood` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take finitely many positions, each with two distinct available values. Assign an independent uniform order to its two slots. A fixed observation may specify neither, one, or both slots at each position.

The observation is compatible if each specified value is available at its position and two specified slots at the same position have different values. If s is the set of positions with a specified slot, a compatible observation has outer mass two to the power minus the size of s. An incompatible observation has mass zero.

One specified slot determines the order of two distinct values. A second specified slot tests the already determined order. The compatible tables thus form the product cylinder that fixes one order at each observed position.

**Theorem 1.2 (The posterior is the prior conditioned on compatibility).**

Lean statement: `D5/S3/Combinatorics/Graph/Queries/PartialForwardOrderLaw.partial_forward_order_posterior`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Queries/PartialForwardOrderLaw.partial_forward_order_posterior` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a world sampled from a probability mass function determine the two distinct available values at every position. Draw the uniform order table independently. A given partial observation has the same number of observed positions in every world.

If the joint observation has positive mass, the posterior mass of each set of worlds is its prior mass intersected with the compatible worlds, divided by the prior mass of all compatible worlds. The common positive likelihood cancels from the two outer masses.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Queries/PartialForwardOrderLaw.partial_forward_order_likelihood`
- Truth anchor: `D5/S3/Combinatorics/Graph/Queries/PartialForwardOrderLaw.partial_forward_order_posterior`
- Dependency: [D5/S3/Combinatorics/Graph/Queries/FixedNeighborOrder](FixedNeighborOrder.md)
