# Periodic Collapse

## Abstract

A periodic digit block is an affine map with an expanding multiplier, so exactly one starting point keeps its conjugate orbit bounded.

Reading a whole period as one step turns it into multiplication by the conjugate raised to the period, followed by subtracting the digits accumulated over that period. That map has one fixed point, and the distance to it is multiplied by the conjugate modulus raised to the period at every block. Since that multiplier exceeds one, the fixed point is the only starting value whose orbit stays bounded; every other one passes every bound.

**Theorem 1.1 (A periodic block collapses to one orbit).**

$$\forall c \in R, y \in R,\; \left(y = \operatorname{collapseCentre}\left(p, c\right) \Rightarrow \left(\forall k \in N,\; \operatorname{collapseIterate}\left(p, c, k, y\right) = y\right)\right) \land \left(y \ne \operatorname{collapseCentre}\left(p, c\right) \Rightarrow \left(\forall M \in R,\; \exists k \in N,\; M < \left|\operatorname{collapseIterate}\left(p, c, k, y\right) - \operatorname{collapseCentre}\left(p, c\right)\right|\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/NonPisotFrontier/PeriodicCollapse.periodic_block_collapses_to_one_orbit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The period is assumed nonzero; that is what makes the multiplier exceed one. Nothing here says which digit sequences actually arise, nor that the orbit of one is among the unbounded ones. It states only the dichotomy that any eventual period forces.

## References

- Truth anchor: `D5/S0/Tower/NonPisotFrontier/PeriodicCollapse.periodic_block_collapses_to_one_orbit`
- Dependency: [D5/S0/Tower/NonPisotFrontier/BetaThirteen](BetaThirteen.md)
