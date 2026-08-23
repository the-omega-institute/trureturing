# Interior Probability Fibers and Relative Phases

## Abstract

A strictly positive projective probability fiber has canonical relative phases.

**Theorem 1.1 (Relative phases coordinatize the interior probability fiber).**

$$\forall n\in \mathbb{N}, p\in \operatorname{int}(\Delta_{n}),\\{}(\forall i, p_{i} > 0) \Rightarrow\\{}\operatorname{Bijective}(\operatorname{relativePhaseCoordinates}\left(p\right): q_{B}^{-1}\{p\} \to T^{{n}}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/InteriorProbabilityPhaseFiber.interior_probability_fiber_relative_phase_coordinates_bijective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An interior probability vector has n plus one strictly positive real coordinates summing to one. A polar representative pairs those probabilities with one unit complex phase per basis coordinate.

Projective states are constructed by quotienting representatives that have equal probabilities and differ by one common unit phase. The basis-probability map forgets the phase class.

The named coordinate map divides each non-reference phase by phase zero. It is invariant under common phase, and gauge fixing phase zero to one supplies its inverse. Thus the fiber is coordinatized by exactly n independent circle factors.

## References

- Truth anchor: `D5/S3/Quantum/Fibers/InteriorProbabilityPhaseFiber.interior_probability_fiber_relative_phase_coordinates_bijective`
