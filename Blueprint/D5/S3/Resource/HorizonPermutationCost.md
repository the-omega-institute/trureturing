# Finite-Horizon Permutation Simulation Cost

## Abstract

The exact number of internal states needed to reproduce a finite self-map through a prescribed horizon by initialized permutation dynamics.

Let X be any finite set, f a self-map of X, and H a natural number. A simulation consists of a finite state set E, a permutation P of E, a fixed total readout r from E to X, and an initialization i from X to E. For every x and every natural t at most H, the readout of P iterated t times at i(x) equals f iterated t times at x. Write S(f,H) for the collection of all such simulations. All internal state coordinates count toward the cardinality of E.

**Theorem 1.1 (The lower bound is attained).**

$$\forall X, [\operatorname{Finite}(X)], \forall f:X\to X, \forall H\in \mathbb{N},\\(\forall (E,P,r,i)\in S(f,H), \lvert X \rvert + H\cdot \lvert X\setminus f(X) \rvert\leq \lvert E \rvert)\\\land (\exists (E,P,r,i)\in S(f,H), \lvert E \rvert=\lvert X \rvert + H\cdot \lvert X\setminus f(X) \rvert)$$

*Proof.* Machine-checked in Lean as `D5/S3/Resource/HorizonPermutationCost.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite X, every f and every H, all simulations have at least |X| + H times |X minus f(X)| states, and some simulation has exactly that many. Empty X, horizon zero, and bijective f are included. The readout has no time argument, and the simulation law is required only on initialized trajectories through H.

At time H, initialized trajectories give |X| distinct states. For each point without a predecessor, its states at times zero through H minus one are distinct from each other and from the time-H states. Cancelling the earlier permutation iterate would otherwise put a point without a predecessor in the image of a positive iterate of f.

Choose one predecessor of each image point and extend these selected edges to a permutation q of X. Every q-edge entering an image point is then an f-edge. Subdivide each remaining edge, which enters a missing-image point, by H new states. Read an added state by applying the corresponding positive iterate of f to that edge's source. An initialized trajectory enters an added segment only after a positive number of steps, so it cannot leave that segment within H steps. The construction adds exactly H states per missing-image point.

## References

- Truth anchor: `D5/S3/Resource/HorizonPermutationCost.result`
- Dependency: [D5/S3/ObserverMemory/Realization/FreeWindowRealizationCapacity](../ObserverMemory/Realization/FreeWindowRealizationCapacity.md)
