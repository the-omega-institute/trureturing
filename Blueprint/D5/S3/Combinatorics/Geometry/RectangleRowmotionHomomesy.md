# Rectangle rowmotion max-minus-min homomesy

## Abstract

The max-minus-min statistic is zero-sum on every literal interval-closed rectangle rowmotion orbit.

For a finite rectangle Point(m,n) = Fin m × Fin n with coordinatewise order, a complete reverse extension enumerates the points from larger to smaller. During the first N trace steps, each point is visited once and is toggled when symmetric difference preserves interval-closedness. For a fixed input I, trace(e,I,k) equals trace(e,I,N) for every trace index k at least N. One rowmotion step is the unary map rowmotion(e): S ↦ trace(e,S,N); repeated rowmotion applies this whole N-step map to each new input state. The orbit is the finite set of distinct states reached by those applications.

**Definition 1.1 (The finite literal rowmotion orbit).**

$$\forall m \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall N \in \mathbb{N},\; \forall e \in \operatorname{Equiv}\left(\operatorname{Fin}\left(N\right), \operatorname{Point}\left(m, n\right)\right),\; \forall I \in \operatorname{Set}\left(\operatorname{Point}\left(m, n\right)\right),\; \operatorname{literalOrbit}\left(e, I\right) = Finset \{S \in \operatorname{Set}\left(\operatorname{Point}\left(m, n\right)\right) \mid \exists k \in \mathbb{N},\; \operatorname{iterate}\left(\operatorname{rowmotion}\left(e\right), k, I\right) = S\}$$

*Formalization.* `D5/S3/Combinatorics/Geometry/RectangleRowmotionHomomesy.literalOrbit` (`✓ std3`).

*Citation.* Jennifer Elder, Nadia Lafrenière, Erin McNicholas, Jessica Striker, Amanda Welch (2024). *Toggling, rowmotion, and homomesy on interval-closed sets*. DOI: [10.48550/arXiv.2307.08520](https://doi.org/10.48550/arXiv.2307.08520). URL: <https://arxiv.org/abs/2307.08520v2>.

*Commentary.*

The orbit contains each distinct set state S for which some natural iterate of the actual trace from I equals S. It is a Finset of sets, so every reachable state is counted once; no period, transition identity, or selected finite testing range is assumed.

**Definition 1.2 (The integer max-minus-min statistic).**

$$\forall m \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall I \in \operatorname{Set}\left(\operatorname{Point}\left(m, n\right)\right),\; \operatorname{maxMinusMin}\left(I\right) = (\operatorname{card}\left(\{a \in \operatorname{Point}\left(m, n\right) \mid \operatorname{Maximal}\left(I, a\right)\}\right):\mathbb{Z}) - (\operatorname{card}\left(\{u \in \operatorname{Point}\left(m, n\right) \mid \operatorname{Minimal}\left(I, u\right)\}\right):\mathbb{Z})$$

*Formalization.* `D5/S3/Combinatorics/Geometry/RectangleRowmotionHomomesy.maxMinusMin` (`✓ std3`).

*Citation.* Jennifer Elder, Nadia Lafrenière, Erin McNicholas, Jessica Striker, Amanda Welch (2024). *Toggling, rowmotion, and homomesy on interval-closed sets*. DOI: [10.48550/arXiv.2307.08520](https://doi.org/10.48550/arXiv.2307.08520). URL: <https://arxiv.org/abs/2307.08520v2>.

*Commentary.*

The statistic is the integer cast of the number of globally maximal members of a state minus the integer cast of the number of globally minimal members. It is defined for every set, including the empty set.

**Theorem 1.3 (The original all-rectangle homomesy conjecture).**

$$\forall m \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall N \in \mathbb{N},\; ((0 < m) \land (0 < n)) \Rightarrow \left(\forall e \in \operatorname{Equiv}\left(\operatorname{Fin}\left(N\right), \operatorname{Point}\left(m, n\right)\right),\; (\operatorname{ReverseExtension}\left(e\right)) \Rightarrow \left(\forall I \in \operatorname{Set}\left(\operatorname{Point}\left(m, n\right)\right),\; (\operatorname{OrdConnected}\left(I\right)) \Rightarrow \sum_{S \in \operatorname{literalOrbit}\left(e, I\right)} \operatorname{maxMinusMin}\left(S\right) = 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/RectangleRowmotionHomomesy.result` (`✓ std3`). ∎

*Resolves.* `Problems/rectangle-rowmotion-max-minus-min-homomesy` (proved) by `D5/S3/Combinatorics/Geometry/RectangleRowmotionHomomesy.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"rectangle-rowmotion-max-minus-min-homomesy","declaration_gid":"D5/S3/Combinatorics/Geometry/RectangleRowmotionHomomesy.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jennifer Elder, Nadia Lafrenière, Erin McNicholas, Jessica Striker, Amanda Welch (2024). *Toggling, rowmotion, and homomesy on interval-closed sets*. DOI: [10.48550/arXiv.2307.08520](https://doi.org/10.48550/arXiv.2307.08520). URL: <https://arxiv.org/abs/2307.08520v2>.

*Acknowledgement.* Nadia Lafrenière, Joel Brewster Lewis, Erin McNicholas, Jessica Striker, Amanda Welch (2025). *Interval-closed set rowmotion and homomesy on products of two chains*. DOI: [10.48550/arXiv.2505.04000](https://doi.org/10.48550/arXiv.2505.04000). URL: <https://arxiv.org/abs/2505.04000v1>.

*Commentary.*

For all positive rectangle dimensions, every complete legal reverse extension, and every order-convex initial set, the sum of maxMinusMin over the actual distinct forward orbit states is zero. The proof counts strict rectangular corners with the frozen RectangularCorner theorem, transports endpoint pairs through the literal trace with the frozen RowmotionEndpointTransport theorem, and obtains an integer coboundary. Reversing coordinates supplies the dual count; a recovered reverse trace proves that the literal trace permutes its finite orbit. No global transition law, potential, orbit pairing, width bound, or finite-instance premise is added.

This is the exact max-minus-min conjecture stated as Conjecture 4.9 of the published interval-closed-set rowmotion paper and restated as Conjecture 4.2 in the follow-up paper. The repository result settles that original target for every product of two finite chains; the follow-up's separate signed-cardinality result and its other scopes are outside this claim.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/RectangleRowmotionHomomesy.literalOrbit`
- Truth anchor: `D5/S3/Combinatorics/Geometry/RectangleRowmotionHomomesy.maxMinusMin`
- Truth anchor: `D5/S3/Combinatorics/Geometry/RectangleRowmotionHomomesy.result`
- Dependency: [D5/S3/Combinatorics/Geometry/RectangularCorner](RectangularCorner.md)
- Dependency: [D5/S3/Combinatorics/Geometry/RowmotionEndpointTransport](RowmotionEndpointTransport.md)
