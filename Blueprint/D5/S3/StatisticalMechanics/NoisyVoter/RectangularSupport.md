# Graph-ball support for the native voter history

## Abstract

Exact finite graph-ball rectangles support the native joint opinion and source history.

Let G be a connected locally finite undirected simple graph on an arbitrary vertex type V, let u be a root, and let N be any natural horizon. The finite enumeration K(G,u,N) is exactly the closed graph ball of radius N. Its construction starts with the singleton root and takes the union of the root with the radius-N balls at its actual neighbours. Shortest walks identify this finite enumeration with the displayed distance ball in the opening proof of Theorem 2.1 of the ancestral-collision source. The countable union of these balls is all of V.

The disjoint label type is the native Label V: an initial vertex or a pair consisting of a strictly positive natural birth time and a vertex. The set L(G,u,N) contains exactly the initial labels on K(G,u,N) and the fresh labels at times 1 through N on that same ball. The coordinate set rectangle(G,u,N) contains every initial opinion on the ball and every fresh opinion, refresh control and actual-neighbour choice at each time 1 through N on the ball. It is the complete rectangular set of the source, including coordinates not reached by a realized history. It includes no auxiliary time-zero coordinate.

RectangleState is the dependent vector of the native Value G c at every coordinate c in that rectangle, with the finite product measurable structure. restrictRectangle x u N w reads that vector from x at w. The native history x u N w records both nvm x s u w and source x s u w for all times s from zero through N. Each choice still takes values in the actual neighbour set of its vertex; a boundary choice may point outside the ball, but the causal recursion only consults it when the preceding time has a remaining distance budget.

**Theorem 1.1 (Exact rectangular support and finite measurable joint reconstruction).**

$$\forall V \in \operatorname{Type},\; \forall O \in \operatorname{Type},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{LocallyFinite}\left(G\right)] \operatorname{Connected}\left(G\right) \Rightarrow \left(\left(\forall v \in V,\; \exists z \in V,\; \operatorname{Adj}\left(G, v, z\right)\right) \Rightarrow \left(\forall u \in V,\; \forall N \in \mathbb{N},\; \left(\forall v \in V,\; v \in \operatorname{K}\left(G, u, N\right) \Leftrightarrow \operatorname{dist}\left(G, u, v\right) \le N\right) \land \left(\operatorname{Countable}\left(V\right) \land \left(\left(\forall v \in V,\; \operatorname{inl}\left(v\right) \in \operatorname{L}\left(G, u, N\right) \Leftrightarrow v \in \operatorname{K}\left(G, u, N\right)\right) \land \left(\left(\forall n \in \operatorname{PNat},\; \forall v \in V,\; \operatorname{inr}\left((n,v)\right) \in \operatorname{L}\left(G, u, N\right) \Leftrightarrow \left(\operatorname{val}\left(n\right) \le N \land v \in \operatorname{K}\left(G, u, N\right)\right)\right) \land \left(\left(\forall c \in \operatorname{Coord}\left(V\right),\; c \in \operatorname{rectangle}\left(G, u, N\right) \Rightarrow \operatorname{positive}\left(c\right)\right) \land \left(\exists f \in \operatorname{RectangleState}\left(G, u, N\right) \to \left(\operatorname{Fin}\left(N+1\right) \to \operatorname{Bool}\times\operatorname{Label}\left(V\right)\right),\; \operatorname{Measurable}\left(f\right) \land \left(\forall x \in (c:\operatorname{Coord}\left(V\right)) \to O \to \operatorname{Value}\left(G, c\right),\; \forall w \in O,\; \operatorname{history}\left(x, u, N, w\right) = f\left(\operatorname{restrictRectangle}\left(x, u, N, w\right)\right) \land \left(\forall s \in \operatorname{Fin}\left(N+1\right),\; \operatorname{source}\left(x, \operatorname{val}\left(s\right), u, w\right) \in \operatorname{L}\left(G, u, N\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/NoisyVoter/RectangularSupport.rectangular_history_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* I. Benjamini, H. Helman Tov and M. Zhukovskii (2023). *Global information from local observations of the noisy voter model on a graph*. DOI: [10.1214/23-AOP1637](https://doi.org/10.1214/23-AOP1637). URL: <https://arxiv.org/abs/2207.01224>.

*Commentary.*

The statement holds for every sample type O, every connected locally finite G, every root and horizon, with a nonempty actual neighbour set at every vertex. Both label membership equivalences are exact; the positive natural type excludes a fresh birth at zero. The displayed decoder f is a single measurable function of the entire rectangular vector, valid for every coordinate assignment and every sample point. Every actual source in the joint history lies in L(G,u,N). The two finite sets are deterministic, and V is countable without a finite-graph hypothesis.

The new induction uses the invariant dist(u,v)+n at most N. It proves that every recursively needed input for (v,n) is in the original rectangle and that its terminal label is in the original label set. The decoder restricts the rectangle to the existing historyInputs vector and directly applies finite_history_factorization from FiniteCausalInputs. No second proof of finite-input reconstruction or of cross-space law transport is introduced.

For Assumption 1.1, encode its initial opinions and strictly positive-time auxiliary coordinates as the native family x, and set N=t+d. Fill the unused time-zero fresh, refresh and choice slots arbitrarily. Every coordinate in the rectangle is initial or has strictly positive time, so the original measurability hypotheses make the rectangle vector measurable; composition with f gives measurable joint opinions and sources. Keep 0 < epsilon < 1 and the original mutual independence and marginal laws for initial and strictly positive-time coordinates: fair initial and fresh opinion coins, noisy refresh controls and uniform choices on actual neighbours. Apply the existing history_law_of_positive_coordinate_laws with that marginal family for cross-space transport. Neither a law nor independence nor measurability is required of the unused time-zero auxiliary slots. A native full-coordinate Model G P is a further application. The support argument itself is pathwise.

The horizon-zero case has K consisting only of u, L consisting only of the initial label at u, and the coordinate rectangle consisting only of the initial opinion at u. For t=0 and positive lag d the horizon is d and the repetition sum is empty. For general t and d every time i and i+d with 1 at most i at most t is within t+d. These readouts use the actual synchronous recursion and keep source equality distinct from colour agreement.

This supplies the exact graph-ball, label-support and finite measurable joint-reconstruction prerequisite in the opening proof of Theorem 2.1. It does not prove the subsequent variance identities, remainder formulas, equality criterion or unordered-pair grouping and multiplicity counting. These identities and counting statements require further arguments.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/NoisyVoter/RectangularSupport.rectangular_history_support`
- Dependency: [D5/S3/StatisticalMechanics/NoisyVoter/FiniteCausalInputs](FiniteCausalInputs.md)
