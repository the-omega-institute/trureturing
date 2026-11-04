# Finite causal inputs and joint history laws

## Abstract

Finite positive-time inputs determine the joint native opinion and source history.

Let G be a locally finite simple graph, with an arbitrary vertex type. The input set at time zero and vertex v consists of the initial opinion at v. At time n+1 it consists of the fresh opinion, refresh control and neighbour choice at (n+1,v), together with the input sets at time n of all actual neighbours of v. This is a finite set on finite and infinite graphs. Taking its union over times zero through N gives historyInputs(u,N). No fresh, refresh or choice coordinate at time zero occurs.

The history records both the actual synchronous opinion and its disjoint initial-or-fresh source label at each time. Its opinion coordinate is the original nvm recursion; its label coordinate is the original source recursion. The finite vector restrictInputs retains all input coordinates jointly. To decode it, complete the unspecified coordinates using an arbitrary fixed assignment base and run those same recursions. The resulting history is independent of that completion.

**Theorem 1.1 (Finite reconstruction of the complete joint history).**

$$\forall V \in \operatorname{Type},\; \forall O \in \operatorname{Type},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [G.\operatorname{LocallyFinite}] \forall base \in (c:\operatorname{Coord}\left(V\right)) \to \operatorname{Value}\left(G, c\right),\; \forall u \in V,\; \forall N \in \mathbb{N},\; \left(\forall c \in \operatorname{Coord}\left(V\right),\; c \in \operatorname{historyInputs}\left(u, N\right) \Rightarrow \operatorname{positive}\left(c\right)\right) \land \left(\forall x \in (c:\operatorname{Coord}\left(V\right)) \to O \to \operatorname{Value}\left(G, c\right),\; \forall w \in O,\; \operatorname{history}\left(x, u, N\right)\left(w\right) = \operatorname{decode}\left(base, u, N, \operatorname{restrictInputs}\left(x, u, N\right)\left(w\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/NoisyVoter/FiniteCausalInputs.finite_history_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* I. Benjamini, H. Helman Tov and M. Zhukovskii (2023). *Global information from local observations of the noisy voter model on a graph*. DOI: [10.1214/23-AOP1637](https://doi.org/10.1214/23-AOP1637). URL: <https://arxiv.org/abs/2207.01224>.

*Commentary.*

For every locally finite simple graph, every sample type, every base assignment, root and natural horizon, all inputs are initial or have positive time, and decoding the finite input vector recovers the joint history at every sample point. Agreement propagates through the same refresh decision and the same selected neighbour in the preceding time layer. The statement includes horizon zero and requires no probability, stationarity or independence assumption.

**Theorem 1.2 (The positive-time coordinate law determines the joint history law).**

$$\forall V \in \operatorname{Type},\; \forall O \in \operatorname{Type},\; \forall Oprime \in \operatorname{Type},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [G.\operatorname{LocallyFinite}] [\operatorname{MeasurableSpace}\left(O\right)] [\operatorname{MeasurableSpace}\left(Oprime\right)] \forall P \in \operatorname{Measure}\left(O\right),\; \forall Q \in \operatorname{Measure}\left(Oprime\right),\; \forall x \in (c:\operatorname{Coord}\left(V\right)) \to O \to \operatorname{Value}\left(G, c\right),\; \forall y \in (c:\operatorname{Coord}\left(V\right)) \to Oprime \to \operatorname{Value}\left(G, c\right),\; \forall m \in (c:\{c:\operatorname{Coord}\left(V\right)|\operatorname{positive}\left(c\right)\}) \to \operatorname{Measure}\left(\operatorname{Value}\left(G, \operatorname{val}\left(c\right)\right)\right),\; \left(\forall c \in \operatorname{Coord}\left(V\right),\; \operatorname{positive}\left(c\right) \Rightarrow \operatorname{Measurable}\left(x\left(c\right)\right)\right) \Rightarrow \left(\left(\forall c \in \operatorname{Coord}\left(V\right),\; \operatorname{positive}\left(c\right) \Rightarrow \operatorname{Measurable}\left(y\left(c\right)\right)\right) \Rightarrow \left(\operatorname{iIndepFun}\left((\lambda c:\{c:\operatorname{Coord}\left(V\right)|\operatorname{positive}\left(c\right)\} \mapsto x\left(\operatorname{val}\left(c\right)\right)), P\right) \Rightarrow \left(\operatorname{iIndepFun}\left((\lambda c:\{c:\operatorname{Coord}\left(V\right)|\operatorname{positive}\left(c\right)\} \mapsto y\left(\operatorname{val}\left(c\right)\right)), Q\right) \Rightarrow \left(\left(\forall c \in \{c:\operatorname{Coord}\left(V\right)|\operatorname{positive}\left(c\right)\},\; \operatorname{HasLaw}\left(x\left(\operatorname{val}\left(c\right)\right), m\left(c\right), P\right)\right) \Rightarrow \left(\left(\forall c \in \{c:\operatorname{Coord}\left(V\right)|\operatorname{positive}\left(c\right)\},\; \operatorname{HasLaw}\left(y\left(\operatorname{val}\left(c\right)\right), m\left(c\right), Q\right)\right) \Rightarrow \left(\forall u \in V,\; \forall N \in \mathbb{N},\; \operatorname{map}\left(P, \operatorname{history}\left(x, u, N\right)\right) = \operatorname{map}\left(Q, \operatorname{history}\left(y, u, N\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/NoisyVoter/FiniteCausalInputs.history_law_of_positive_coordinate_laws` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* I. Benjamini, H. Helman Tov and M. Zhukovskii (2023). *Global information from local observations of the noisy voter model on a graph*. DOI: [10.1214/23-AOP1637](https://doi.org/10.1214/23-AOP1637). URL: <https://arxiv.org/abs/2207.01224>.

*Commentary.*

The two coordinate families may live on different measurable spaces with different measures. On each space, require mutual independence of the family indexed by initial and strictly positive-time coordinates, measurability of those coordinates, and the same prescribed marginal laws. Then the complete joint opinion-and-source history laws agree, using the same graph, root and horizon. Neither measurability nor independence nor a marginal law is required for a fresh, refresh or choice coordinate at time zero. The common marginal family is arbitrary and may be specialized to fair opinion coins, noisy refresh controls and uniform choices on the actual neighbour sets.

For repetition observations with lag d at times i and i+d, the horizon N=t+d includes every observation, including the empty repetition sum at t=0. Retaining source labels jointly also retains every equality among sources, rather than identifying sources whenever their opinion colours happen to agree. The result transports the full source partition and does not assert independence of source collisions.

Specializing the marginal family to the original coordinateLaw gives the joint law of the repetition statistic W, the source-collision count C and the multiplicity of each fixed unordered pair of distinct labels. Each is a readout of the joint history through horizon t+d. For arbitrary vertex types, measurability follows by extending the readout from the deterministic finite image of the decoder as a finite sum of measurable singleton indicators; it does not require a globally measurable equality relation on all pairs of labels. The positive-coordinate product realization may fill unused time-zero coordinates arbitrarily and has the same history law as the native full-coordinate product realization.

This finite reconstruction supplies the finite-coordinate determination assertion in the opening paragraph of the proof of Theorem 2.1 in the ancestral-collision source. The recursive input set is used directly; no identification with the displayed graph ball or countability conclusion is asserted. The exact variance decomposition with both the variance of the collision count and the expected squared pair multiplicities, its two remainder identities, and its almost-sure equality criterion require further arguments. Equality of the finite product input laws is obtained from the specified independence and marginals, and the common deterministic decoder then transports it to the joint history.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/NoisyVoter/FiniteCausalInputs.finite_history_factorization`
- Truth anchor: `D5/S3/StatisticalMechanics/NoisyVoter/FiniteCausalInputs.history_law_of_positive_coordinate_laws`
- Dependency: [D5/S3/StatisticalMechanics/NoisyVoter/AncestralSources](AncestralSources.md)
