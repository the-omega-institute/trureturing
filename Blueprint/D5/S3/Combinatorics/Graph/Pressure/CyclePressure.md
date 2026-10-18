# Minimum directed-cycle mean and zero-temperature pressure

## Abstract

Minimum directed-cycle mean and zero-temperature pressure

X ranges over arbitrary finite types with decidable equality; Network X means precisely the original Prop-valued strongly connected support with an actual edge, and RealEdgeCosts X means arbitrary X-to-X real costs. SupportClosedWalk(G,x) is the actual supportGraph.Walk x x; IsSimpleCycle uses the existing cycle predicate. minimumCycleMean is the mean of the constructed attaining simple cycle, and maxOutdegree is the attained maximum cardinality of actual successor subtypes. realNat casts this degree to the reals. pressureFunction(G,c) is temperature mapped to minus temperature times log of the constructed actual Perron root. nhdsRight(0) denotes the right-hand neighborhood filter at zero. No PF data, chosen cycle, potential, or pressure bracket occurs as a supplied premise.

SupportEdge is precisely the subtype of ordered pairs satisfying the original Prop-valued support. supportGraph uses their original source and target. Strong connectivity and an actual edge supply a nonempty closed walk. The existing simple-cycle reduction supplies a simple cycle. Its existing length bound makes the set of actual mean costs finite. minimumCycle chooses a minimizing actual cycle from that nonempty finite set. outdegree counts the actual successor subtype, and maxOutdegree is the maximum of these cardinalities. The result includes an attaining cycle, minimality against all nonempty closed walks including repetitions, an attaining maximum degree, the exact temperature bracket and the right-hand zero-temperature limit.

**Theorem 1.1 (Minimum directed-cycle mean and zero-temperature pressure).**

$$\forall X \in \mathrm{FiniteDecidableType},\; \forall G \in \mathrm{Network}\left(X\right),\; \forall c \in \mathrm{RealEdgeCosts}\left(X\right),\; \left(\exists x \in X,\; \exists w \in \mathrm{SupportClosedWalk}\left(G, x\right),\; \mathrm{IsSimpleCycle}\left(w\right) \land \mathrm{cycleMean}\left(G, c, w\right) = \mathrm{minimumCycleMean}\left(G, c\right)\right) \land \left(\left(\forall x \in X,\; \forall w \in \mathrm{SupportClosedWalk}\left(G, x\right),\; 0 < \mathrm{length}\left(w\right) \Rightarrow \mathrm{minimumCycleMean}\left(G, c\right) \le \mathrm{cycleMean}\left(G, c, w\right)\right) \land \left(\left(\left(\exists x \in X,\; \mathrm{outdegree}\left(G, x\right) = \mathrm{maxOutdegree}\left(G\right)\right) \land 1 \le \mathrm{maxOutdegree}\left(G\right)\right) \land \left(\left(\forall temperature \in \mathrm{Real},\; 0 < temperature \Rightarrow \left(\mathrm{minimumCycleMean}\left(G, c\right) - temperature \cdot \mathrm{log}\left(\mathrm{realNat}\left(\mathrm{maxOutdegree}\left(G\right)\right)\right) \le \mathrm{neg}\left(temperature \cdot \mathrm{log}\left(\mathrm{root}\left(\mathrm{perron}\left(G, c, temperature\right)\right)\right)\right) \land \mathrm{neg}\left(temperature \cdot \mathrm{log}\left(\mathrm{root}\left(\mathrm{perron}\left(G, c, temperature\right)\right)\right)\right) \le \mathrm{minimumCycleMean}\left(G, c\right)\right)\right) \land \mathrm{Tendsto}\left(\mathrm{pressureFunction}\left(G, c\right), \mathrm{nhdsRight}\left(0\right), \mathrm{nhds}\left(\mathrm{minimumCycleMean}\left(G, c\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Pressure/CyclePressure.cycle_pressure_laws` (`✓ std3`). ∎

*Citation.* Shmuel Friedland and Stephane Gaubert (2019). *Spectral inequalities for nonnegative tensors and their tropical analogues*. URL: <https://arxiv.org/html/1804.00204v3>.

*Commentary.*

Use the existing cycle reduction and one-sided potential suppliers directly, with weight=-cost and level=-minimumCycleMean. The resulting potential satisfies -cost+phi(source)-phi(target)<=-minimumCycleMean. For each positive temperature use z=exp(-phi/temperature). Each actual supported matrix term satisfies W(i,j)z(j)<=exp(-minimum/temperature)z(i); summation counts actual successors. At a vertex maximizing the actual positive Perron-vector ratio r/z, its eigenrelation gives the upper Perron bound with the actual maximum outdegree. Multiply Perron row inequalities along the actual minimizing cycle; its positive right-vector factor cancels because the walk is closed, giving the lower bound. Real logarithms give minimum-temperature*log(maximumDegree)<=-temperature*log(root)<=minimum. The squeeze yields the right-hand zero-temperature limit. The construction uses the same original graph, costs, matrix and actual Perron vector throughout.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Pressure/CyclePressure.cycle_pressure_laws`
- Dependency: [D5/S3/Combinatorics/Graph/LayeredCirculation/PositiveCircuitSupplier](../LayeredCirculation/PositiveCircuitSupplier.md)
- Dependency: [D5/S3/Combinatorics/Graph/Pressure/WeightedWalks](WeightedWalks.md)
