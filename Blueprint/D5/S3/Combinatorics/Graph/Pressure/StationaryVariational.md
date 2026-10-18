# Stationary pressure with zero masses and zero probabilities

## Abstract

Stationary pressure with zero masses and zero probabilities

X is an arbitrary finite type with decidable equality. G is strongly connected Prop-valued edge support with an actual edge; costs are arbitrary real functions and temperature is positive. A StationaryPair contains nonnegative normalized pi, a nonnegative row-stochastic Q supported on the original G.edge, and the exact column balance pi Q = pi. Both pi and Q may have zero entries. Entropy is minus the full finite sum pi(i)Q(i,j)log Q(i,j), with zero products contributing zero. The objective is the actual mean c minus temperature times this entropy.

**Theorem 1.1 (Stationary pressure with zero masses and zero probabilities).**

$$\forall X \in \mathrm{FiniteDecidableType},\; \forall G \in \mathrm{Network}\left(X\right),\; \forall c \in \mathrm{RealEdgeCosts}\left(X\right),\; \forall temperature \in \mathrm{Real},\; 0 < temperature \Rightarrow \left(\exists p \in \mathrm{StationaryPair}\left(G\right),\; \mathrm{Q}\left(p\right) = \mathrm{Qstar}\left(G, c, temperature\right) \land \left(\mathrm{objective}\left(p, c, temperature\right) = \mathrm{neg}\left(temperature \cdot \mathrm{log}\left(\mathrm{root}\left(\mathrm{perron}\left(G, c, temperature\right)\right)\right)\right) \land \left(\forall q \in \mathrm{StationaryPair}\left(G\right),\; \mathrm{neg}\left(temperature \cdot \mathrm{log}\left(\mathrm{root}\left(\mathrm{perron}\left(G, c, temperature\right)\right)\right)\right) \le \mathrm{objective}\left(q, c, temperature\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Pressure/StationaryVariational.variational_minimum` (`✓ std3`). ∎

*Citation.* Shmuel Friedland and Stephane Gaubert (2019). *Spectral inequalities for nonnegative tensors and their tropical analogues*. URL: <https://arxiv.org/html/1804.00204v3>.

*Commentary.*

On a nonzero Q entry, support gives a positive Qstar entry and permits expanding log Qstar = -c/temperature + log r(j) - log r(i) - log root. At a zero Q entry the weighted term is exactly zero. Row normalization and column stationarity cancel the arbitrary potential log r. The exact identity is temperature*weightedKL = objective + temperature*log root for every StationaryPair. Apply GrandmotherTheorem.kl_divergence_nonneg directly to full rows, with absolute continuity supplied by graph support. At an actual stationary law of Qstar, every row KL is zero. Hence the minimum is attained on the same actual W.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Pressure/StationaryVariational.variational_minimum`
- Dependency: [D5/S3/Combinatorics/Graph/Pressure/PerronDoob](PerronDoob.md)
- Dependency: [D5/S3/Divergence/GrandmotherTheorem](../../../Divergence/GrandmotherTheorem.md)
