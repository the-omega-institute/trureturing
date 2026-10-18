# Periodic-safe every-state transfer growth

## Abstract

Periodic-safe every-state transfer growth

X is an arbitrary finite type with decidable equality. G is strongly connected Prop-valued edge support with an actual edge; costs are arbitrary real functions and temperature is real. The abbreviation growthQuotient denotes n mapped to log((W^n times the all-ones column)(i))/n. The observable is (W^n times the all-ones column)(i), for every starting state i and n. It sums over terminal states. The proof does not replace it by a fixed-terminal matrix entry and does not assume primitive convergence. If m and M bound the actual positive right eigenvector, the exact factors are r(i)/M below and r(i)/m above, multiplied by root^n.

**Theorem 1.1 (Periodic-safe every-state transfer growth).**

$$\forall X \in \mathrm{FiniteDecidableType},\; \forall G \in \mathrm{Network}\left(X\right),\; \forall c \in \mathrm{RealEdgeCosts}\left(X\right),\; \forall temperature \in \mathrm{Real},\; \forall i \in X,\; \mathrm{Tendsto}\left(\mathrm{growthQuotient}\left(G, c, temperature, i\right), \mathrm{atTop}, \mathrm{nhds}\left(\mathrm{log}\left(\mathrm{root}\left(\mathrm{perron}\left(G, c, temperature\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Pressure/PeriodicGrowth.weighted_growth` (`✓ std3`). ∎

*Citation.* Shmuel Friedland and Stephane Gaubert (2019). *Spectral inequalities for nonnegative tensors and their tropical analogues*. URL: <https://arxiv.org/html/1804.00204v3>.

*Commentary.*

Inductively transport the actual eigenrelation through each matrix power. Nonnegativity compares the weighted row sums against m and M. Both constant multiples are positive, so logarithms and division by n for n at least one give a squeeze around log root. Finite extrema supply m>0 and M>0, and the additive constants divided by n tend to zero. At zero supported costs W is the actual counting adjacency, and the complex spectral-radius equality gives its logarithmic growth. An explicit bijection to a finite type of unrestricted directed walks is not yet delivered. The original minimum-cycle-mean, maximum-outdegree bracket, and zero-temperature limit remain unpaid; none is inferred from these components.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Pressure/PeriodicGrowth.weighted_growth`
- Dependency: [D5/S3/Combinatorics/Graph/Pressure/PerronDoob](PerronDoob.md)
