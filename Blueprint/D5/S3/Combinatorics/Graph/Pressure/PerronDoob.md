# Actual exponential transfer matrix and Doob stationary law

## Abstract

Actual exponential transfer matrix and Doob stationary law

The notation FiniteDecidableType means an arbitrary finite type with decidable equality; RealEdgeCosts(X) means an arbitrary function X -> X -> Real. Let X be finite and let G be a Prop-valued directed support. G.connected connects every ordered vertex pair by an ordinary, possibly empty path, and G.hasEdge supplies an actual edge. This includes every original loopless simple strongly connected graph with an edge; loops are also permitted by this stronger formulation. Costs c are arbitrary real functions. W is exactly exp(-c/temperature) on G.edge and zero elsewhere. No row normalization or aperiodicity is assumed.

**Theorem 1.1 (Actual exponential transfer matrix and Doob stationary law).**

$$\forall X \in \mathrm{FiniteDecidableType},\; \forall G \in \mathrm{Network}\left(X\right),\; \forall c \in \mathrm{RealEdgeCosts}\left(X\right),\; \forall temperature \in \mathrm{Real},\; \mathrm{Nonempty}\left(\mathrm{Perron}\left(G, c, temperature\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Pressure/PerronDoob.exists_perron` (`✓ std3`). ∎

*Citation.* Shmuel Friedland and Stephane Gaubert (2019). *Spectral inequalities for nonnegative tensors and their tropical analogues*. URL: <https://arxiv.org/html/1804.00204v3>.

*Commentary.*

Transport original paths along the exact positive support and use the existing positive-path connectivity lemma. Apply the source-equivalent MCMC supplier to this actual matrix, then transport its real positive eigenvector to the complex matrix. Spectrum membership and the supplier eigenvalue-modulus bound give both inequalities for the extended nonnegative complex spectral radius. Define Qstar as W(i,j)r(j)/(root*r(i)); positivity gives exact original support, and the eigenrelation gives row sum one. Apply the existing finite stationary-distribution supplier to Qstar itself.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Pressure/PerronDoob.exists_perron`
- Dependency: [D5/S3/Combinatorics/Graph/PerronFrobenius/MCMCSupplier/LinearAlgebra/Matrix/PerronFrobenius/Dominance](../PerronFrobenius/MCMCSupplier/LinearAlgebra/Matrix/PerronFrobenius/Dominance.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteStochasticMixing](../../../Observer/ProbabilisticClosure/TrajectoryLaws/FiniteStochasticMixing.md)
