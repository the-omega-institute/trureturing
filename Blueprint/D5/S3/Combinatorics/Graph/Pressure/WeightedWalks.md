# Unrestricted weighted walks and counting entropy

## Abstract

Unrestricted weighted walks and counting entropy

X ranges over arbitrary finite types with decidable equality; Network X means precisely the original Prop-valued strongly connected support with an actual edge, and RealEdgeCosts X means arbitrary X-to-X real costs. Temperature is any real number in this law. matrixPowerOne(G,c,temperature,n,x) means ((W^n) times the all-ones column)(x). walkGrowthQuotient is n mapped to log(walkSum(G,c,temperature,n,x))/n; countGrowthQuotient is n mapped to log(Nat.card(Walks(G,n,x)))/n. ZeroSupportedCosts means c(i,j)=0 on every actual supported edge. realNatCard casts that exact cardinality to the reals, and complexSpectralRadius is spectralRadius over the complex numbers of the actual adjacency matrix embedded into the complex matrices. Nat includes zero. All walks retain repeated vertices and edges.

Walks n x recursively chooses one actual supported successor at each step. Its zero-length case has one inhabitant. There is no visited-set restriction, so loops, repetitions, returns and periodic cycles are included. walkBoltzmann is the product of exp(-cost/temperature) along the chosen edges. The finite sum is exactly the original matrix power applied to the all-ones column, for every natural n and state x. Zero supported costs make every weight one, yielding Nat.card of this same walk type. The growth limit uses the existing actual Perron vector and actual complex adjacency radius; no aperiodicity or row-normalized reference is introduced.

For a positive temperature tau, let lambda and r be the constructed positive Perron root and right vector of the actual exponential adjacency W. Define Qstar(i,j)=W(i,j)r(j)/(lambda r(i)). The eigenrelation makes each row sum one; Qstar is nonnegative and is positive exactly on the original support. Applying FiniteStochasticMixing.stationary_distribution_exists to this finite row-stochastic matrix gives a stationary probability pi and an attainer (pi,Qstar), without any aperiodicity assumption.

The stationary variational consequence ranges over every graph-supported pair (pi,Q), with pi and Q nonnegative, sum pi=1, every row sum Q=1, and sum_i pi(i)Q(i,j)=pi(j). Set E=sum_ij pi(i)Q(i,j)c(i,j), h=-sum_ij pi(i)Q(i,j)log Q(i,j), and K=sum_i pi(i) KL(Q(i,.) || Qstar(i,.)). Zero entries and zero stationary masses are allowed. A zero Q term contributes zero; a nonzero Q term lies on the graph support and hence has strictly positive Qstar, so its logarithm quotient is legitimate.

Expand log Qstar(i,j)=-c(i,j)/tau+log r(j)-log lambda-log r(i). Multiplying by tau*pi(i)Q(i,j) and summing gives tau*K=E-tau*h+tau*log lambda: the potential sum involving log r(i)-log r(j) vanishes by row normalization and column stationarity, and the total edge mass is one. The existing full-row kl_divergence_nonneg makes K nonnegative, including zero entries and zero stationary masses. At the stationary Doob pair K=0. Consequently the minimum over all these stationary pairs is attained and equals -tau*log lambda. The finite stationary-existence and KL theorems thus give the attained variational identity on the original support.

For every start i and every n including zero, if m and M are positive lower and upper bounds for r, the actual matrix row sum lies between (r(i)/M)*lambda^n and (r(i)/m)*lambda^n. The proof applies the pinned Module.End.HasEigenvector.pow_apply result to Perron.eigen through Matrix.toLin'_pow and Matrix.toLin'_apply, with the positive Perron vector supplying the nonzero eigenvector witness, and uses nonnegative matrix powers. Taking logarithms for n>=1 and squeezing after division by n gives the same growth rate at every start, including periodic supports. At zero supported costs W is the unnormalized counting adjacency. The unrestricted-walk cardinality therefore has entropy log of its actual complex spectral radius.

The cycle comparison combines with these identities to give finite-graph pressure laws for arbitrary real supported costs, all positive temperatures, the stationary minimum with zeros, every unrestricted walk length and starting vertex, counting entropy, the constructed minimum directed-cycle mean and maximum outdegree bracket, and the right-hand zero-temperature limit.

**Theorem 1.1 (Unrestricted weighted walks and counting entropy).**

$$\forall X \in \mathrm{FiniteDecidableType},\; \forall G \in \mathrm{Network}\left(X\right),\; \forall c \in \mathrm{RealEdgeCosts}\left(X\right),\; \forall temperature \in \mathrm{Real},\; \left(\forall n \in \mathrm{Nat},\; \forall x \in X,\; \mathrm{walkSum}\left(G, c, temperature, n, x\right) = \mathrm{matrixPowerOne}\left(G, c, temperature, n, x\right)\right) \land \left(\left(\forall x \in X,\; \mathrm{Tendsto}\left(\mathrm{walkGrowthQuotient}\left(G, c, temperature, x\right), \mathrm{atTop}, \mathrm{nhds}\left(\mathrm{log}\left(\mathrm{root}\left(\mathrm{perron}\left(G, c, temperature\right)\right)\right)\right)\right)\right) \land \left(\left(\mathrm{ZeroSupportedCosts}\left(G, c\right) \Rightarrow \left(\forall n \in \mathrm{Nat},\; \forall x \in X,\; \mathrm{walkSum}\left(G, c, temperature, n, x\right) = \mathrm{realNatCard}\left(\mathrm{Walks}\left(G, n, x\right)\right)\right)\right) \land \left(\forall x \in X,\; \mathrm{Tendsto}\left(\mathrm{countGrowthQuotient}\left(G, x\right), \mathrm{atTop}, \mathrm{nhds}\left(\mathrm{log}\left(\mathrm{toReal}\left(\mathrm{complexSpectralRadius}\left(\mathrm{adjacency}\left(G\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Pressure/WeightedWalks.unrestricted_walk_laws` (`✓ std3`). ∎

*Citation.* Shmuel Friedland and Stephane Gaubert (2019). *Spectral inequalities for nonnegative tensors and their tropical analogues*. URL: <https://arxiv.org/html/1804.00204v3>.

*Commentary.*

Partition the successor-walk sigma type by its first actual successor and distribute the finite weighted sums. Induction on n identifies the result with W^n times the all-ones column. Apply the existing periodic growth theorem to this equality. For zero costs, induction makes each Boltzmann product one and the sum is the cardinality; apply the existing zero-cost actual adjacency spectral-radius identity.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Pressure/WeightedWalks.unrestricted_walk_laws`
- Dependency: [D5/S3/Combinatorics/Graph/PerronFrobenius/MCMCSupplier/LinearAlgebra/Matrix/PerronFrobenius/Dominance](../PerronFrobenius/MCMCSupplier/LinearAlgebra/Matrix/PerronFrobenius/Dominance.md)
