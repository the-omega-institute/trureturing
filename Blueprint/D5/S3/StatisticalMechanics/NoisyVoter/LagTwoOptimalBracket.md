# The lag-two optimal-constant bracket

## Abstract

The original synchronous law gives a ratio-less-than-two bracket and linear small-noise order.

The graph class consists of all connected locally finite simple graphs on an arbitrary vertex type, finite or infinite, with a nonempty finite neighbour set at every vertex. The probability space is arbitrary. OriginalLaw requires a probability measure and measurability, mutual independence and the prescribed coordinateLaw marginals only for initial slots and strictly positive-time fresh, refresh and choice slots. Initial and fresh opinions are fair independent bits, refresh controls have parameter epsilon, and each choice is uniform on its actual neighbour set. No condition is imposed on auxiliary slots at time zero. X is the original synchronous recursion; W(x,u,2,t) sums the equalities X(i,u)=X(i+2,u) for i from one through t.

**Definition 1.1 (The full variance-value infimum).**

$$\forall epsilon \in \mathbb{R},\; \operatorname{copt}\left(epsilon\right) = \operatorname{inf}\left(\operatorname{Values}\left(epsilon\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/NoisyVoter/LagTwoOptimalBracket.cOpt` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* I. Benjamini, H. Helman Tov and M. Zhukovskii (2023). *Global information from local observations of the noisy voter model on a graph*. DOI: [10.1214/23-AOP1637](https://doi.org/10.1214/23-AOP1637). URL: <https://arxiv.org/abs/2207.01224>.

*Commentary.*

Values(epsilon) consists exactly of Var(W(x,u,2,t);P)/t, quantified over arbitrary vertex and sample types, the graph class above, every measurable probability-space realization of OriginalLaw, every vertex u and every natural t at least one. Its definition retains the original P and coordinate assignment. A unit-interval parameter e with real value epsilon carries the marginal laws; it introduces no additional restriction on zero<epsilon<one. Outside the unit interval this class is empty; all bounds concern the stated open interval. The infimum does not assert attainment.

**Theorem 1.2 (The complete bracket and native two-vertex law).**

$$\forall epsilon \in \operatorname{UnitInterval},\; \left(0 < epsilon \land epsilon < 1\right) \Rightarrow \left(\left(\frac{1-(1-epsilon)^{2}}{4} \le \operatorname{copt}\left(epsilon\right) \land \left(\operatorname{copt}\left(epsilon\right) \le \frac{1-(1-epsilon)^{4}}{4} \land \left(\frac{1-(1-epsilon)^{4}}{1-(1-epsilon)^{2}} = 1+(1-epsilon)^{2} \land \left(1+(1-epsilon)^{2} < 2 \land \left(\frac{2\times epsilon-epsilon^{2}}{4} \le \operatorname{copt}\left(epsilon\right) \land \left(\operatorname{copt}\left(epsilon\right) \le \frac{4\times epsilon-6\times epsilon^{2}+4\times epsilon^{3}-epsilon^{4}}{4} \land \left(\frac{epsilon}{4} \le \operatorname{copt}\left(epsilon\right) \land \operatorname{copt}\left(epsilon\right) \le epsilon\right)\right)\right)\right)\right)\right)\right) \land \left(\left(\operatorname{ThetaRightZero}\left(\operatorname{copt}, \operatorname{identity}\right) \land \left(\frac{1}{2} \le \operatorname{liminfRightZero}\left(\operatorname{normalizedCopt}\right) \land \left(\operatorname{liminfRightZero}\left(\operatorname{normalizedCopt}\right) \le \operatorname{limsupRightZero}\left(\operatorname{normalizedCopt}\right) \land \operatorname{limsupRightZero}\left(\operatorname{normalizedCopt}\right) \le 1\right)\right)\right) \land \left(\forall O \in \operatorname{Type},\; \forall m \in \operatorname{MeasurableSpace}\left(O\right),\; \forall P \in \operatorname{Measure}\left(O, m\right),\; \forall x \in \operatorname{Coordinates}\left(\operatorname{Ktwo}, O\right),\; \operatorname{OriginalLaw}\left(\operatorname{Ktwo}, P, epsilon, x\right) \Rightarrow \left(\forall u \in \operatorname{Bool},\; \left(\forall n \in \mathbb{N},\; \forall z \in \operatorname{Bits}\left(n+2\right),\; \forall b \in \operatorname{Bool},\; 0 < \operatorname{P}\left(\operatorname{History}\left(x, u, n, z\right)\right) \Rightarrow \frac{\operatorname{P}\left(\operatorname{HistoryNext}\left(x, u, n, z, b\right)\right)}{\operatorname{P}\left(\operatorname{History}\left(x, u, n, z\right)\right)} = \frac{1-(1-epsilon)^{2}}{2}+(1-epsilon)^{2}\times \operatorname{Indicate}\left(b = \operatorname{Entry}\left(z, n\right)\right)\right) \land \left(\left(\forall N \in \mathbb{N},\; \operatorname{HasLaw}\left(\operatorname{Y}\left(x, u, N\right), \operatorname{ProductLaw}\left(epsilon, N\right), P\right)\right) \land \left(\forall t \in \mathbb{N},\; \operatorname{HasLaw}\left(\operatorname{W}\left(x, u, 2, t\right), \operatorname{CastBinomial}\left(t, \frac{1+(1-epsilon)^{2}}{2}\right), P\right) \land \operatorname{Var}\left(\operatorname{W}\left(x, u, 2, t\right), P\right) = \frac{t\times (1-(1-epsilon)^{4})}{4}\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/NoisyVoter/LagTwoOptimalBracket.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* I. Benjamini, H. Helman Tov and M. Zhukovskii (2023). *Global information from local observations of the noisy voter model on a graph*. DOI: [10.1214/23-AOP1637](https://doi.org/10.1214/23-AOP1637). URL: <https://arxiv.org/abs/2207.01224>.

*Commentary.*

Here q(epsilon)=1-epsilon, p(epsilon)=(1+q(epsilon)^2)/2 and normalizedCopt(e)=copt(e)/e. ThetaRightZero means two-sided Big-O on the real right-neighbourhood filter at zero; liminfRightZero and limsupRightZero use exactly that filter. The displayed inequalities include the bracket, exact endpoint ratio, both expanded endpoint polynomials, the uniform epsilon/4 and epsilon bounds, and all three lower/upper-limit comparisons.

Ktwo is the complete simple graph on Bool. For any original realization on this graph, bits(x,u,n+1) is the actual centre history Z(0),...,Z(n+1), where Z(k)=X(k,u). History(x,u,n,z) is its equality event with the specified binary string z, and HistoryNext additionally requires Z(n+2)=b. Entry(z,n) is the bit two time steps before that next bit. The ratio of the two real probabilities is the conditional probability on each positive-probability history. Indicate is one when its proposition holds and zero otherwise.

For each natural N, Y(x,u,N) is the actual vector (Z(0),Z(1),E(2),...,E(N+1)), with E(k) indicating Z(k)=Z(k-2). ProductLaw(epsilon,N) is the product of independent Bernoulli laws, fair at indices zero and one and with parameter p(epsilon) at every later index. Thus N=0 gives independent fair Z(0),Z(1), and N=M-1 gives the full joint law through every horizon M at least two, including independence of all agreement bits from both initial bits. These variables are read from the original recursion on P. CastBinomial(t,p) is the pushforward of the natural-valued Binomial(t,p) law by the real cast.

The variance and Binomial assertions use the actual W: its i-th summand is E(i+2), so the selected agreement coordinates are E(3),...,E(t+2). Every natural t is included. At t=0 the empty sum has the point-mass-at-zero Binomial law and zero variance.

The lower endpoint applies original_potential_path_bounds with lag two to each member of Values. For the upper endpoint, on Ktwo each actual neighbour is the other endpoint. Expanding two synchronous updates gives Z(n+2)=F(n+2,u) if the centre refreshes, F(n+1,other) if only the intermediate leaf refreshes, and Z(n) otherwise. These four refresh/fresh coordinates lie outside the causal inputs of the entire preceding centre history. Their native independent laws give the conditional kernel (1-q^2)/2+q^2 Indicate(b=Z(n)). The initial pair uses I(u) and the independent block consisting of R(1,u), F(1,u), I(other), giving its fair product law. Induction on the horizon appends one independent Bernoulli agreement to the actual innovation vector. Selecting the coordinates used by W gives its Binomial law and variance t p(1-p)=t(1-q^4)/4.

The Ktwo law is the specialization of the star-centre transition in Benjamini, Helman Tov and Zhukovskii, Theorem 6.1 proof, Section 6, pages 28-29; the finite-horizon relation above is established directly from the synchronous coordinates. The existing lower bound and pinned product-measure, independence, Bernoulli and Binomial results supply the remaining probability interfaces. Factorization yields the exact ratio; polynomial expansion yields the endpoint formulas; division by positive epsilon gives the uniform order and right-sided limit bounds. No exact value of the infimum, attainment, minimizing graph, or existence of the normalized limit is asserted.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/NoisyVoter/LagTwoOptimalBracket.cOpt`
- Truth anchor: `D5/S3/StatisticalMechanics/NoisyVoter/LagTwoOptimalBracket.result`
- Dependency: [D5/S3/StatisticalMechanics/NoisyVoter/PotentialPaths](PotentialPaths.md)
