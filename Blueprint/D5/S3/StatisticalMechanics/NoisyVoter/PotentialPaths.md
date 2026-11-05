# Unstopped potential copy paths

## Abstract

Unstopped potential copy paths identify native survival, the first fresh source and the original-law variance chain.

Let G be a simple graph on an arbitrary vertex type V and x a native coordinate assignment on a sample type O. The choice at v belongs to the actual neighbour set of v. Set Z(n,u,z,0)=u and Z(n,u,z,k+1)=J(n-k,Z(n,u,z,k)). The potential path never tests a refresh to decide whether to continue. Only its offsets zero through d are used when n=i+d. Define A(x,i,d,u,z) independently as: for every k<d, R(i+d-k,Z(i+d,u,z,k)) is false. Its inspected times range from i+d down to i+1; the refresh at its time-i endpoint is excluded.

**Theorem 1.1 (The complete native potential-path correspondence).**

$$\forall V \in \operatorname{Type},\; \forall O \in \operatorname{Type},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall x \in \operatorname{Coordinates}\left(G, O\right),\; \forall i \in \mathbb{N},\; \forall d \in \mathbb{N},\; \forall u \in V,\; \forall z \in O,\; \operatorname{Z}\left(i+d, u, z, 0\right) = u \land \left(\left(\forall k \in \mathbb{N},\; k < d \Rightarrow \operatorname{Z}\left(i+d, u, z, k+1\right) = \operatorname{J}\left(i+d-k, \operatorname{Z}\left(i+d, u, z, k\right)\right)\right) \land \left(\left(\operatorname{A}\left(x, i, d, u, z\right) \Leftrightarrow \operatorname{survives}\left(x, i, d, u, z\right) = \operatorname{true}\right) \land \left(\left(\operatorname{A}\left(x, i, d, u, z\right) \Leftrightarrow \operatorname{birth}\left(\operatorname{S}\left(i+d, u, z\right)\right) \le i\right) \land \left(\left(\operatorname{A}\left(x, i, d, u, z\right) \Rightarrow \operatorname{S}\left(i+d, u, z\right) = \operatorname{S}\left(i, \operatorname{Z}\left(i+d, u, z, d\right), z\right)\right) \land \left(\left(\forall k \in \mathbb{N},\; k < d \Rightarrow \left(\operatorname{EarlierFalse}\left(k\right) \Rightarrow \left(\operatorname{R}\left(i+d-k, \operatorname{Z}\left(i+d, u, z, k\right)\right) = \operatorname{true} \Rightarrow \left(\operatorname{S}\left(i+d, u, z\right) = \operatorname{freshLabel}\left(i+d-k, \operatorname{Z}\left(i+d, u, z, k\right)\right) \land i < \operatorname{birth}\left(\operatorname{S}\left(i+d, u, z\right)\right)\right)\right)\right)\right) \land \left(\left(\left(\neg \operatorname{A}\left(x, i, d, u, z\right)\right) \Rightarrow \left(\exists k \in \mathbb{N},\; k < d \land \left(\operatorname{EarlierFalse}\left(k\right) \land \operatorname{R}\left(i+d-k, \operatorname{Z}\left(i+d, u, z, k\right)\right) = \operatorname{true}\right)\right)\right) \land \left(\operatorname{S}\left(i, u, z\right) = \operatorname{S}\left(i+d, u, z\right) \Rightarrow \operatorname{A}\left(x, i, d, u, z\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/NoisyVoter/PotentialPaths.potential_path_source_correspondence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* I. Benjamini, H. Helman Tov and M. Zhukovskii (2023). *Global information from local observations of the noisy voter model on a graph*. DOI: [10.1214/23-AOP1637](https://doi.org/10.1214/23-AOP1637). URL: <https://arxiv.org/abs/2207.01224>.

*Commentary.*

All i,d are natural, all u are vertices and z is any sample. No probability, cardinality, stationarity or terminal-correctness premise is used. The freshLabel(n,v) in the formula is the disjoint positive-time fresh label; k<d proves its positive birth time. EarlierFalse(k) means every j<k has R(i+d-j,Z_j)=false. A first refresh exists whenever A fails, including offsets zero and d-1. The path continues after that refresh, while the native source stops there. Source collision implies A; the converse is not asserted.

For the probability statement, OriginalLaw(G,P,epsilon,x) abbreviates the following explicit hypotheses: G is connected and locally finite, every actual neighbour set is nonempty, P is a probability measure on an arbitrary measurable sample space O, zero<epsilon<one, and the family indexed by initial coordinates and strictly positive-time fresh, refresh and choice coordinates is measurable and mutually independent with the native coordinateLaw marginals. Initial and fresh opinions are independent fair Bernoulli coins, refresh controls have Bernoulli(epsilon) law, and choices are uniform on the actual finite neighbour sets. No measurability, marginal law or independence is required of any fresh, refresh or choice slot at time zero. Native opinions X and disjoint sources S retain their original synchronous recursions.

**Theorem 1.2 (Probability and variance on the original positive-time law).**

$$\forall V \in \operatorname{Type},\; \forall O \in \operatorname{Type},\; \forall m \in \operatorname{MeasurableSpace}\left(O\right),\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall P \in \operatorname{Measure}\left(O\right),\; \forall epsilon \in \operatorname{UnitInterval},\; \forall x \in \operatorname{Coordinates}\left(G, O\right),\; \operatorname{OriginalLaw}\left(G, P, epsilon, x\right) \Rightarrow \left(\forall u \in V,\; \forall d \in \mathbb{N},\; \forall t \in \mathbb{N},\; \left(\forall i \in \mathbb{N},\; \operatorname{MeasurableSet}\left(\operatorname{Aevent}\left(i\right)\right) \land \left(\operatorname{P}\left(\operatorname{Aevent}\left(i\right)\right) = q^{d} \land \left(\operatorname{subset}\left(\operatorname{E}\left(i\right), \operatorname{Aevent}\left(i\right)\right) \land \left(\operatorname{P}\left(\operatorname{E}\left(i\right)\right) \le q^{d} \land 1-q^{d} \le \operatorname{P}\left(\operatorname{N}\left(i\right)\right)\right)\right)\right)\right) \land \left(\frac{1}{4}\times\operatorname{sumNoncollision}\left(P, x, u, d, t\right) \le \operatorname{Var}\left(\operatorname{W}\left(x, u, d, t\right), P\right) \land \frac{t\times{1-q^{d}}}{4} \le \frac{1}{4}\times\operatorname{sumNoncollision}\left(P, x, u, d, t\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/NoisyVoter/PotentialPaths.original_potential_path_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* I. Benjamini, H. Helman Tov and M. Zhukovskii (2023). *Global information from local observations of the noisy voter model on a graph*. DOI: [10.1214/23-AOP1637](https://doi.org/10.1214/23-AOP1637). URL: <https://arxiv.org/abs/2207.01224>.

*Commentary.*

The formula uses Aevent(i)={z:A(x,i,d,u,z)}, q=1-epsilon, E(i)=E_i={z:S_i(u,z)=S_(i+d)(u,z)}, N(i)=N_i its complement, and sumNoncollision=sum over i=1 through t of P(N_i). W is exactly the native sum of opinion-equality indicators over the same observation pairs. Every natural d,t is admitted, hence in particular every positive lag and t=0. The observation horizon is t+d. Probabilities are on the original P throughout.

For the proof, construct the full-coordinate comparison product Q using the same graph, noise and actual neighbour marginals. The full Model assumptions hold only on Q. Restrict its coordinates and the original x to the positive-coordinate subtype, and apply history_law_of_positive_coordinate_laws at the same root and horizon. The joint opinion-and-source history laws agree. Connectivity and local finiteness give countability through the original vertices_countable supplier; finite histories therefore admit measurable scalar and event readouts. The original history is measurable by finite_history_factorization and the original decode_measurable supplier. Transfer the source-birth event to obtain P(A)=q^d from survival_probability. Transfer each collision event and the actual W variance, then apply native_variance_lower on Q. The complement identity and a finite sum give the second inequality. Time-zero auxiliary slots of x are never included in these laws or measurability hypotheses.

When t=0 the sum and W are zero. At d=0 the potential-path event is the empty conjunction; this extra boundary does not replace the positive-lag statement. The path construction and its prefix-source induction are the mathematical content; existing native source, survival, probability and variance results are reused. The raw control-field conditional laws, character-moment variance identity, equality criterion, K2 optimality and improved coefficients are outside these two statements.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/NoisyVoter/PotentialPaths.original_potential_path_bounds`
- Truth anchor: `D5/S3/StatisticalMechanics/NoisyVoter/PotentialPaths.potential_path_source_correspondence`
- Dependency: [D5/S3/StatisticalMechanics/NoisyVoter/RectangularSupport](RectangularSupport.md)
