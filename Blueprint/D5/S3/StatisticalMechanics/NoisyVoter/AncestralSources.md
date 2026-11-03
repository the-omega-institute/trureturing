# Ancestral collisions and repetition variance

## Abstract

Actual ancestral sources give a degree-independent native repetition variance bound.

Initial opinions and positive-time fresh opinions have disjoint labels. A fresh label records its positive natural birth time and vertex. At time zero the source is the initial coordinate. A refresh selects the corresponding fresh coordinate. A copy follows the actual chosen neighbour into the preceding time layer.

**Theorem 1.1 (Reconstruction of the actual opinion).**

$$\forall V \in \operatorname{Type},\; \forall O \in \operatorname{Type},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall x \in (c:\operatorname{Coord}\left(V\right)) \to O \to \operatorname{Value}\left(G, c\right),\; \forall n \in \mathbb{N},\; \forall v \in V,\; \forall w \in O,\; \operatorname{nvm}\left(x, n, v, w\right) = \operatorname{coin}\left(x, \operatorname{source}\left(x, n, v, w\right), w\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/NoisyVoter/AncestralSources.native_source` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* I. Benjamini, H. Helman Tov and M. Zhukovskii (2023). *Global information from local observations of the noisy voter model on a graph*. DOI: [10.1214/23-AOP1637](https://doi.org/10.1214/23-AOP1637). URL: <https://arxiv.org/abs/2207.01224>.

*Commentary.*

For every coordinate assignment, vertex, natural time and sample point, the native opinion equals the coin at its source label. The identity is pathwise and includes time zero.

**Theorem 1.2 (The degree-independent finite-time lower bound).**

$$\forall V \in \operatorname{Type},\; \forall O \in \operatorname{Type},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [G.\operatorname{LocallyFinite}] [\operatorname{MeasurableSpace}\left(O\right)] \forall P \in \operatorname{Measure}\left(O\right),\; \forall M \in \operatorname{Model}\left(G, P\right),\; \forall u \in V,\; \forall d \in \mathbb{N},\; \forall t \in \mathbb{N},\; \frac{(t:\mathbb{R})}{4} \cdot \left(1 - (1 - (M.\varepsilon:\mathbb{R}))^{d}\right) \le \operatorname{variance}\left(\operatorname{W}\left(M.\operatorname{coordinate}, u, d, t\right), P\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/NoisyVoter/AncestralSources.uniform_variance_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* I. Benjamini, H. Helman Tov and M. Zhukovskii (2023). *Global information from local observations of the noisy voter model on a graph*. DOI: [10.1214/23-AOP1637](https://doi.org/10.1214/23-AOP1637). URL: <https://arxiv.org/abs/2207.01224>.

*Commentary.*

For every instance of the existing native Model, Var(W_t) is at least t(1-(1-epsilon)^d)/4 for every vertex and natural d,t. This includes finite and infinite connected locally finite graphs and uses that model's original probability space and joint coordinate law. The empty time sum and lag zero give a zero lower bound. At lag two the expression is the lower endpoint required by the source Theorem 3.2.

The proof uses deterministic finite source support to establish measurability. The complete source field is independent of the labelled fair opinion coins. Consequently, a two-opinion sign moment is its source-collision probability, and a four-opinion sign moment is the probability of an even pairing of its four sources. The pairing events form a union and can overlap; their probabilities are not added.

Comparing the sign-product covariance with the covariance of the source-collision indicators leaves nonnegative off-diagonal contributions and an unequal-source probability on the diagonal. The variance of the collision-indicator sum is nonnegative. A collision across lag d requires survival without refresh through those d layers, whose probability is (1-epsilon)^d under the actual joint law.

Application to the original positive-time law. Keep the same connected locally finite simple graph G, root u, noise epsilon, lag d at least one, horizon N=t+d and probability space (O,P). Set x(initial v)=I_v and, for n at least one, x(fresh n v)=F_(n,v), x(refresh n v)=R_(n,v) and x(choice n v)=J_(n,v). A choice takes values in the subtype of actual neighbours of its vertex, with the original uniform law. Fill unused auxiliary slots at time zero with deterministic constants, selecting an actual neighbour for a choice slot. This completes a function assignment without adding random input. It does not make x a full-coordinate Model on P. The initial opinions remain independent fair coins; no stationary law is substituted.

Let Q be Measure.infinitePi of coordinateLaw on the full Coord V family, with coordinate evaluations y. The existing probability instance, measurePreserving_eval_infinitePi and iIndepFun_infinitePi supply a full-coordinate Model on Q with the same G, epsilon and nonempty neighbour sets. Restrict x and y to the subtype FiniteCausalInputs.positive. Independence restricts by iIndepFun.precomp along its injective inclusion, and the positive marginal laws agree. Apply history_law_of_positive_coordinate_laws to P,x and Q,y at the same u,N. The JOINT opinion-and-source history laws agree. Only the separate comparison space Q is assigned the full-coordinate Model assumptions.

RectangularSupport.rectangular_history_support supplies the deterministic finite label set L(G,u,N). Define W_t as the sum over 1 through t of the opinion-equality indicators, C_t as the sum of the source-equality indicators, and m_e as the number of unequal source pairs equal to a fixed unordered two-element set e. All are readouts of that joint history. Their compositions with the rectangle decoder have finite domains, since both the rectangle and every coordinate value type are finite, and hence are measurable. Label events on its finite image are finite unions of measurable singleton events. Thus W_t, C_t, m_e, their products, squares and finite sums are measurable and bounded on both P and Q. For transport, extend each scalar readout off the common finite history image by zero as a finite sum of singleton indicators. This supplies the globally measurable function required by IdentDistrib.comp and agrees on both histories. IdentDistrib.integral_eq and IdentDistrib.variance_eq then transport its moments and variance. The entire source partition, including repeated unordered pairs, is retained.

For the unconditional calculation, apply native_pair_sign_mean at (i,i+d,u,u), and native_four_sign_mean at (i,i+d,j,j+d,u,u,u,u), on Q and transport the resulting moments. Let Z_i be the product of the two opinion signs and c_i the equal-source indicator. Then E[Z_i]=E[c_i]. Define D_ij by a_i unequal b_i, a_j unequal b_j and {a_i,b_i}={a_j,b_j}. The Boolean identity for evenPairing is the disjoint union of the event that both pairs coalesce and D_ij. Therefore E[Z_i Z_j]=E[c_i c_j]+P(D_ij). The original three pairing events form a union, not a sum: four identical labels contribute one, not three. In particular D_ii is the unequal-source event.

The identity W_t=(t+sum_i Z_i)/2, variance_eq_sub and finite expansion give Var(W_t)=Var(C_t)/4 + sum_(i,j) P(D_ij)/4. For each source realization, expand m_e squared into the double sum of its membership indicators. Each D_ij selects exactly one unordered pair e. Hence sum_e m_e squared = sum_(i,j) 1_(D_ij). Finite sum and integral interchange yields Var(W_t)=Var(C_t)/4 + E[sum_e m_e squared]/4. All e are two-element subsets of the same deterministic L(G,u,N). Replacing a repeated pair by one copy would change this identity.

Apply Finset.card_eq_sum_card_fiberwise to the index set of unequal source pairs, the map i to {a_i,b_i}, and the target two-element subsets of L(G,u,N). The source support verifies its maps-to premise, giving sum_e m_e=t-C_t. Subtract its expectation divided by four from the variance identity. The excess over sum_i P(a_i unequal b_i)/4 is Var(C_t)/4 + E[sum_e m_e(m_e-1)]/4. Expanding m_e(m_e-1) removes the diagonal ordered pairs; exchanging i and j gives the equivalent second term sum_(i<j) P(D_ij)/2. Both the collision-count variance and the repeated-pair term are nonnegative. Neither term may be dropped from the equality formula.

Equality in this first lower bound holds exactly when C_t is almost surely constant and every m_e is at most one almost surely. Indeed, ae_eq_integral_of_variance_eq_zero applies to the bounded C_t, and integral_eq_zero_iff_of_nonneg applies to the bounded nonnegative sum of m_e(m_e-1). This sum vanishes exactly when every natural multiplicity is zero or one. Only finitely many e occur, so their almost-sure assertions hold simultaneously. Conversely those two conditions make both excess terms zero. This criterion concerns the first bound, not equality in the later universal bound.

The existing native_variance_lower already states the first inequality for a full-coordinate Model. For the explicit survival estimate, survives_iff_old_source identifies survives(x,i,d,u)=true with birth(source(x,i+d,u)) at most i. survival_probability gives this event probability q to the power d on Q, where q=1-epsilon. Because this birth event is a source-label readout, its probability transfers to the original P. source_birth_le gives birth(a_i) at most i pathwise. Thus a_i=b_i implies the birth event, so collision_probability_le transfers as P(a_i=b_i) at most q to the power d. Summation gives Var(W_t) at least t(1-q to the power d)/4 on P. Graph, root, noise, lag and horizon agree throughout these applications.

The raw conditioning field H is generated by ALL strictly positive-time refresh controls and neighbour choices at all vertices. A one-root joint finite-history law does not transfer conditional identities relative to H. Nor does sources_independent_coins alone establish independence from this larger field. A direct application of iIndepFun.indepFun_set on the original positive-coordinate index must use the entire control/choice family and the opinion-coordinate family as its disjoint sets. condExp_indep_eq additionally needs both sub-sigma-fields below the ambient field and strong measurability of the integrand. Conditional finite sums and pull-out also require the stated integrability hypotheses. The exact source-to-control-tuple measurability application and generated-field identification on P remain unresolved here. Accordingly the raw-H conditional cylinder law, pair-character moments, mean formula and variance formula are not supplied by this finite-history transfer. Conditional pair-character orthogonality would not imply mutual independence of all pair characters.

PotentialPaths.potential_path_source_correspondence identifies the independently defined event A_i along the unstopped d-layer copy path with survives and the source-birth event, and identifies its first refreshed label. PotentialPaths.original_potential_path_bounds supplies the measurable event, its exact probability and the native variance chain on the original positive-time law, without assumptions on unused time-zero auxiliary slots. TerminatedHistories.terminated_history_source_correspondence supplies the separate stopped-history and path-meeting equivalence.

At t=0 the observation index set is empty, W_t=C_t=0 and every m_e is zero. Both variance terms, both excess terms and the first-bound equality conditions reduce to their empty-sum cases even when the history horizon d is positive. These conclusions concern unconditional finite-history readouts. The raw-H conditional identities remain an additional boundary. The K2 finite-time independence identity, optimal-constant infimum and its upper and asymptotic endpoints are outside this application.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/NoisyVoter/AncestralSources.native_source`
- Truth anchor: `D5/S3/StatisticalMechanics/NoisyVoter/AncestralSources.uniform_variance_lower`
- Dependency: [D5/S3/StatisticalMechanics/NoisyVoter/RepetitionVarianceLinear](RepetitionVarianceLinear.md)
