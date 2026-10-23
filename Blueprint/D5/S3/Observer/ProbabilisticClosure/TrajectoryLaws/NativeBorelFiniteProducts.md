# The unweighted finite product

## Abstract

Finite killed products on the original flow

**Theorem 1.1 (Measurable finite-history extension).**

$$\forall S: MeasurableType, \forall n: Nat, \operatorname{Measurable}\left(\operatorname{snocMap}\left(S, n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelFiniteProducts.snoc_measurable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every type S with its arbitrary measurable space and every natural n, snocMap(S,n) sends a pair (w,y) with w:Fin(n+1)->S and y:S to Fin.snoc(w,y):Fin(n+2)->S. Measurability is checked coordinatewise. This supplier is consumed in the actual finite product extension and trajectory shift proof.

**Theorem 1.2 (The actual homogeneous finite history).**

$$\forall S: MeasurableType, \forall mu: ProbabilityMeasureS, \forall K: MarkovKernelS, \forall n: Nat, \operatorname{finitePrefix}\left(\operatorname{homogeneousLaw}\left(mu, K\right), n\right)=\operatorname{finiteProduct}\left(mu, K, n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelFiniteProducts.homogeneous_prefix_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every measurable type S, probability measure mu, Markov kernel K:S->S and n:Nat, the prefix pushforward of homogeneousLaw(mu,K) to Fin(n+1) equals finiteProduct(mu,K,n). The proof uses the original trajectory partial products and the exact measurable index equivalence. The same supplier identifies started and shifted original C histories.

**Theorem 1.3 (Surviving prefixes and row densities).**

$$\forall F: CommonFlow, \exists G\subset PDescriptor, \exists hsub: \operatorname{Subprobability}\left(\operatorname{doob}\left(F, G\right)\right), \operatorname{MeasurableSet}\left(G\right)\land \operatorname{AE}\left(\operatorname{nuP}\left(F\right), Q, Q\in G\right)\land \operatorname{AE}\left(\operatorname{nuP}\left(F\right), Q, \operatorname{AE}\left(\operatorname{CRow}\left(F, Q\right), R, \operatorname{rowDerivative}\left(\operatorname{doob}\left(F, G\right), \operatorname{C}\left(F\right), Q, R\right)\leq\operatorname{inv}\left(\operatorname{threeStepAverage}\left(F, Q\right)\right) \cdot \operatorname{threeStepAverage}\left(F, R\right) \cdot \operatorname{ofReal}\left(1+\frac{25 \cdot \operatorname{excess}\left(Q\right)}{9}\right)\right)\right)\land \forall n: Nat, \operatorname{restrict}\left(\operatorname{finitePrefix}\left(\operatorname{killedTrajectory}\left(F, \operatorname{doob}\left(F, G\right), hsub\right), n\right), \operatorname{allLive}\left(n\right)\right)=\operatorname{map}\left(\operatorname{finiteProduct}\left(\operatorname{nuP}\left(F\right), \operatorname{doob}\left(F, G\right), n\right), \operatorname{includePrefix}\left(n\right)\right)\land \operatorname{finiteProduct}\left(\operatorname{nuP}\left(F\right), \operatorname{doob}\left(F, G\right), n\right)=\operatorname{withDensity}\left(\operatorname{finitePrefix}\left(\operatorname{originalTrajectory}\left(F\right), n\right), \operatorname{finiteDensity}\left(F, \operatorname{doob}\left(F, G\right), n\right)\right)\land \operatorname{AbsolutelyContinuous}\left(\operatorname{finiteProduct}\left(\operatorname{nuP}\left(F\right), \operatorname{doob}\left(F, G\right), n\right), \operatorname{finitePrefix}\left(\operatorname{originalTrajectory}\left(F\right), n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelFiniteProducts.common_flow_finite_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

finiteProduct(mu,K,n) is the actual unnormalized kernel product on the complete finite history of n+1 states. It starts with mu at time zero, and each extension appends the actual K row at the last state by a composition-product. finitePrefix(mu,n) maps a full path measure to its coordinates indexed by Fin(n+1). allLive(n) requires every one of those coordinates to differ from the cemetery state; includePrefix(n) applies the live inclusion to every original coordinate.

For the original Doob kernel M, restricting its lawful cemetery prefix to allLive gives the included finiteProduct(nuP,M,n). There is no terminal survival weight in this equality. The same finite M measure equals the original C prefix weighted by finiteDensity(F,M,n), the product over i=0,...,n-1 of the jointly measurable row Radon-Nikodym derivative M/C at the actual adjacent states. The extension proof uses the same preceding history at each step. This earns absolute continuity on each finite prefix; the complete immortal-law absolute continuity is supplied by the separate full-path identity.

**Theorem 1.4 (Finite-history h-ratio and excess bound).**

$$\forall F: CommonFlow, \exists G\subset PDescriptor, \exists hsub: \operatorname{Subprobability}\left(\operatorname{doob}\left(F, G\right)\right), \operatorname{MeasurableSet}\left(G\right)\land \operatorname{AE}\left(\operatorname{nuP}\left(F\right), Q, Q\in G\right)\land \operatorname{AE}\left(\operatorname{nuP}\left(F\right), Q, \operatorname{AE}\left(\operatorname{CRow}\left(F, Q\right), R, \operatorname{rowDerivative}\left(\operatorname{doob}\left(F, G\right), \operatorname{C}\left(F\right), Q, R\right)\leq\operatorname{inv}\left(\operatorname{threeStepAverage}\left(F, Q\right)\right) \cdot \operatorname{threeStepAverage}\left(F, R\right) \cdot \operatorname{ofReal}\left(1+\frac{25 \cdot \operatorname{excess}\left(Q\right)}{9}\right)\right)\right)\land \forall n: Nat, \operatorname{AE}\left(\operatorname{finiteProduct}\left(\operatorname{nuP}\left(F\right), \operatorname{C}\left(F\right), n\right), w, \operatorname{rnDeriv}\left(\operatorname{finiteProduct}\left(\operatorname{nuP}\left(F\right), \operatorname{doob}\left(F, G\right), n\right), \operatorname{finiteProduct}\left(\operatorname{nuP}\left(F\right), \operatorname{C}\left(F\right), n\right), w\right)\leq\operatorname{inv}\left(\operatorname{threeStepAverage}\left(F, \operatorname{at}\left(w, 0\right)\right)\right) \cdot \operatorname{threeStepAverage}\left(F, \operatorname{at}\left(w, \operatorname{last}\left(n\right)\right)\right) \cdot \operatorname{prod}\left(i, \operatorname{Fin}\left(n\right), \operatorname{ofReal}\left(1+\frac{25 \cdot \operatorname{excess}\left(\operatorname{at}\left(w, \operatorname{castSucc}\left(i\right)\right)\right)}{9}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelFiniteProducts.common_flow_finite_history_rn_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The row comparison is transported along the same stationary original C history. The product density is the exact Radon-Nikodym derivative of the all-live Doob product against the original finite C product, and telescoping the intermediate three-step averages yields h(X_n)/h(X_0) times the product of the original excess factors. Every horizon is retained, and terminal cancellation is made only on the transported conull carrier where h is finite and positive.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelFiniteProducts.common_flow_finite_history_rn_bound`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelFiniteProducts.common_flow_finite_product`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelFiniteProducts.homogeneous_prefix_product`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelFiniteProducts.snoc_measurable`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelKilledPaths](NativeBorelKilledPaths.md)
