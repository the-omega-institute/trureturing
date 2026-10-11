# The unweighted finite product

## Abstract

Finite killed products on the original flow

**Theorem 1.1 (Surviving prefixes and row densities).**

$$\forall F: CommonFlow, \exists G\subset PDescriptor, \exists hsub: \operatorname{Subprobability}\left(\operatorname{doob}\left(F, G\right)\right), \operatorname{MeasurableSet}\left(G\right)\land \operatorname{AE}\left(\operatorname{nuP}\left(F\right), Q, Q\in G\right)\land \forall n: Nat, \operatorname{restrict}\left(\operatorname{finitePrefix}\left(\operatorname{killedTrajectory}\left(F, \operatorname{doob}\left(F, G\right), hsub\right), n\right), \operatorname{allLive}\left(n\right)\right)=\operatorname{map}\left(\operatorname{finiteProduct}\left(\operatorname{nuP}\left(F\right), \operatorname{doob}\left(F, G\right), n\right), \operatorname{includePrefix}\left(n\right)\right)\land \operatorname{finiteProduct}\left(\operatorname{nuP}\left(F\right), \operatorname{doob}\left(F, G\right), n\right)=\operatorname{withDensity}\left(\operatorname{finitePrefix}\left(\operatorname{originalTrajectory}\left(F\right), n\right), \operatorname{finiteDensity}\left(F, \operatorname{doob}\left(F, G\right), n\right)\right)\land \operatorname{AbsolutelyContinuous}\left(\operatorname{finiteProduct}\left(\operatorname{nuP}\left(F\right), \operatorname{doob}\left(F, G\right), n\right), \operatorname{finitePrefix}\left(\operatorname{originalTrajectory}\left(F\right), n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelFiniteProducts.common_flow_finite_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

finiteProduct(mu,K,n) is the actual unnormalized kernel product on the complete finite history of n+1 states. It starts with mu at time zero, and each extension appends the actual K row at the last state by a composition-product. finitePrefix(mu,n) maps a full path measure to its coordinates indexed by Fin(n+1). allLive(n) requires every one of those coordinates to differ from the cemetery state; includePrefix(n) applies the live inclusion to every original coordinate.

For the original Doob kernel M, restricting its lawful cemetery prefix to allLive gives the included finiteProduct(nuP,M,n). There is no terminal survival weight in this equality. The same finite M measure equals the original C prefix weighted by finiteDensity(F,M,n), the product over i=0,...,n-1 of the jointly measurable row Radon-Nikodym derivative M/C at the actual adjacent states. The extension proof uses the same preceding history at each step. This earns absolute continuity on each finite prefix; the complete immortal-law absolute continuity is supplied by the separate full-path identity.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelFiniteProducts.common_flow_finite_product`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelKilledPaths](NativeBorelKilledPaths.md)
