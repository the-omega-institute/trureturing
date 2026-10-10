# Four-Exit Coarse Controller Lower Bounds

## Abstract

Two subset potentials bound every probability law of coarse-observable original controllers, including laws with infinite expected costs.

For k at least one, I(k)=Unit plus Fin(k) times Fin(4), and n(k)=8k+16. F(k,i) is the existing literal family from FourExitRawEndpointSpectrum. The baseline is the Unit row; rows zero, one, two and three in a slot are A, Y, H and Z. The Strategy, chronological execution, terminal history, distinct-address cost, leaf addresses and coarse observability are the existing actual-tree interfaces. Every Strategy is globally correct on all finite sources; neither a family promise nor a uniform termination bound is assumed.

A law consists of any measurable space Omega, a probability measure mu on it, and an arbitrary choice c:Omega to Strategy. Every c(omega) is coarse-observable, and each coordinate omega to C_i(c(omega)) is measurable as an extended nonnegative real function. No finite support, measurable controller carrier or finiteness of expectation is required. R is the supremum of the coordinate expectations. D is the infimum, over all coarse-observable original Strategies, of their worst coordinate cost. W is the expectation of the supremum of coordinate costs. All expectations are nonnegative Lebesgue integrals and can be infinite.

**Theorem 1.1 (Arbitrary Laws and Deterministic Two-Excess Obstruction).**

$$\forall k: Nat, ((1 \leq k) \implies (\forall Omega: MeasurableSpace, (\forall mu: \operatorname{Probability}\left(Omega\right), (\forall c: \operatorname{Controllers}\left(Omega\right), (((\operatorname{CoarseLaw}\left(k, mu, c\right)) \land (\operatorname{MeasurableCosts}\left(k, c\right))) \implies ((\operatorname{n}\left(k\right) + \frac{5 \cdot k - 1}{4 \cdot k} \leq \operatorname{R}\left(k, mu, c\right)) \land (\operatorname{n}\left(k\right) + \frac{4 \cdot k - 2}{3 \cdot k} \leq \operatorname{R}\left(k, mu, c\right)) \land (\forall pi: Strategy, ((\operatorname{CoarseObservable}\left(\operatorname{policy}\left(pi\right)\right)) \implies (\exists i: \operatorname{I}\left(k\right), (\operatorname{n}\left(k\right) + 2 \leq \operatorname{C}\left(k, i, pi\right))))) \land (\operatorname{n}\left(k\right) + 2 \leq \operatorname{D}\left(k\right)) \land (\operatorname{n}\left(k\right) + 2 \leq \operatorname{W}\left(k, mu, c\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/FourExitCoarseLowerBounds.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite fuel chosen from the actual terminating executions produces a finite coarse tree with the original terminal histories. At any none branch, saturation and fresh divergence imply that at most one row in a counting subset has excess below two. Following the leaf branch therefore yields a charge inequality for every subset.

For all nonbaseline rows the potential sums min(column size,3). The actual support table excludes a leaf support of size three, so every relevant none deletion drops this potential. For the A,Y,Z subset the potential sums min(triple size,2); a one-unit credit accounts for its possible nondropping deletion. The actual common compensation support ensures that this exception occurs at most once. At the root these yield total excess at least 5k-1 and 4k-2, respectively. Finite-sum integration and averaging give the two bounds on R.

On the baseline together with any four-row slot, the actual support table excludes a leaf child of size four. The first information query thus has at least two none rows. Their subsequent fresh divergence forces one row to pay a second nonleaf. This gives a deterministic row of cost at least n+2, the infimum bound on D and the pointwise bound whose integral yields W.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FourExitCoarseLowerBounds.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualCoarseReadoutCompletion](ActualCoarseReadoutCompletion.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/FourExitRawDomination](FourExitRawDomination.md)
