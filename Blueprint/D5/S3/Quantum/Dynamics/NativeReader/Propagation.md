# Full native propagation at every physical call time

## Abstract

Full native propagation at every physical call time.

**Theorem 1.1 (Full native propagation at every physical call time).**

$$\forall lambda, \forall k: \operatorname{Fin}\left(15\right), \forall s, \operatorname{InUnitInterval}\left(s\right) \implies \operatorname{OperatorNormDifference}\left(\operatorname{fullInternalOperator}\left(lambda, k, s\right), \operatorname{fullInternalOperator}\left(alpha, k, s\right)\right) \leq 12 \times \operatorname{abs}\left(lambda - alpha\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/NativeReader/Propagation.full_operator_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The matrices act on every one of the 610 extended coordinates with the Euclidean operator norm. Their exact source/tail block identity transports the existing weighted-path Hermitian projection laws to the full carrier. The phase is retained. Existing spectral-block multiplication gives unitarity. The pinned complex phase bound gives an error at most twice the angle change per changed factor. Chronological product induction counts the four occurrences of address eleven and two of address thirteen. Thus every internal time s in [0,1] in every one of the fifteen physical calls has operator error at most 12*abs(lambda-alpha). No input-state norm or projected subcarrier is substituted for this operator estimate. The proof uses standard algebra and norm bookkeeping and earns no additional content credit. Its live consumer is the auxiliary no-jump and propagation result in History. The native Bell probability law, report total variation witness and full source/archive history correspondence are additional obligations.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/NativeReader/Propagation.full_operator_bound`
- Dependency: [D5/S3/Quantum/Dynamics/NativeReader/Global](Global.md)
