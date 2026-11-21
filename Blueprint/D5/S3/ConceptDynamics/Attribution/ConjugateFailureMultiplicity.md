# Fixed mass under normal closure

## Abstract

Counting the occurrences of each seed in distinct conjugate failure events.

**Theorem 1.1 (Bound normal-closure loss by failure multiplicity).**

$$d (T - \operatorname{M}\left(N\right)) \le r (T - \operatorname{M}\left(H\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/ConjugateFailureMultiplicity.normal_closure_loss_mul_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let G act on a finite set S with nonnegative invariant real weights a. Write T for the sum of all the weights and M(K) for the weight of the seeds fixed by a subgroup K. Let N be the normal closure of H in G.

For each g in G, the failure event consists of the seeds moved by an element of the conjugate of H by g. Count each different event once and write r for their number. Suppose every positive-weight seed moved by N belongs to at least d different events, where d is a natural number.

Every event is a translate of the failure event for H. The sum of the weights counted over all the events therefore equals r times the loss for H. Counting the same weights by seed gives at least d times the loss for N, because each positive contribution to that loss is counted at least d times.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/ConjugateFailureMultiplicity.normal_closure_loss_mul_le`
- Dependency: [D5/S3/ConceptDynamics/Attribution/FixedKernelMass](FixedKernelMass.md)
