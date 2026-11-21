# Fixed mass under normal closure

## Abstract

Counting the occurrences of each seed in distinct conjugate failure events.

**Theorem 1.1 (Exact loss gap and equality criterion).**

$$\operatorname{LowerBound}\left(d\right) \Rightarrow (r \operatorname{L}\left(H\right) - d \operatorname{L}\left(N\right) = \operatorname{SumMoved}\left(s, \operatorname{a}\left(s\right) (\operatorname{C}\left(s\right) - d)\right) \land 0 \le r \operatorname{L}\left(H\right) - d \operatorname{L}\left(N\right) \land (r \operatorname{L}\left(H\right) - d \operatorname{L}\left(N\right) = 0 \Leftrightarrow \operatorname{ExactMultiplicity}\left(d\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/ConjugateFailureMultiplicity.normal_closure_loss_gap_and_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let G act on a finite set S with nonnegative invariant real weights a. Write T for the sum of all the weights and M(K) for the weight of the seeds fixed by a subgroup K. Let N be the normal closure of H in G.

For each g in G, the failure event consists of the seeds moved by an element of the conjugate of H by g. Count each different event once and write r for their number. For a seed s write C(s) for the number of events containing it. Write L(K) for T minus M(K).

Let d be a natural number that bounds C(s) from below for every positive-weight seed moved by N. LowerBound is that premise. ExactMultiplicity means C(s) equals d on the same seeds. The gap equals the sum on the right, with SumMoved ranging over seeds moved by N. The gap is nonnegative and equals zero exactly when every such seed has C(s) equal to d.

Weight invariance gives the same loss for every conjugate event. Counting by seed gives the weighted multiplicity, which is zero on a seed fixed by N. Subtracting d times the loss for N gives the formula. On the stated support every summand is nonnegative. Each positive-weight moved seed then contributes zero exactly at multiplicity d.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/ConjugateFailureMultiplicity.normal_closure_loss_gap_and_eq`
- Dependency: [D5/S3/ConceptDynamics/Attribution/FixedKernelMass](FixedKernelMass.md)
