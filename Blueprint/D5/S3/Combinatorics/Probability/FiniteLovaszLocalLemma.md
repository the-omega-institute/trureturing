# The Finite Symmetric Lovasz Local Lemma

## Abstract

A finite family of rare dependent events can be avoided simultaneously under the exponential symmetric local-lemma criterion.

Let Omega and I be finite types, with decidable equality on I. A real weight w on Omega is nonnegative and sums to one. For a set E, write P(E) for the sum of w over E. Let A_i be the bad events and G a simple graph on I with decidable adjacency. JointIndependence(w,A,G) means that for every index i and finite set S disjoint from i and all its neighbors, the probability of A_i intersected with all A_j for j in S equals P(A_i) times the probability of the latter intersection. Pairwise independence alone is insufficient.

**Theorem 1.1 (Positive Probability of Avoiding Every Bad Event).**

$$\forall Omega \in \mathrm{Type},\; [\mathrm{Fintype}\left(Omega\right)] \forall I \in \mathrm{Type},\; [\mathrm{Fintype}\left(I\right)] [\mathrm{DecidableEq}\left(I\right)] \forall w \in \mathrm{Function}\left(Omega, \mathrm{Real}\right),\; \forall A \in \mathrm{Function}\left(I, \mathrm{Set}\left(Omega\right)\right),\; \forall G \in \mathrm{SimpleGraph}\left(I\right),\; [\mathrm{DecidableRel}\left(\mathrm{Adj}\left(G\right)\right)] \forall p \in \mathrm{Real},\; \forall d \in \mathrm{Nat},\; (\mathrm{NonnegativeWeights}\left(w\right) \land \left(\mathrm{TotalWeight}\left(w\right) = 1 \land \left(0 \le p \land \left(\mathrm{maxDegree}\left(G\right) \le d \land \left(\left(\forall x \in I,\; \mathrm{P}\left(w, \mathrm{Apply}\left(A, x\right)\right) \le p\right) \land \left(\mathrm{JointIndependence}\left(w, A, G\right) \land \mathrm{exp}\left(1\right) \cdot p \cdot \left(\mathrm{RealCast}\left(d\right) + 1\right) \le 1\right)\right)\right)\right)\right)) \Rightarrow (0 < \mathrm{P}\left(w, \mathrm{AvoidAll}\left(A\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Probability/FiniteLovaszLocalLemma.lovasz_local_lemma_symmetric_finite` (`✓ std3`). ∎

*Citation.* ATLAS contributors; AutoformBot (2026). *ATLAS finite symmetric Lovasz local lemma*. URL: <https://github.com/facebookresearch/atlas-lean/blob/0b121a198307b6153181f5a1d9145dcda2f7bfee/MathlibExt/Probability/Combinatorics/LovaszLocalLemma.lean>.

*Commentary.*

For a nonnegative real p and natural d, suppose every bad event has probability at most p, the maximum degree of G is at most d, and the stated joint independence condition holds. If exp(1) p (d+1) is at most one, the event that all bad events fail has strictly positive probability. The conclusion includes the zero-degree boundary case. It asserts simultaneous avoidance and does not provide an efficient search algorithm.

## References

- Truth anchor: `D5/S3/Combinatorics/Probability/FiniteLovaszLocalLemma.lovasz_local_lemma_symmetric_finite`
