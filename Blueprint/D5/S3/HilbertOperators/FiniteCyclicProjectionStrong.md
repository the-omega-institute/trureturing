# Strong convergence of finite cyclic orthogonal projections

## Abstract

The powers of each fixed finite ordered product of actual orthogonal projections converge in norm on every vector to the actual projection onto the common intersection.

**Definition 1.1 (Ordered projection product).**

Lean statement: `D5/S3/HilbertOperators/FiniteCyclicProjectionStrong.cycle`

*Formalization.* `D5/S3/HilbertOperators/FiniteCyclicProjectionStrong.cycle` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite ordered list Us of closed k-linear subspaces of H, Cycle(Us) is a bounded k-linear endomorphism. Cycle([]) is the identity. For a head U and tail Vs, Cycle(U::Vs) is Cycle(Vs) composed with the actual orthogonal projection P(U). Thus the first listed projection acts first, and the last listed projection acts last. The order is part of the list and remains fixed throughout iteration.

**Theorem 1.2 (Convergence to the common intersection).**

$$\forall (u: \operatorname{UniverseLevel}()), \forall (v: \operatorname{UniverseLevel}()), \forall (k: \operatorname{Type}_{u}), \forall (H: \operatorname{Type}_{v}), [\operatorname{RCLike}(k)] [\operatorname{NormedAddCommGroup}(H)] [\operatorname{InnerProductSpace}(k, H)] [\operatorname{CompleteSpace}(H)] \forall (Us: \operatorname{List}(\operatorname{ClosedSubmodule}(k, H))), \forall (x: H), \forall (epsilon: \mathbb{R}), (0 < epsilon) \Rightarrow \exists (N: \mathbb{N}), \forall (n: \mathbb{N}), (N \leq n) \Rightarrow \left\lVert (\operatorname{Cycle}(Us))^{n}(x) - \operatorname{P}(\operatorname{Inter}(Us))(x) \right\rVert < epsilon$$

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/FiniteCyclicProjectionStrong.tendsto_cycle_pow` (`✓ std3`). ∎

*Citation.* Omer Ginat (2018). *The method of alternating projections*. URL: <https://arxiv.org/pdf/1809.05858v1>.

*Commentary.*

The universes u and v are independent. The scalar k is any RCLike field, and H is any complete inner product space over k. The list Us and initial vector x are arbitrary. Inter(Us) is the infimum of the set of subspaces occurring in Us, so membership means membership in every listed subspace. P(Inter(Us)) is its actual orthogonal projection. For every positive real epsilon there is a natural N such that every n at least N satisfies the displayed strict norm bound. N may depend on k, H, Us, x and epsilon.

For every finite list and vector z, the squared displacement of one complete cycle is at most 2 to the power length(Us) times the drop in squared norm. Inductively split a cycle into its first projection and the remaining cycle. The projection Pythagorean identity gives the first loss; the inductive bound gives the remaining loss. The triangle inequality combines the two displacements. The factor 2 to the power length(Us) is sufficient and is not asserted sharp.

The cycle is a contraction. A vector fixed by the cycle has equal norms through the initial projection and the remaining contraction. Equality in the projection norm bound puts the vector in the first subspace, and induction puts it in every subsequent subspace. Conversely, a vector in every subspace is fixed by every factor. Thus the fixed locus is exactly Inter(Us).

Along the actual orbit, squared norms are nonnegative and antitone. Their successive drops tend to zero. The complete-cycle energy inequality then gives asymptotic regularity. The Hilbert space mean ergodic theorem gives convergence of the averages to the fixed-locus projection. The fixed-window convergence theorem for contractive powers transfers these averages and asymptotic regularity to convergence of the actual nonaveraged powers. Uniqueness of orthogonal projection identifies the limit with P(Inter(Us))x.

The empty list has identity cycle and whole-space intersection. A singleton gives its orthogonal projection. Arbitrary repetitions, the zero or whole subspace, and the zero ambient space are included. There is no dimension, separability, positive-angle, closed-sum, nonzero or distinct-subspace assumption. The conclusion gives pointwise norm convergence, with no rate and no operator-norm convergence assertion.

Ginat, arXiv:1809.05858v1, Section 4.2, Theorem 4.2 on printed page 21, states Halperin's finite-family theorem for real or complex Hilbert spaces and J at least 2, with T=P_J ... P_1. The empty and singleton cases are included in the present formal statement. The source is an exposition; Halperin's original paper is cited there but is not the directly consulted source.

## References

- Truth anchor: `D5/S3/HilbertOperators/FiniteCyclicProjectionStrong.cycle`
- Truth anchor: `D5/S3/HilbertOperators/FiniteCyclicProjectionStrong.tendsto_cycle_pow`
- Dependency: [D5/S3/HilbertOperators/AlternatingProjectionStrong](AlternatingProjectionStrong.md)
