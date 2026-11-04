# Strong convergence of alternating orthogonal projections

## Abstract

The actual powers of two orthogonal projections converge in norm on every vector to the projection onto the intersection, in an arbitrary complete real or complex Hilbert space.

For a closed k-linear subspace U of H, P(U) denotes the actual orthogonal projection onto U from H to H. Comp(A,B) applies B first and then A. Inf(U,V) denotes the closed linear intersection. Powers are powers of bounded endomorphisms: the zeroth power is the identity, and applying the nth power agrees with n iterations of the same map.

**Theorem 1.1 (Actual nonaveraged powers).**

$$\forall (u: \operatorname{UniverseLevel}()), \forall (v: \operatorname{UniverseLevel}()), \forall (k: \operatorname{Type}_{u}), \forall (H: \operatorname{Type}_{v}), [\operatorname{RCLike}(k)] [\operatorname{NormedAddCommGroup}(H)] [\operatorname{InnerProductSpace}(k, H)] [\operatorname{CompleteSpace}(H)] \forall (U: \operatorname{ClosedSubmodule}(k, H)), \forall (V: \operatorname{ClosedSubmodule}(k, H)), \forall (x: H), \forall (epsilon: \mathbb{R}), (0 < epsilon) \Rightarrow \exists (N: \mathbb{N}), \forall (n: \mathbb{N}), (N \leq n) \Rightarrow \left\lVert (\operatorname{Comp}(\operatorname{P}(U), \operatorname{P}(V)))^{n}(x) - \operatorname{P}(\operatorname{Inf}(U, V))(x) \right\rVert < epsilon$$

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/AlternatingProjectionStrong.tendsto_alternating_projection_pow` (`✓ std3`). ∎

*Citation.* Heinz H. Bauschke, Frank Deutsch, Hein Hundal (2007). *Characterizing arbitrarily slow convergence in the method of alternating projections*. URL: <https://arxiv.org/pdf/0710.2387v1>.

*Commentary.*

The universes u and v, the RCLike scalar k, and the complete inner product space H are arbitrary. For all closed k-linear subspaces U and V and every x in H, set T=P(U) composed with P(V). Then the sequence T to the power n applied to x converges in the norm topology to P(Inf(U,V)) applied to x. The displayed epsilon statement is precisely this pointwise norm convergence; N can depend on the vector, both subspaces and epsilon.

For the same actual orbit x_n=T^n x, apply the orthogonal-projection Pythagorean identity at x_n and at P(V)x_n. The triangle inequality bounds the squared full-step displacement by twice the drop in squared orbit norm. The squared norms are nonnegative and antitone, so the monotone convergence theorem gives their limit and their successive drops tend to zero. Squeezing the squared increments and taking square roots proves x_(n+1)-x_n tends to zero.

For each fixed positive m, telescope finitely many increments to obtain x_(n+i)-x_n tending to zero for every i below m. Linearity identifies T^n applied to the m-term Cesàro average, minus x_n, with the average of these finitely many shifted differences. This error tends to zero with m fixed. Contractivity bounds the distance of the transported average from a fixed vector by its original average error, uniformly in n. Given epsilon, choose m from Cesàro convergence first, then choose n from the fixed-window error. No interchange of two limits or Cauchy conclusion from square summability is used.

The product is a contraction. Its fixed vectors are exactly U intersect V: a fixed vector lies in U, and equality through the two projection norm bounds forces it into V by the characterization of equality in the orthogonal-projection norm bound. Conversely, each vector in both subspaces is fixed. The Hilbert space mean ergodic theorem supplies Cesàro convergence to the fixed-locus projection. Uniqueness of orthogonal projection identifies that projection with the actual intersection projection, giving the endpoint used in the fixed-window estimate.

The statement includes zero ambient space, zero or whole subspaces, coincident subspaces, arbitrary infinite dimension, nonseparability and zero Friedrichs angle. It assumes no closed sum, positive angle, finite dimension, separability, convergence rate, prior convergence or supplied decomposition. It asserts convergence for each vector in the norm topology, and supplies no operator-norm convergence or uniform rate.

The classical result is von Neumann's alternating-projection theorem, stated in Theorem 1.1 of Bauschke, Deutsch and Hundal, arXiv:0710.2387v1. Badea, Grivaux and Müller, arXiv:1006.2047v1, equation (1.1), gives the same strong-convergence formula and discusses the separate operator-norm question.

## References

- Truth anchor: `D5/S3/HilbertOperators/AlternatingProjectionStrong.tendsto_alternating_projection_pow`
