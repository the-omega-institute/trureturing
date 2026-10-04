# Directed positive operator nets

## Abstract

An increasing positive operator net converges strongly to its operator-order least upper bound.

**Theorem 1.1 (Strong convergence to the order supremum).**

$$\forall H \in \operatorname{Type}\left(\right),\; \forall J \in \operatorname{Type}\left(\right),\; [\operatorname{NormedAddCommGroup}\left(H\right)] [\operatorname{InnerProductSpace}\left(\mathbb{C}, H\right)] [\operatorname{CompleteSpace}\left(H\right)] [\operatorname{Preorder}\left(J\right)] [\operatorname{Nonempty}\left(J\right)] [\operatorname{IsDirectedOrder}\left(J\right)] \forall X \in J \to \operatorname{ContinuousLinearMap}\left(\mathbb{C}, H, H\right),\; \forall U \in \operatorname{ContinuousLinearMap}\left(\mathbb{C}, H, H\right),\; (\forall i \in J,\; 0 \le X\left(i\right)) \Rightarrow ((\operatorname{Monotone}\left(X\right)) \Rightarrow ((\operatorname{IsLUB}\left(\operatorname{range}\left(X\right), U\right)) \Rightarrow ((\forall i \in J,\; \left\lVert X\left(i\right) \right\rVert \le \left\lVert U \right\rVert) \land (\forall v \in H,\; \operatorname{Tendsto}\left((i: J) \mapsto X\left(i\right)\left(v\right), atTop, \operatorname{nhds}\left(U\left(v\right)\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/DirectedPositiveNet.directed_positive_net_strong_of_isLUB` (`✓ std3`). ∎

*Citation.* Jesse Peterson (2013). *Notes on von Neumann algebras*. URL: <https://math.vanderbilt.edu/peters10/teaching/spring2013/vonNeumannAlgebras.pdf>.

*Commentary.*

H is any complete complex inner-product space. J is any nonempty directed preorder; a common upper index is sufficient, and no countable cofinal subset is assumed. ContinuousLinearMap denotes bounded complex linear operators. Their order is the positive-operator order.

X is positive at every index and monotone. IsLUB(range(X), U) says that U bounds all X(j) above and is below every such upper bound. The conclusions give the operator norm bound and pointwise strong convergence to U.

For a positive difference D, its continuous-functional-calculus square root gives the bound norm(D(v)) squared by norm(D) times the real quadratic form. Scalar monotone convergence and common upper indices then make every vector net Cauchy. Completeness, linearity of limits and the uniform norm bound construct a bounded linear limit S. Positivity survives strong limits, so S is a least upper bound and equals U.

The proof uses the positive constant norm(U) plus one. It applies also when U is zero or H is the zero space. Peterson's Lemma 2.7.1 supplies the classical monotone-net context; the displayed result identifies the limit with a specified operator-order least upper bound.

## References

- Truth anchor: `D5/S3/Quantum/Measurements/DirectedPositiveNet.directed_positive_net_strong_of_isLUB`
