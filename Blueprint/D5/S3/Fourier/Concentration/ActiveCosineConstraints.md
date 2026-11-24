# Two active cosine moment constraints

## Abstract

For q ≥ 4 and 0 < a < 1, both cosine moment bounds are tight at a joint minimum of squared mass.

On residues modulo q set cₖ = cos(2πk/q) and dₖ = cos(4πk/q). Let M and N be moments against c and d respectively. At a common target a, C(w), D(w), and J(w) mean that w minimizes the sum of squared weights over probability laws subject to the first bound, the second bound, and both bounds, respectively. Each bound is a lower bound a. Even(q) means that q is divisible by two.

**Theorem 1.1 (Strict cross-moment failure and joint tightness).**

$$\begin{aligned}&\forall q \in \mathbb{N},\quad q \ge 4,\quad \forall a \in \mathbb{R},\quad 0<a<1:\\&\forall w:\mathbb{Z}/q\mathbb{Z} \to \mathbb{R},\quad \operatorname{C}\left(w\right) \longrightarrow \operatorname{M}\left(w\right)=a \land \operatorname{N}\left(w\right)<a,\\&\forall w:\mathbb{Z}/q\mathbb{Z} \to \mathbb{R},\quad \operatorname{D}\left(w\right) \longrightarrow \operatorname{N}\left(w\right)=a \land \operatorname{M}\left(w\right)<a \land (\operatorname{Even}\left(q\right) \longrightarrow \operatorname{M}\left(w\right)=0),\\&\forall w:\mathbb{Z}/q\mathbb{Z} \to \mathbb{R},\quad \operatorname{J}\left(w\right) \longrightarrow \operatorname{M}\left(w\right)=a \land \operatorname{N}\left(w\right)=a.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/ActiveCosineConstraints.active_cosine_constraints` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The one-moment law is a normalized clipped affine function of its own readout. For the first moment, c−d = (1−c)(2c+1). Both readouts have mean zero, so one can subtract the clipped value at −1/2. The resulting summands are nonnegative and the residue 1 gives a positive term.

For the second moment on an even cycle, translation by a half-turn fixes d and negates c. On an odd cycle, doubling is a permutation, so the sum of squared clipped values is unchanged. Each squared positive-part tangent defect is nonnegative, and residue 1 supplies strict inequality.

If one bound had slack at a joint minimum, a small mixture with the minimizer for the other bound would still satisfy both bounds and would decrease the squared mass.

Direct evaluation at q = 3 gives identical readouts. At q = 2 the second readout is constant 1. At a = 0 the uniform minimizer has both moments zero. At a = 1 the first-mode bound forces the point mass at residue zero, whose two moments are one.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/ActiveCosineConstraints.active_cosine_constraints`
- Dependency: [D5/S3/Fourier/Concentration/ClippedMomentWeights](ClippedMomentWeights.md)
