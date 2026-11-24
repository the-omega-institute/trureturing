# Minimum squared mass with one lower moment bound

## Abstract

A normalized positive part minimizes squared mass with a lower bound on one real moment.

For a finite index set I and real values cᵢ, let C be any attained value and a ≤ C. Write μ for the uniform mean, M for the real moment and E for the squared mass.

**Theorem 1.1 (Exact optimizer for one real lower moment bound).**

$$\begin{aligned}&T=\max(\{0\} \cup \{\frac{1}{C-c_{i}} \mid c_{i}<C\}),\\&\exists t \in [0,T],\quad a \le \mu \longrightarrow t=0,\\&u_{i}=\max(0,1-t(C-c_{i})),\quad v_{i}=\frac{u_{i}}{Z},\quad Z=\sum_{j}u_{j},\\&v_{i} \ge0,\quad \sum_{i}v_{i}=1,\quad \operatorname{M}\left(v\right)=\max(\mu,a),\\&\forall w: I \to \mathbb{R},\quad \sum_{i}w_{i}=1 \longrightarrow \\&\operatorname{E}\left(w\right)-\operatorname{E}\left(v\right)=\sum_{i}(w_{i}-v_{i})^{2}+\frac{2}{Z}(t(\operatorname{M}\left(w\right)-\operatorname{M}\left(v\right))+\sum_{i}(t(C-c_{i})-1)_{+}w_{i}),\\&((\forall i, w_{i} \ge0) \land a \le \operatorname{M}\left(w\right)) \longrightarrow \sum_{i}(w_{i}-v_{i})^{2} \le \operatorname{E}\left(w\right)-\operatorname{E}\left(v\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/ClippedMomentWeights.exists_clipped_moment_minimizer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Weimi Zhou and Yong-Jin Liu (2025). *Fast projection onto the intersection of simplex and singly linear constraint and its generalized Jacobian*. DOI: [10.61208/pjo-2025-002](https://doi.org/10.61208/pjo-2025-002). URL: <https://arxiv.org/html/2310.10388v3>.

*Commentary.*

Let I be a finite set, let c be a real readout on I, and take a target a at most an attained value C. Write μ for the uniform mean of c, M(w) for the weighted moment, E(w) for the sum of squared weights, and Z for the sum of the raw clipped weights u. All sums range over I. The identity holds for any real w of sum one. The inequality applies when w is also nonnegative and M(w) is at least a.

Zhou and Liu study Euclidean projection onto the intersection of the simplex and one linear half-space. With center zero and half-space vector −c, their shifted simplex projection gives the thresholded affine form for this objective.

At t = 0 the weights are uniform. Every index attaining C has raw weight one for all t, so the denominator stays positive. At the largest reciprocal of a positive gap C − cᵢ, or zero if there are no such gaps, all weights below C have vanished. The normalized moment is then at least C. Continuity gives a finite parameter for the required moment.

The affine constant disappears in the inner product with w − v by equality of total mass. At each clipped entry v vanishes, so replacing the negative raw weight by zero adds the clipped contribution in the identity. Both terms of the correction are nonnegative for feasible w when the moment bound is active. At t = 0 the correction is zero. The squared distance forces uniqueness.

On a finite cyclic group the readout can be the real part of a character at a single spatial residue. A whole spatial band imposes further joint constraints.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/ClippedMomentWeights.exists_clipped_moment_minimizer`
