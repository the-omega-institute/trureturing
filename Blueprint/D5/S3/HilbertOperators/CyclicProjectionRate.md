# Linear regularity and cyclic projection rates

## Abstract

Linear regularity exactly characterizes uniform geometric convergence of a finite cyclic product, with the inclination energy rate.

**Definition 1.1 (Same-family residual observation).**

Lean statement: `D5/S3/HilbertOperators/CyclicProjectionRate.LinearRegular`

*Formalization.* `D5/S3/HilbertOperators/CyclicProjectionRate.LinearRegular` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let k be an RCLike field and H a complete inner product space over k, with independent universes. Let Us be a nonempty finite ordered list of closed subspaces, m its length, M the infimum of its members, P the actual orthogonal projection onto M, and T the existing cycle of Us, whose first listed factor acts first. R(Us,ell) means that for every x in H there is a member U of Us such that ell times the norm of x-Px is at most the norm of x-P_U x. The witnessing member can depend on x. Every projection refers to this same actual family.

**Theorem 1.2 (Inclination energy rate).**

$$\forall (ell: \mathbb{R}), (0 < ell \leq 1 \land \operatorname{R}(Us, ell)) \Rightarrow \forall (n: \mathbb{N}), \forall (x: H), (\left\lVert \operatorname{Iterate}(\operatorname{Cycle}(Us), n, x)-\operatorname{P}(\operatorname{Inter}(Us), x) \right\rVert)^{2} \leq (1-\frac{(ell)^{2}}{(\operatorname{length}(Us))^{2}})^{n} (\left\lVert \operatorname{Iterate}(\operatorname{Cycle}(Us), 0, x)-\operatorname{P}(\operatorname{Inter}(Us), x) \right\rVert)^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/CyclicProjectionRate.geometric_rate` (`✓ std3`). ∎

*Citation.* Catalin Badea, Sophie Grivaux, Vladimir Müller (2010). *The rate of convergence in the method of alternating projections*. DOI: [10.48550/arXiv.1006.2047](https://doi.org/10.48550/arXiv.1006.2047). URL: <https://arxiv.org/abs/1006.2047v1>.

*Commentary.*

The displayed estimate holds for every natural n, including zero, and every x in H whenever zero is less than ell, ell is at most one, and R(Us,ell) holds. The scalar ell is any admissible lower bound, without an infimum or an angle parameter.

For one cycle starting at z, write E for the drop in squared norm. Projection Pythagoras makes E nonnegative and bounds each successive step by the square root of E. Induction along the actual list, using contractivity of complementary projections, bounds each member residual at the initial z by m times the square root of E. Squaring yields the member residual bound by m squared times E.

The common projection p=Px belongs to every listed subspace and is fixed by the cycle. Apply the member estimate to x-p. The regularity witness then forces a loss of at least ell squared divided by m squared of the squared distance to M. Nested orthogonal projections show PTx=Px. Induction on n gives the displayed rate with the same P and T.

**Theorem 1.3 (Exact uniform geometric classification).**

$$(\exists (ell: \mathbb{R}), 0 < ell \leq 1 \land \operatorname{R}(Us, ell)) \Leftrightarrow (\exists (q: \mathbb{R}), 0 \leq q < 1 \land \forall (n: \mathbb{N}), \forall (x: H), (\left\lVert \operatorname{Iterate}(\operatorname{Cycle}(Us), n, x)-\operatorname{P}(\operatorname{Inter}(Us), x) \right\rVert)^{2} \leq (q)^{n} (\left\lVert \operatorname{Iterate}(\operatorname{Cycle}(Us), 0, x)-\operatorname{P}(\operatorname{Inter}(Us), x) \right\rVert)^{2})$$

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/CyclicProjectionRate.linear_regular_iff_uniform_geometric` (`✓ std3`). ∎

*Citation.* Catalin Badea, Sophie Grivaux, Vladimir Müller (2010). *The rate of convergence in the method of alternating projections*. DOI: [10.48550/arXiv.1006.2047](https://doi.org/10.48550/arXiv.1006.2047). URL: <https://arxiv.org/abs/1006.2047v1>.

*Commentary.*

For this fixed actual family, a positive regularity constant at most one exists if and only if a real q with zero at most q and q less than one gives the squared-error estimate for every natural n and every vector. The forward direction chooses q=1-ell squared divided by m squared.

Conversely, put a=sqrt(q) and ell=(1-a)/m. The n=1 estimate bounds the norm of Tx-Px by a times the norm of x-Px. A member U maximizing the initial residual exists because the actual list is finite and nonempty. Contractivity and telescoping bound the complete displacement by m times this maximal member residual. The triangle inequality therefore proves R(Us,ell), and zero is less than ell and ell is at most one.

There is no dimension, separability, angle, closed-sum or additional contraction hypothesis. Repeated subspaces, singleton lists, top and bottom subspaces, the zero Hilbert space, ell=1 and q=0 are included. The list remains nonempty.

Badea, Grivaux and Müller, arXiv:1006.2047, Section 4.1, give the qualitative inclination criterion for complex Hilbert spaces and at least two subspaces. The quantitative remark in Section 4.2 gives the factor sqrt(1-ell squared divided by m squared). The elementary energy and displacement proofs also cover real scalars and the listed degenerate cases.

## References

- Truth anchor: `D5/S3/HilbertOperators/CyclicProjectionRate.LinearRegular`
- Truth anchor: `D5/S3/HilbertOperators/CyclicProjectionRate.geometric_rate`
- Truth anchor: `D5/S3/HilbertOperators/CyclicProjectionRate.linear_regular_iff_uniform_geometric`
- Dependency: [D5/S3/HilbertOperators/FiniteCyclicProjectionStrong](FiniteCyclicProjectionStrong.md)
