# Whole boundary factor deletion

## Abstract

Deleting a linear factor through an interior point on the entire convex boundary.

Let E be a real normed vector space, B a convex subset, and a an interior point of B. Let L be a nonzero continuous real linear functional and g a continuous real function on E. If L(x-a)g(x) vanishes at every boundary point of B, then g vanishes at every boundary point of B. Compactness, finite dimension and differentiability of the boundary are unnecessary for this implication.

**Theorem 1.1 (A hyperplane through an interior point contributes no indispensable boundary factor).**

$$\forall E \in RealNormedVectorSpace,\; \forall B \in Set\left(E\right),\; \forall a \in E,\; \forall L \in ContinuousLinearMap\left(Real, E, Real\right),\; \forall g \in Function\left(E, Real\right),\; \left(Convex\left(Real, B\right) \land \left(a \in interior\left(B\right) \land \left(Nonzero\left(L\right) \land \left(Continuous\left(g\right) \land \left(\forall x \in E,\; x \in frontier\left(B\right) \Rightarrow mul\left(L\left(sub\left(x, a\right)\right), g\left(x\right)\right) = 0\right)\right)\right)\right)\right) \Rightarrow \left(\forall x \in E,\; x \in frontier\left(B\right) \Rightarrow g\left(x\right) = 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlgebraicBoundary/InteriorFactorDeletion.whole_boundary_factor_delete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Translate a to the origin and write mu for the convex gauge of B. The gauge is continuous and equals one exactly on the boundary. At a boundary point b with L(b)=0, choose v with L(v) nonzero. For all sufficiently small nonzero real t, mu(b+tv) is positive and z(t)=(b+tv)/mu(b+tv) belongs to the boundary. Its L value is nonzero, so g(z(t))=0. Since z(t) tends to b, continuity gives g(b)=0. At a boundary point with L(b) nonzero, cancellation gives the result directly. This argument also includes a one-dimensional ambient space.

For a polynomial factorization f(x)=L(x-a)g(x), polynomial continuity supplies the hypothesis on g. Thus the factor can be deleted from an equation of the entire boundary. This implication does not assert the existence of that factorization, the nonvanishing of the derivative at an interior zero, a principal boundary ideal, or a hyperbolic branch representation.

## References

- Truth anchor: `D5/S3/Geometry/AlgebraicBoundary/InteriorFactorDeletion.whole_boundary_factor_delete`
