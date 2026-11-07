# Colourful Carathéodory theorem

## Abstract

One representative per label preserves a common convex hull point.

For a natural number d, E(d) denotes the native real Euclidean space EuclideanSpace Real (Fin d), and I(d) denotes Fin (d+1). Set(E(d)) is the set of all subsets of E(d). The operator convexHull below is convexHull Real, and range is the image of a function on its entire domain.

**Theorem 1.1 (Labelled convex hull selection in every dimension).**

$$\forall d \in Nat,\; \forall p \in E\left(d\right),\; \forall S \in I\left(d\right) \to Set\left(E\left(d\right)\right),\; \left(\forall i \in I\left(d\right),\; p \in convexHull\left(S\left(i\right)\right)\right) \Rightarrow \left(\exists f \in I\left(d\right) \to E\left(d\right),\; \left(\forall i \in I\left(d\right),\; f\left(i\right) \in S\left(i\right)\right) \land p \in convexHull\left(range\left(f\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/ColourfulCaratheodory.colourful_caratheodory` (`✓ std3`). ∎

*Citation.* Imre Bárány (1982). *A generalization of Carathéodory's theorem*. DOI: [10.1016/0012-365X(82)90115-7](https://doi.org/10.1016/0012-365X(82)90115-7). URL: <https://users.renyi.hu/~barany/cikkek/9.pdf>.

*Commentary.*

For every natural d, every point p of E(d), and every family S indexed by I(d) of arbitrary subsets of E(d), assume p belongs to the real convex hull of S(i) for every label i. There exists a function f on all labels such that f(i) belongs to S(i) for every i and p belongs to the real convex hull of range(f). The sets may be infinite and may overlap. The representatives may coincide, and convex coefficients may vanish. There is no compactness, closedness, boundedness, affine independence or general position hypothesis. Dimension zero is included.

Translate p to zero and extract a finite nonempty subset from each original hull membership. The union of the convex hulls of all choices from these finite labelled subsets is a nonempty finite union of compact sets. Minimize the Euclidean norm on that union, obtaining q in one selected hull.

If q is nonzero, the projection inequality gives inner(q,z) at least inner(q,q) for every point z of this hull. Take a positive affinely independent representation of q. The weighted inequalities sum to equality, so every support point lies at the supporting level inner(q,q). That level is positive; applying the inner product to a linear relation shows its coefficient sum is zero. Affine independence then makes the support linearly independent. It has at most d members and therefore omits a label among the d+1 colours.

The omitted colour has zero in its convex hull, so some point x of that colour has inner(q,x) strictly less than inner(q,q). Change only that representative. All support points remain in the new selected hull, which still contains q and now contains x. The projection characterization implies that some point r in this same new hull has norm strictly less than the norm of q. This contradicts the chosen global minimum. Thus q is zero. Translate the selected representatives back to obtain the stated selection for p.

Bárány's Theorem 2.1 on printed page 141 states the classical colourful selection theorem for arbitrary subsets of real Euclidean space. Ordinary Carathéodory, compactness of finite convex hulls, the finite-dimensional independence bound and the Hilbert projection characterization supply the standard ingredients.

## References

- Truth anchor: `D5/S3/Geometry/ColourfulCaratheodory.colourful_caratheodory`
