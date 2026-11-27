# The signed wrap hull and constant translates

## Abstract

The signed wrap hull is a linear image of the cross-polytope.

**Definition 1.1 (Absolute sum).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezWrapHull.absoluteSum`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezWrapHull.absoluteSum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Colin Olairez (2026). *Triangulation, Volume, and Symmetries of a Dihedral Group Analogue of the Permutohedron*. DOI: [10.48550/arXiv.2610.28672](https://doi.org/10.48550/arXiv.2610.28672). URL: <https://arxiv.org/html/2610.28672v2#S6.Thmquestion2>.

*Commentary.*

For a real vector z with coordinates indexed modulo a positive n, its absolute sum is the sum of the absolute values of its entries.

**Theorem 1.2 (Membership in the scaled wrap hull).**

$$\forall n,k \in \mathbb{N}, 0<n \implies \forall d \in H_{n}, d \in kC_{n} \iff \exists t \in \mathbb{R}, \sum_{i \in \mathbb{Z}_{n}} \left|d_{i}+t\right| \le nk$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezWrapHull.scaled_wrap_hull_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Colin Olairez (2026). *Triangulation, Volume, and Symmetries of a Dihedral Group Analogue of the Permutohedron*. DOI: [10.48550/arXiv.2610.28672](https://doi.org/10.48550/arXiv.2610.28672). URL: <https://arxiv.org/html/2610.28672v2#S6.Thmquestion2>.

*Commentary.*

This criterion supports the lattice-point count in Question 6.1 of Colin Olairez, arXiv:2610.28672v2, §6, printed p. 21. Source locator https://arxiv.org/html/2610.28672v2#S6.Thmquestion1 . For a positive natural n, Hₙ is the real sum-zero subspace. Cₙ is the convex hull in Hₙ of the signed wrap vectors ±(1 − neᵢ). The linear map u ↦ (∑ᵢ uᵢ)1 − nu sends the signed coordinate basis to these vectors.

The absolute-sum unit ball is the convex hull of the signed basis. One convex combination represents each point of the ball using its absolute coordinate values and assigns the remaining weight to zero. The linear map therefore takes the radius-k ball onto kCₙ. Over a sum-zero d, scaling its constant translates by −1/n gives all preimages. The zero dilation is the singleton at zero. Here k is any natural, including zero, and the assumption n > 0 supplies the nonzero divisor and nonempty index set.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezWrapHull.absoluteSum`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezWrapHull.scaled_wrap_hull_iff`
- Dependency: [D5/S3/Combinatorics/Geometry/Permutohedra/OlairezQ62](OlairezQ62.md)
