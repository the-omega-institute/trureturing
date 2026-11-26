# The integral slope inequality

## Abstract

Euclidean lattice maps and Harder-Narasimhan slopes

**Remark 1.1 (Integral maps in the frame slope argument).**

Lean statement: `D5/S3/Combinatorics/Lattices/EuclideanSlopeMorphism.slope_morphism`

*Formalization.* `D5/S3/Combinatorics/Lattices/EuclideanSlopeMorphism.slope_morphism` (`✓ std3`).

*Citation.* Levent Alpöge (2026). *Riemann hypothesis formalization in Lean*. URL: <https://github.com/the-omega-institute/riemann-hypothesis>.

*Commentary.*

Alpoge's TheoremFSharp uses maps into one common integral lattice to carry high source slopes into high target slopes. The underlying canonical filtration is the Euclidean lattice filtration described by Grayson. The theorem below uses one real embedding, integral rank, and minus the logarithm of the Gram covolume as degree.

**Theorem 1.2 (A nonzero integral map bounds the extreme slopes).**

Lean statement: `D5/S3/Combinatorics/Lattices/EuclideanSlopeMorphism.slope_morphism`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Lattices/EuclideanSlopeMorphism.slope_morphism` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel R. Grayson (1984). *Reduction theory using semistability*. DOI: [10.1007/BF02566369](https://doi.org/10.1007/BF02566369).

*Commentary.*

Let N and C be discrete integral submodules of finite dimensional real inner product spaces E and F. Let f be a real continuous linear map, and let A be a saturated section of N. Let B be a saturated section of C. Assume f(A) is contained in C, its image is not contained in the real span of B, and the projection of f away from the real span of B, restricted to the real span of A, has operator norm at most exp(h). Then the minimal HN slope of the source interval from zero to A is at most the maximal HN slope of the target interval from B to C plus h. Taking A equal to N and B equal to zero gives the full lattice assertion. Neither lattice is required to span its whole ambient space.

First compose f with the orthogonal projection onto the real span of A. This agrees with f on A and turns the restricted height bound into a bound on the whole source space. Project the target away from the real span of B. Intersect A with the real kernel of the resulting composite. This is a saturated integral sublattice K. Extend a basis of K to one of A. The images of the complementary basis form an integral basis modulo B for the sum of B and f(A). Orthogonal projection away from the real span of K separates the Gram determinant into the determinant of K and that of the projected complementary vectors. The projected map has the same values on these projected vectors. Its singular values are bounded by exp(h), so an image of rank r loses at most r times h in degree. Saturating the sum of B and f(A) inside C can only increase degree, since its positive integral index multiplies the covolume. The quotient and subobject extrema of the HN filtrations give the stated comparison.

The height contribution has coefficient one. The Gram determinant contributes twice the rank in its exponent, and the square root in the covolume removes this factor two. The real normalization is therefore h equal to log of the projected operator norm on the source span; a bound on the full operator norm suffices by orthogonal contraction. A convention using log of its square uses one half of that height in this comparison.

**Theorem 1.3 (The top saturated section has the original integral carrier).**

Lean statement: `D5/S3/Combinatorics/Lattices/EuclideanSlopeMorphism.integral_top`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Lattices/EuclideanSlopeMorphism.integral_top` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel R. Grayson (1984). *Reduction theory using semistability*. DOI: [10.1007/BF02566369](https://doi.org/10.1007/BF02566369).

*Commentary.*

For an integral submodule L of a finite-dimensional real inner product space, the integral carrier of its top saturated section equals L. This identity supplies the top endpoint in the morphism comparison and in the common lattice spectrum and mean estimates.

## References

- Truth anchor: `D5/S3/Combinatorics/Lattices/EuclideanSlopeMorphism.integral_top`
- Truth anchor: `D5/S3/Combinatorics/Lattices/EuclideanSlopeMorphism.slope_morphism`
- Truth anchor: `D5/S3/Combinatorics/Lattices/EuclideanSlopeMorphism.slope_morphism`
- Dependency: [D5/S3/Combinatorics/Lattices/EuclideanHarderNarasimhan](EuclideanHarderNarasimhan.md)
