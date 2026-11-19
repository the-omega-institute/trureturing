# Degree-zero persistent heat stability

## Abstract

Pairwise heat stability of the degree-zero weighted persistent Laplacian.

**Definition 1.1 (The weighted persistent vertex operator).**

Lean statement: `D5/S3/Geometry/PersistentLaplacianHeatStability.persistentLaplacian`

*Formalization.* `D5/S3/Geometry/PersistentLaplacianHeatStability.persistentLaplacian` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For finite simplicial complexes K contained in L on a linearly ordered vertex type, take the real coordinates of the integer ordered edge boundary of L. An increasing edge contributes its two signed vertex deletions. Multiply the column of each edge by the square root of its weight and divide the row of each vertex by the square root of its weight. Let B and C be the resulting retained and hidden rows. Restrict B to the kernel of C to obtain T. The degree-zero unaugmented persistent Laplacian is S = TT*, equivalently B times the orthogonal projection onto the kernel of C times B*.

**Theorem 1.2 (Comparison at two positive times).**

$$\left\lVert \operatorname{exp}\left(-u S'\right) - \operatorname{exp}\left(-t S\right) \right\rVert \le \frac{M-1}{M+1}$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/PersistentLaplacianHeatStability.weighted_persistent_heat_stability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use one fixed positive retained vertex weight system, any two positive hidden vertex weight systems, and positive edge weights w and w' on L. For t,u > 0 and M ≥ 1, assume for each edge e that t w(e) divided by M is at most u w'(e), which is at most M t w(e). Here S and S' are the corresponding persistent Laplacians on the same retained Euclidean coordinates. The norm is the Euclidean operator norm. Singular hidden blocks and empty face sets are included.

The quadratic form of S is the squared distance from B*x to the range of C*. The hidden vertex factors are invertible row scalings, so their adjoints can be absorbed into the variable of the distance minimization. Comparing the same trial vector with effective edge weights t w and u w' gives the two Löwner bounds.

The two positive forms from the Löwner bounds yield a mixed quadratic estimate between the two generators. Apply it to the derivative of the product with one heat factor running forward and the other backward. Cauchy–Schwarz in time bounds the pairing by the product of heat energies. Each energy keeps its endpoint norm term. For a unit vector the two heat expectations are nonnegative, so the larger endpoint norm bounds their absolute difference. Substitution into the energy bound and the self-adjoint Rayleigh formula give the stated constant.

## References

- Truth anchor: `D5/S3/Geometry/PersistentLaplacianHeatStability.persistentLaplacian`
- Truth anchor: `D5/S3/Geometry/PersistentLaplacianHeatStability.weighted_persistent_heat_stability`
- Dependency: [D5/S3/Geometry/FiniteSimplicialSingularHomology](FiniteSimplicialSingularHomology.md)
