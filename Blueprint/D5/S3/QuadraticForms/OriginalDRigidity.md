# The first rigidity boundary for the original relation

## Abstract

The common two-label Hermitian boundary forces scalar skew symmetry of the old response relation.

**Theorem 1.1 (Hermitian response tables force skew symmetry).**

$$\forall (E : \operatorname{Type}\left(\right)), [\operatorname{AddCommGroup}\left(E\right)] [\operatorname{Module}\left(\mathbb{R}, E\right)], \forall (S : \operatorname{LinearMap}\left(\mathbb{R}, E, \operatorname{LinearMap}\left(\mathbb{R}, E, E\right)\right)), \forall (D : \operatorname{Function}\left(E, \operatorname{Function}\left(E, E\right)\right)), \forall (alpha : \operatorname{LinearMap}\left(\mathbb{R}, E, \mathbb{R}\right)), (\forall (x : E), \forall (y : E), \operatorname{S}\left(x, y\right) = \operatorname{S}\left(y, x\right)) \land (\operatorname{ThreeLabelPSD}\left(S, D, alpha\right)) \Rightarrow \forall (x : E), \forall (y : E), \operatorname{alpha}\left(\operatorname{D}\left(y, x\right)\right) = -\operatorname{alpha}\left(\operatorname{D}\left(x, y\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/OriginalDRigidity.three_label_skew` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

E is an arbitrary real module. S is the fixed real-bilinear symmetric part, D is still an arbitrary total relation, and alpha is one real-linear separating evaluation. ThreeLabelPSD requires the same response matrix to be positive semidefinite for every label list of order at most three, including zero, repeated and singular lists.

The response entry is alpha(S a b) minus i times alpha(D a b). Positive semidefinite matrices are Hermitian, so the two off-diagonal entries are conjugates. Since the S contribution is real and symmetric, their imaginary parts give alpha(D b a) = -alpha(D a b), including the diagonal zero case. No mass, Gram determinant, finite-dimensionality or regularity assumption is introduced.

The complete C128 source theorem additionally quantifies every original separating evaluation over the same old vector-valued D, assumes the common tables for every order from one through three and every zero, repeated, scaled and translated label list, and concludes alternating real-bilinearity of D together with all finite positive semidefiniteness of each scalar kernel. Those fixed-background, separation, singular-case and all-finite clauses remain the source context and target boundary for the unfinished cross-plane translation step.

This node records only that verified skew boundary. It does not claim additivity or real homogeneity of D, the evaluation-separated vector-valued conclusion, or all finite-order positivity. Those require the unresolved cross-plane translation bridge from the original C128 source.

## References

- Truth anchor: `D5/S3/QuadraticForms/OriginalDRigidity.three_label_skew`
- Dependency: [D5/S3/QuadraticForms/ParallelogramConstruction](ParallelogramConstruction.md)
