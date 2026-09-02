# Minimal Relational Visibility

## Abstract

Two nonnegative Pick-kernel diagonal values can form an indefinite two-point relation.

**Theorem 1.1 (The first negative relation certificate has width two).**

$$\forall s: \mathbb{C} \to \mathbb{C}, a \in \mathbb{D}, (\operatorname{s}\left(0\right) = 0 \land \operatorname{s}\left(a\right) = 1) \Rightarrow \operatorname{let}(K := (z, w \mapsto \frac{1 - \operatorname{s}\left(z\right) \times \overline{\operatorname{s}\left(w\right)}}{1 - z \times \overline{w}}), p := \operatorname{vector}\left(0, a\right), R := (i, j \mapsto \operatorname{K}\left(\operatorname{p}\left(i\right), \operatorname{p}\left(j\right)\right)))\;R = \operatorname{matrix}\left(1, 1, 1, 0\right) \land (\forall i \in \{0, 1\}, 0 \leq \operatorname{R}\left(i, i\right)) \land \operatorname{det}\left(R\right) = -1 \land \neg\operatorname{PosSemidef}\left(R\right) \land \neg\exists A: \operatorname{Matrix}\left(2, 2, \mathbb{C}\right), R = \operatorname{conjTranspose}\left(A\right) \times A.$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/MinimalRelationalVisibility.minimal_relational_visibility` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let s be a complex Schur candidate and a an interior disk point, with s zero at the origin and one at a. The displayed kernel, point family, and relation matrix are the source constructions.

Both one-point diagonal tests are nonnegative. Sampling the two names together gives the matrix with rows (1,1) and (1,0), whose determinant is minus one and which is not positive semidefinite.

Every conjugate-transpose product is positive semidefinite, so the same certificate rules out a Gram factorization of the joint relation.

## References

- Truth anchor: `D5/S3/Weil/Pick/MinimalRelationalVisibility.minimal_relational_visibility`
