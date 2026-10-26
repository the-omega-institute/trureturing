# Tournament Hessian: derivative

## Abstract

Regular tournament Hessians: derivative.

**Theorem 1.1 (Smoothness of the determinant polynomial).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; \operatorname {ContDiff}\left(\mathbb {C}, 2, \operatorname {K}\left(A\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Derivative.polynomialSmooth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The permutation expansion of the determinant expresses K as a finite sum of products of affine coordinate functions. It is complex C2 everywhere.

**Theorem 1.2 (A local solution from the implicit function theorem).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; (3 \le d) \Rightarrow ((\operatorname {IsRegularTournament}\left(A\right)) \Rightarrow ((\operatorname {ContinuousLinearMap.IsInvertible}\left(\operatorname {ContinuousLinearMap.comp}\left(\operatorname {fderiv}\left(\mathbb {C}, (p: \operatorname {Prod}\left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C}, \mathbb {C}\right)\mapsto \operatorname {K}\left(A, \operatorname {appendLast}\left(\operatorname {Prod.fst}\left(p\right), \operatorname {Prod.snd}\left(p\right)\right)\right)), \operatorname {Prod.mk}\left(\operatorname {Function.const}\left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right), \operatorname {z}\left(d\right)\right), \operatorname {z}\left(d\right)\right)\right), \operatorname {ContinuousLinearMap.inr}\left(\mathbb {C}, \operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C}, \mathbb {C}\right)\right)\right)) \Rightarrow (\exists h \in \left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C}\right) \to \mathbb {C},\; \operatorname {IsLocalSolution}\left(A, h\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Derivative.localSolutionOfInvertible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the final-coordinate derivative at the expansion point is invertible, the complex implicit function theorem gives a C2 local solution. The zero value follows from the preceding determinant identity. This statement retains the invertibility hypothesis.

## Coordinate derivatives and local existence

**Theorem 1.3 (Appending coordinates is complex linear).**

$$\forall d \in \mathbb {N},\; \forall p \in \operatorname {Prod}\left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C}, \mathbb {C}\right),\; \operatorname {appendLastLinear}\left(d\right)\left(p\right) = \operatorname {appendLast}\left(\operatorname {Prod.fst}\left(p\right), \operatorname {Prod.snd}\left(p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Derivative.appendLastLinearApply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The continuous complex linear map appendLastLinear appends the second component after the coordinates of the first component.

**Theorem 1.4 (Changing the final coordinate).**

$$\forall d \in \mathbb {N},\; (1 \le d) \Rightarrow (\forall t \in \mathbb {C},\; \operatorname {appendLast}\left(\operatorname {Function.const}\left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right), \operatorname {z}\left(d\right)\right), t\right) = \operatorname {Function.update}\left(\operatorname {Function.const}\left(\operatorname {Fin}\left(d\right), \operatorname {z}\left(d\right)\right), \operatorname {Fin.mk}\left(d - 1\right), t\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Derivative.appendLast_update` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive d, appending t to the constant vector replaces precisely the coordinate with natural value d minus one.

**Theorem 1.5 (Differentiating a single column).**

$$\forall iota \in Type,\; [\operatorname {Fintype}\left(iota\right)] [\operatorname {DecidableEq}\left(iota\right)] \forall B \in \operatorname {Matrix}\left(iota, iota, \mathbb {C}\right),\; \forall j \in iota,\; \forall u \in iota \to \mathbb {C},\; \forall v \in iota \to \mathbb {C},\; \forall t \in \mathbb {C},\; \operatorname {HasDerivAt}\left((s: \mathbb {C}\mapsto \operatorname {Matrix.det}\left(\operatorname {Matrix.updateCol}\left(B, j, u + s\cdot (v)\right)\right)), \operatorname {Matrix.det}\left(\operatorname {Matrix.updateCol}\left(B, j, v\right)\right), t\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Derivative.determinant_column_deriv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multilinearity makes the determinant affine in the scalar multiplying one column. Its derivative is the determinant with that column replaced by its direction.

**Theorem 1.6 (A coordinate derivative of K).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; \forall y \in \operatorname {Fin}\left(d\right) \to \mathbb {C},\; \forall j \in \operatorname {Fin}\left(d\right),\; \forall t \in \mathbb {C},\; \operatorname {HasDerivAt}\left((s: \mathbb {C}\mapsto \operatorname {K}\left(A, \operatorname {Function.update}\left(y, j, s\right)\right)), -\operatorname {Matrix.det}\left(\operatorname {Matrix.updateCol}\left(1 - \left(\frac{1}{2}\cdot (1) + \operatorname {Matrix.map}\left(\operatorname {adjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right)\right) \cdot \operatorname {Matrix.diagonal}\left(y\right), j, (i: \operatorname {Fin}\left(d\right)\mapsto \left(\frac{1}{2}\cdot (1) + \operatorname {Matrix.map}\left(\operatorname {adjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right)\right)\left(i, j\right))\right)\right), t\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Derivative.K_coordinate_deriv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The derivative in coordinate j is minus the determinant obtained by replacing column j of the defining matrix by column j of one half I plus A. This holds at every y.

**Theorem 1.7 (Invertibility in one complex dimension).**

$$\forall L \in \operatorname {ContinuousLinearMap}\left(\mathbb {C}, \mathbb {C}, \mathbb {C}\right),\; (L\left(1\right) \ne 0) \Rightarrow (\operatorname {ContinuousLinearMap.IsInvertible}\left(L\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Derivative.scalar_map_invertible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A complex linear map on the scalar field multiplies by its value at one. The reciprocal scalar defines a continuous linear inverse when that value is nonzero.

**Theorem 1.8 (A nonzero scalar partial derivative).**

$$\forall E \in Type,\; [\operatorname {NormedAddCommGroup}\left(E\right)] [\operatorname {NormedSpace}\left(\mathbb {C}, E\right)] \forall F \in \operatorname {Prod}\left(E, \mathbb {C}\right) \to \mathbb {C},\; \forall y \in E,\; \forall t \in \mathbb {C},\; \forall c \in \mathbb {C},\; (\operatorname {DifferentiableAt}\left(\mathbb {C}, F, \operatorname {Prod.mk}\left(y, t\right)\right)) \Rightarrow ((\operatorname {HasDerivAt}\left((s: \mathbb {C}\mapsto F\left(\operatorname {Prod.mk}\left(y, s\right)\right)), c, t\right)) \Rightarrow ((c \ne 0) \Rightarrow (\operatorname {ContinuousLinearMap.IsInvertible}\left(\operatorname {ContinuousLinearMap.comp}\left(\operatorname {fderiv}\left(\mathbb {C}, F, \operatorname {Prod.mk}\left(y, t\right)\right), \operatorname {ContinuousLinearMap.inr}\left(\mathbb {C}, E, \mathbb {C}\right)\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Derivative.scalar_partial_invertible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Composing the full derivative with the inclusion of the scalar coordinate gives a complex linear map whose value at one is the scalar partial derivative.

**Theorem 1.9 (The rank-one determinant identity).**

$$\forall d \in \mathbb {N},\; \forall Q \in \operatorname {Matrix}\left(\operatorname {Fin}\left(d\right), \operatorname {Fin}\left(d\right), \mathbb {C}\right),\; (\operatorname {Matrix.det}\left(Q\right) \ne 0) \Rightarrow (\operatorname {Matrix.det}\left(Q - \operatorname {Matrix.of}\left((i: \operatorname {Fin}\left(d\right)\mapsto (j: \operatorname {Fin}\left(d\right)\mapsto 1))\right)\right) = \operatorname {Matrix.det}\left(Q\right) \cdot \left(1 - \sum_{i: \operatorname {Fin}\left(d\right)} \sum_{j: \operatorname {Fin}\left(d\right)} \operatorname {Inv.inv}\left(Q\right)\left(i, j\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Derivative.det_rank_one_sub` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The matrix determinant lemma evaluates subtraction of the all-ones matrix. Its correction factor is one minus the sum of all entries of the inverse.

**Theorem 1.10 (Completeness and skew adjacency).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; (\operatorname {IsRegularTournament}\left(A\right)) \Rightarrow (2\cdot (\frac{1}{2}\cdot (1) + \operatorname {Matrix.map}\left(\operatorname {adjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right)) = \operatorname {Matrix.of}\left((i: \operatorname {Fin}\left(d\right)\mapsto (j: \operatorname {Fin}\left(d\right)\mapsto 1))\right) + \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Derivative.tournamentCoefficientIdentity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Tournament completeness gives twice the coefficient matrix as the sum of the all-ones matrix and the skew adjacency matrix.

**Theorem 1.11 (A resolvent factorization of K).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; (\operatorname {IsRegularTournament}\left(A\right)) \Rightarrow (\forall y \in \operatorname {Fin}\left(d\right) \to \mathbb {C},\; (\forall j \in \operatorname {Fin}\left(d\right),\; y\left(j\right) \ne 0) \Rightarrow ((\operatorname {Matrix.det}\left(\operatorname {Matrix.diagonal}\left((j: \operatorname {Fin}\left(d\right)\mapsto \frac{2}{y\left(j\right)})\right) - \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right)\right) \ne 0) \Rightarrow (\operatorname {K}\left(A, y\right) = \operatorname {Matrix.det}\left(\operatorname {Matrix.diagonal}\left((j: \operatorname {Fin}\left(d\right)\mapsto \frac{2}{y\left(j\right)})\right) - \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right)\right) \cdot \left(1 - \sum_{i: \operatorname {Fin}\left(d\right)} \sum_{j: \operatorname {Fin}\left(d\right)} \operatorname {Inv.inv}\left(\operatorname {Matrix.diagonal}\left((j: \operatorname {Fin}\left(d\right)\mapsto \frac{2}{y\left(j\right)})\right) - \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right)\right)\left(i, j\right)\right) \cdot \prod_{j: \operatorname {Fin}\left(d\right)} \frac{y\left(j\right)}{2})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Derivative.K_resolvent_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When every coordinate and the resolvent determinant are nonzero, factor the defining matrix as the resolvent minus the all-ones matrix, followed by the diagonal matrix with entries y divided by two. The rank-one determinant identity then gives this formula.

**Theorem 1.12 (The equation as an inverse-entry sum).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; (\operatorname {IsRegularTournament}\left(A\right)) \Rightarrow (\forall y \in \operatorname {Fin}\left(d\right) \to \mathbb {C},\; (\forall j \in \operatorname {Fin}\left(d\right),\; y\left(j\right) \ne 0) \Rightarrow ((\operatorname {Matrix.det}\left(\operatorname {Matrix.diagonal}\left((j: \operatorname {Fin}\left(d\right)\mapsto \frac{2}{y\left(j\right)})\right) - \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right)\right) \ne 0) \Rightarrow ((\operatorname {K}\left(A, y\right) = 0) \Leftrightarrow (\sum_{i: \operatorname {Fin}\left(d\right)} \sum_{j: \operatorname {Fin}\left(d\right)} \operatorname {Inv.inv}\left(\operatorname {Matrix.diagonal}\left((j: \operatorname {Fin}\left(d\right)\mapsto \frac{2}{y\left(j\right)})\right) - \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right)\right)\left(i, j\right) = 1))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Derivative.K_eq_zero_iff_resolvent_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The nonzero determinant and coordinate-product factors can be cancelled. Thus K vanishes exactly when the sum of all entries of the resolvent inverse equals one.

**Theorem 1.13 (The inverse-entry equation near the base point).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; (3 \le d) \Rightarrow ((\operatorname {IsRegularTournament}\left(A\right)) \Rightarrow (\forall h \in \left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C}\right) \to \mathbb {C},\; (\operatorname {IsLocalSolution}\left(A, h\right)) \Rightarrow ((\operatorname {Matrix.det}\left(\operatorname {Matrix.diagonal}\left((j: \operatorname {Fin}\left(d\right)\mapsto \frac{2}{\operatorname {Function.const}\left(\operatorname {Fin}\left(d\right), \operatorname {z}\left(d\right)\right)\left(j\right)})\right) - \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right)\right) \ne 0) \Rightarrow (\operatorname {Filter.Eventually}\left((y: \operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C}\mapsto \sum_{i: \operatorname {Fin}\left(d\right)} \sum_{j: \operatorname {Fin}\left(d\right)} \operatorname {Inv.inv}\left(\operatorname {Matrix.diagonal}\left((j: \operatorname {Fin}\left(d\right)\mapsto \frac{2}{\operatorname {appendLast}\left(y, h\left(y\right)\right)\left(j\right)})\right) - \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right)\right)\left(i, j\right) = 1), \operatorname {nhds}\left(\operatorname {Function.const}\left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right), \operatorname {z}\left(d\right)\right)\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Derivative.localSolution_resolvent_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Continuity keeps the coordinates and the resolvent determinant nonzero near the base point. Every C2 local solution therefore satisfies the inverse-entry equation on a neighbourhood.

**Theorem 1.14 (Existence of the analytic local solution).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; (3 \le d) \Rightarrow ((\operatorname {IsRegularTournament}\left(A\right)) \Rightarrow (\exists h \in \left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C}\right) \to \mathbb {C},\; \operatorname {IsLocalSolution}\left(A, h\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Derivative.regularLocalSolution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact coordinate derivative is nonzero by strict diagonal dominance of the shifted skew adjacency matrix. Its scalar continuous linear derivative is invertible, so the complex implicit function theorem gives the required C2 local solution.

## Cofactors and the nonzero coordinate derivative

**Theorem 1.15 (The determinant of a constant perturbation).**

$$\forall n \in \mathbb {N},\; \forall c \in \mathbb {C},\; \operatorname {Matrix.det}\left(1 + \operatorname {Matrix.of}\left((i: \operatorname {Fin}\left(n\right)\mapsto (j: \operatorname {Fin}\left(n\right)\mapsto c))\right)\right) = 1 + \operatorname {Nat.cast}\left(n\right) \cdot c$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Derivative.det_const_perturb` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The matrix determinant lemma reduces a constant perturbation of the identity to one scalar. The determinant is one plus the sum of the constant diagonal contributions.

**Theorem 1.16 (A column replacement in the constant-vector projection).**

$$\forall n \in \mathbb {N},\; \forall l \in \operatorname {Fin}\left(n + 1\right),\; \forall v \in \operatorname {Fin}\left(n + 1\right) \to \mathbb {C},\; \operatorname {Matrix.det}\left(\operatorname {Matrix.updateCol}\left(1 - \operatorname {Matrix.of}\left((i: \operatorname {Fin}\left(n + 1\right)\mapsto (j: \operatorname {Fin}\left(n + 1\right)\mapsto \frac{1}{\operatorname {Nat.cast}\left(n\right) + 1}))\right), l, v\right)\right) = \frac{\sum_{i: \operatorname {Fin}\left(n + 1\right)} v\left(i\right)}{\operatorname {Nat.cast}\left(n\right) + 1}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Derivative.det_projection_update` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let P=I−J/(n+1), where every entry of J is one. Replacing column l by v gives determinant equal to the sum of the coordinates of v divided by n+1. Summing the rows and expanding the resulting sparse row leaves a principal minor with determinant 1/(n+1).

**Theorem 1.17 (A cofactor of a centered doubly stochastic matrix).**

$$\forall n \in \mathbb {N},\; \forall l \in \operatorname {Fin}\left(n + 1\right),\; \forall A \in \operatorname {Matrix}\left(\operatorname {Fin}\left(n + 1\right), \operatorname {Fin}\left(n + 1\right), \mathbb {C}\right),\; (\operatorname {Matrix.det}\left(A\right) \ne 0) \Rightarrow ((\forall i \in \operatorname {Fin}\left(n + 1\right),\; \sum_{j: \operatorname {Fin}\left(n + 1\right)} A\left(i, j\right) = 1) \Rightarrow ((\forall j \in \operatorname {Fin}\left(n + 1\right),\; \sum_{i: \operatorname {Fin}\left(n + 1\right)} A\left(i, j\right) = 1) \Rightarrow (\operatorname {Matrix.det}\left(\operatorname {Matrix.updateCol}\left(A - \operatorname {Matrix.of}\left((i: \operatorname {Fin}\left(n + 1\right)\mapsto (j: \operatorname {Fin}\left(n + 1\right)\mapsto \frac{1}{\operatorname {Nat.cast}\left(n\right) + 1}))\right), l, \operatorname {Pi.single}\left(l, 1\right)\right)\right) = \frac{\operatorname {Matrix.det}\left(A\right)}{\operatorname {Nat.cast}\left(n\right) + 1})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Derivative.det_doubly_stochastic_cofactor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An invertible complex matrix whose rows and columns sum to one factors its centered matrix as A(I−J/(n+1)). The inverse image of the lth coordinate vector has coordinate sum one. The projection column formula therefore gives det A divided by n+1.

**Theorem 1.18 (A cofactor of a matrix with zero row and column sums).**

$$\forall n \in \mathbb {N},\; \forall l \in \operatorname {Fin}\left(n + 1\right),\; \forall B \in \operatorname {Matrix}\left(\operatorname {Fin}\left(n + 1\right), \operatorname {Fin}\left(n + 1\right), \mathbb {C}\right),\; (\operatorname {Matrix.det}\left(B + \operatorname {Matrix.of}\left((i: \operatorname {Fin}\left(n + 1\right)\mapsto (j: \operatorname {Fin}\left(n + 1\right)\mapsto \frac{1}{\operatorname {Nat.cast}\left(n\right) + 1}))\right)\right) \ne 0) \Rightarrow ((\forall i \in \operatorname {Fin}\left(n + 1\right),\; \sum_{j: \operatorname {Fin}\left(n + 1\right)} B\left(i, j\right) = 0) \Rightarrow ((\forall j \in \operatorname {Fin}\left(n + 1\right),\; \sum_{i: \operatorname {Fin}\left(n + 1\right)} B\left(i, j\right) = 0) \Rightarrow (\operatorname {Matrix.det}\left(\operatorname {Matrix.updateCol}\left(B, l, \operatorname {Pi.single}\left(l, 1\right)\right)\right) = \frac{\operatorname {Matrix.det}\left(B + \operatorname {Matrix.of}\left((i: \operatorname {Fin}\left(n + 1\right)\mapsto (j: \operatorname {Fin}\left(n + 1\right)\mapsto \frac{1}{\operatorname {Nat.cast}\left(n\right) + 1}))\right)\right)}{\operatorname {Nat.cast}\left(n\right) + 1})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Derivative.cofactor_eq_of_zero_sums` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Adding J/(n+1) to B changes every row and column sum from zero to one. If the resulting determinant is nonzero, each diagonal cofactor of B equals that determinant divided by n+1.

**Theorem 1.19 (The common first-coordinate determinant coefficient).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; (3 \le d) \Rightarrow ((\operatorname {IsRegularTournament}\left(A\right)) \Rightarrow (\forall l \in \operatorname {Fin}\left(d\right),\; \operatorname {Matrix.det}\left(\operatorname {Matrix.updateCol}\left(1 - \left(\frac{1}{2}\cdot (1) + \operatorname {Matrix.map}\left(\operatorname {adjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right)\right) \cdot \operatorname {Matrix.diagonal}\left(\operatorname {Function.const}\left(\operatorname {Fin}\left(d\right), \operatorname {z}\left(d\right)\right)\right), l, (i: \operatorname {Fin}\left(d\right)\mapsto \left(\frac{1}{2}\cdot (1) + \operatorname {Matrix.map}\left(\operatorname {adjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right)\right)\left(i, l\right))\right)\right) = \frac{\operatorname {Matrix.det}\left(\operatorname {Nat.cast}\left(d\right)\cdot (1) - \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right)\right)}{2 \cdot \operatorname {Nat.cast}\left(d\right)^{d}}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Derivative.regularColumnSlopeValue` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Put C=½I+A and B=I−CD_z. Regularity gives zero row and column sums for B and the factorization B+J/d=(dI−S)/d. Every determinant obtained by replacing column l of B with column l of C equals det(dI−S)/(2d^d), independently of l. The coordinate derivative of K is the negative of this column replacement determinant.

**Theorem 1.20 (Regular skew adjacency has zero row sums).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; (3 \le d) \Rightarrow ((\operatorname {IsRegularTournament}\left(A\right)) \Rightarrow (\forall i \in \operatorname {Fin}\left(d\right),\; \sum_{j: \operatorname {Fin}\left(d\right)} \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right)\left(i, j\right) = 0))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Derivative.regularSkewRowSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pair completeness and constant out-degree imply the same in-degree at every vertex. Subtracting the transpose therefore gives zero in every skew adjacency row sum.

**Theorem 1.21 (Regular skew adjacency has zero column sums).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; (3 \le d) \Rightarrow ((\operatorname {IsRegularTournament}\left(A\right)) \Rightarrow (\forall j \in \operatorname {Fin}\left(d\right),\; \sum_{i: \operatorname {Fin}\left(d\right)} \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right)\left(i, j\right) = 0))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Derivative.regularSkewColSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Skew symmetry identifies each column sum with the negative of the corresponding row sum. The zero row sums thus give zero column sums as well.

**Theorem 1.22 (The negative skew shift is nonsingular).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; \operatorname {Matrix.det}\left(\operatorname {Nat.cast}\left(d\right)\cdot (1) - \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right)\right) \ne 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Derivative.shiftedNegativeDetNeZero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The matrix dI−S is the transpose of S+dI. Its determinant equals the nonzero determinant furnished by strict diagonal dominance. This assertion does not require tournament regularity.

## Second variations

**Theorem 1.23 (The Hessian from a scalar implicit equation).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; \forall h \in \left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C}\right) \to \mathbb {C},\; \forall L \in \operatorname {ContinuousLinearMap}\left(\mathbb {C}, \operatorname {Prod}\left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C}, \mathbb {C}\right), \operatorname {Fin}\left(d\right) \to \mathbb {C}\right),\; \forall alpha \in \left(\operatorname {Fin}\left(d\right) \to \mathbb {C}\right) \to \mathbb {C},\; \forall c \in \mathbb {C},\; (3 \le d) \Rightarrow ((\operatorname {IsLocalSolution}\left(A, h\right)) \Rightarrow ((\operatorname {ContDiffAt}\left(\mathbb {C}, 2, alpha, L\left(\operatorname {Prod.mk}\left(\operatorname {Function.const}\left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right), \operatorname {z}\left(d\right)\right), \operatorname {z}\left(d\right)\right)\right)\right)) \Rightarrow ((\operatorname {Filter.EventuallyEq}\left(\operatorname {nhds}\left(\operatorname {Function.const}\left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right), \operatorname {z}\left(d\right)\right)\right), (y: \operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C}\mapsto alpha\left(L\left(\operatorname {Prod.mk}\left(y, h\left(y\right)\right)\right)\right)), (y: \operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C}\mapsto 1)\right)) \Rightarrow ((c \ne 0) \Rightarrow ((\forall j \in \operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right),\; \operatorname {fderiv}\left(\mathbb {C}, alpha, L\left(\operatorname {Prod.mk}\left(\operatorname {Function.const}\left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right), \operatorname {z}\left(d\right)\right), \operatorname {z}\left(d\right)\right)\right), L\left(\operatorname {Prod.mk}\left(\operatorname {Pi.single}\left(j, 1\right), 0\right)\right)\right) = c) \Rightarrow ((\operatorname {fderiv}\left(\mathbb {C}, alpha, L\left(\operatorname {Prod.mk}\left(\operatorname {Function.const}\left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right), \operatorname {z}\left(d\right)\right), \operatorname {z}\left(d\right)\right)\right), L\left(\operatorname {Prod.mk}\left(0, 1\right)\right)\right) = c) \Rightarrow (\forall j \in \operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right),\; \forall k \in \operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right),\; \operatorname {hessian}\left(h, j, k\right) = 1 + \operatorname {ite}\left(j = k, 1, 0\right) + \frac{\operatorname {z}\left(d\right)}{c} \cdot \operatorname {second}\left(\mathbb {C}, alpha, L\left(\operatorname {Prod.mk}\left(\operatorname {Function.const}\left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right), \operatorname {z}\left(d\right)\right), \operatorname {z}\left(d\right)\right)\right), L\left(\operatorname {Prod.mk}\left(\operatorname {Pi.single}\left(j, 1\right), 0 - 1\right)\right), L\left(\operatorname {Prod.mk}\left(\operatorname {Pi.single}\left(k, 1\right), 0 - 1\right)\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Derivative.hessian_of_implicit_scalar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If a C2 scalar equation has a constant nonzero first partial c in every appended coordinate and is constant along the graph of h, then h_j=-1. The second implicit derivative and the angular formula give H_jk=1+delta_jk+(z/c) D2alpha(L(e_j,-1),L(e_k,-1)).

**Theorem 1.24 (The Hessian from the coordinate derivatives of the scalar equation).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; \forall h \in \left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C}\right) \to \mathbb {C},\; \forall L \in \operatorname {ContinuousLinearMap}\left(\mathbb {C}, \operatorname {Prod}\left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C}, \mathbb {C}\right), \operatorname {Fin}\left(d\right) \to \mathbb {C}\right),\; \forall alpha \in \left(\operatorname {Fin}\left(d\right) \to \mathbb {C}\right) \to \mathbb {C},\; \forall c \in \mathbb {C},\; \forall iota \in \operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \operatorname {Fin}\left(d\right),\; \forall last \in \operatorname {Fin}\left(d\right),\; \forall M \in \operatorname {Matrix}\left(\operatorname {Fin}\left(d\right), \operatorname {Fin}\left(d\right), \mathbb {C}\right),\; (3 \le d) \Rightarrow ((\operatorname {IsLocalSolution}\left(A, h\right)) \Rightarrow ((\operatorname {ContDiffAt}\left(\mathbb {C}, 2, alpha, L\left(\operatorname {Prod.mk}\left(\operatorname {Function.const}\left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right), \operatorname {z}\left(d\right)\right), \operatorname {z}\left(d\right)\right)\right)\right)) \Rightarrow ((\operatorname {Filter.EventuallyEq}\left(\operatorname {nhds}\left(\operatorname {Function.const}\left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right), \operatorname {z}\left(d\right)\right)\right), (y: \operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C}\mapsto alpha\left(L\left(\operatorname {Prod.mk}\left(y, h\left(y\right)\right)\right)\right)), (y: \operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C}\mapsto 1)\right)) \Rightarrow ((c \ne 0) \Rightarrow ((\forall j \in \operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right),\; L\left(\operatorname {Prod.mk}\left(\operatorname {Pi.single}\left(j, 1\right), 0\right)\right) = \operatorname {Pi.single}\left(iota\left(j\right), 1\right)) \Rightarrow ((L\left(\operatorname {Prod.mk}\left(0, 1\right)\right) = \operatorname {Pi.single}\left(last, 1\right)) \Rightarrow ((\forall i \in \operatorname {Fin}\left(d\right),\; \operatorname {fderiv}\left(\mathbb {C}, alpha, L\left(\operatorname {Prod.mk}\left(\operatorname {Function.const}\left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right), \operatorname {z}\left(d\right)\right), \operatorname {z}\left(d\right)\right)\right), \operatorname {Pi.single}\left(i, 1\right)\right) = c) \Rightarrow ((\forall i \in \operatorname {Fin}\left(d\right),\; \forall l \in \operatorname {Fin}\left(d\right),\; \operatorname {second}\left(\mathbb {C}, alpha, L\left(\operatorname {Prod.mk}\left(\operatorname {Function.const}\left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right), \operatorname {z}\left(d\right)\right), \operatorname {z}\left(d\right)\right)\right), \operatorname {Pi.single}\left(i, 1\right), \operatorname {Pi.single}\left(l, 1\right)\right) = M\left(i, l\right)) \Rightarrow (\forall j \in \operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right),\; \forall k \in \operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right),\; \operatorname {hessian}\left(h, j, k\right) = 1 + \operatorname {ite}\left(j = k, 1, 0\right) + \frac{\operatorname {z}\left(d\right)}{c} \cdot \left(M\left(iota\left(j\right), iota\left(k\right)\right) - M\left(iota\left(j\right), last\right) - M\left(last, iota\left(k\right)\right) + M\left(last, last\right)\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Derivative.hessian_of_implicit_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If M is the matrix of second complex partial derivatives of the scalar equation, the graph tangent vectors are coordinate differences. Bilinearity gives the four-entry difference M_jk-M_jd-M_dk+M_dd in the angular Hessian formula.

**Definition 1.25 (The continuous linear coordinate assembly).**

$$\forall d \in \mathbb {N},\; \forall p \in \operatorname {Prod}\left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C}, \mathbb {C}\right),\; \operatorname {appendLastLinear}\left(d\right)\left(p\right) = \operatorname {appendLast}\left(\operatorname {Prod.fst}\left(p\right), \operatorname {Prod.snd}\left(p\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/WormaldTournamentHessian/Derivative.appendLastLinear` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The continuous complex linear map takes (y,t) to appendLast y t.

## References

- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Derivative.K_coordinate_deriv`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Derivative.K_eq_zero_iff_resolvent_sum`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Derivative.K_resolvent_factorization`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Derivative.appendLastLinear`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Derivative.appendLastLinearApply`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Derivative.appendLast_update`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Derivative.cofactor_eq_of_zero_sums`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Derivative.det_const_perturb`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Derivative.det_doubly_stochastic_cofactor`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Derivative.det_projection_update`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Derivative.det_rank_one_sub`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Derivative.determinant_column_deriv`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Derivative.hessian_of_implicit_coordinates`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Derivative.hessian_of_implicit_scalar`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Derivative.localSolutionOfInvertible`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Derivative.localSolution_resolvent_eq`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Derivative.polynomialSmooth`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Derivative.regularColumnSlopeValue`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Derivative.regularLocalSolution`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Derivative.regularSkewColSum`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Derivative.regularSkewRowSum`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Derivative.scalar_map_invertible`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Derivative.scalar_partial_invertible`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Derivative.shiftedNegativeDetNeZero`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Derivative.tournamentCoefficientIdentity`
- Dependency: [D5/S3/Combinatorics/WormaldTournamentHessian/Algebra](Algebra.md)
