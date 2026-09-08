# Weighted Discrete Logarithmic Selection

## Abstract

Unequal coordinate weights select a unique positive definite integer matrix with unequal diagonal entries.

Let M be the set of all two by two integer matrices. For T in M, R(T) is its entrywise real cast, and P(T) means that R(T) is positive definite. Thus P(T) includes symmetry and strict positivity of the quadratic form on every nonzero real vector. The symbol I denotes the two by two real identity matrix.

**Definition 1.1 (The price window).**

$$\forall p \in \mathbb{R},\; \operatorname{W}\left(p\right) \Leftrightarrow \left(\left(\operatorname{log}\left(\frac{3}{2}\right) < 3 \cdot p \land 3 \cdot p < \operatorname{log}\left(2\right)\right) \land \left(\operatorname{log}\left(\frac{4}{3}\right) < 2 \cdot p \land 2 \cdot p < \operatorname{log}\left(\frac{3}{2}\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/GoldenResource/WeightedDiscreteLogNoGo.priceWindow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two effective prices are three times p and two times p.

**Definition 1.2 (The weighted objective).**

$$\forall p \in \mathbb{R}, T \in M,\; \operatorname{f}\left(p, T\right) = \operatorname{log}\left(\operatorname{det}\left(\operatorname{R}\left(T\right)\right)\right) - p \cdot \left(3 \cdot T\left(0, 0\right) + 2 \cdot T\left(1, 1\right)\right)$$

*Formalization.* `D5/S3/Arith/GoldenResource/WeightedDiscreteLogNoGo.objective` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All logarithms and arithmetic in the objective are real valued.

**Definition 1.3 (The selected matrix).**

$$D = \operatorname{diag}\left(2, 3\right)$$

*Formalization.* `D5/S3/Arith/GoldenResource/WeightedDiscreteLogNoGo.selectedMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The off-diagonal entries of D are zero.

**Theorem 1.4 (An explicit interior price).**

$$\left(\operatorname{log}\left(\frac{3}{2}\right) < 3 \cdot \frac{1}{6} \land 3 \cdot \frac{1}{6} < \operatorname{log}\left(2\right)\right) \land \left(\operatorname{log}\left(\frac{4}{3}\right) < 2 \cdot \frac{1}{6} \land 2 \cdot \frac{1}{6} < \operatorname{log}\left(\frac{3}{2}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/WeightedDiscreteLogNoGo.one_sixth_mem_priceWindow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive x different from one, log(x) is strictly less than x minus one. Applying this bound to three halves and four thirds gives the upper bounds. Applying it to the reciprocals of two and three halves gives the strict lower bounds.

**Theorem 1.5 (The price window is nonempty).**

$$\exists p \in \mathbb{R},\; \operatorname{W}\left(p\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/WeightedDiscreteLogNoGo.priceWindow_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One sixth is a witness.

**Theorem 1.6 (The candidate is positive definite).**

$$\operatorname{P}\left(D\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/WeightedDiscreteLogNoGo.selectedMatrix_posDef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A real diagonal matrix with diagonal entries two and three is positive definite.

**Theorem 1.7 (The integral off-diagonal loss).**

$$\forall T \in M,\; \left(\operatorname{P}\left(T\right) \land T\left(0, 1\right) \ne 0\right) \Rightarrow \operatorname{det}\left(\operatorname{R}\left(T\right)\right) \le T\left(0, 0\right) \cdot T\left(1, 1\right) - 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/WeightedDiscreteLogNoGo.off_diagonal_det_loss` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a symmetric two by two matrix the determinant is the diagonal product minus the square of the off-diagonal entry. A nonzero integer has square at least one.

**Theorem 1.8 (A unique global maximum).**

$$\forall p \in \mathbb{R}, T \in M,\; \left(\operatorname{W}\left(p\right) \land \operatorname{P}\left(T\right)\right) \Rightarrow \left(\operatorname{f}\left(p, T\right) \le \operatorname{f}\left(p, D\right) \land \left(T \ne D \Rightarrow \operatorname{f}\left(p, T\right) < \operatorname{f}\left(p, D\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/WeightedDiscreteLogNoGo.weighted_unique_maximum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The logarithm of the determinant is at most the sum of the diagonal logarithms, and the inequality is strict when the off-diagonal entry is nonzero. On the diagonal, the positive integer logarithmic selector applies at effective price three times p with optimizer two, and at effective price two times p with optimizer three. Any diagonal change gives a strict loss in at least one coordinate.

**Theorem 1.9 (The optimizer is not scalar).**

$$D\left(0, 0\right) \ne D\left(1, 1\right) \land \left(\forall c \in \mathbb{R},\; \operatorname{R}\left(D\right) \ne c \cdot I\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/WeightedDiscreteLogNoGo.selectedMatrix_not_scalar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two diagonal entries are two and three. A scalar identity matrix has equal diagonal entries.

**Definition 1.10 (The equal-diagonal assertion).**

$$A \Leftrightarrow \left(\forall p \in \mathbb{R},\; \operatorname{W}\left(p\right) \Rightarrow \left(\forall T \in M,\; \operatorname{P}\left(T\right) \Rightarrow \left(\left(\forall U \in M,\; \operatorname{P}\left(U\right) \Rightarrow \left(U \ne T \Rightarrow \operatorname{f}\left(p, U\right) < \operatorname{f}\left(p, T\right)\right)\right) \Rightarrow T\left(0, 0\right) = T\left(1, 1\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/GoldenResource/WeightedDiscreteLogNoGo.uniformSelection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This assertion would force every strict global optimizer at every price in W to have equal diagonal entries.

**Theorem 1.11 (Equal diagonals are not forced).**

$$\neg A$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/WeightedDiscreteLogNoGo.weighted_selector_refutes_uniformity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At price one sixth, D is positive definite and every distinct admissible integer matrix has smaller objective, while its diagonal entries are unequal.

## References

- Truth anchor: `D5/S3/Arith/GoldenResource/WeightedDiscreteLogNoGo.objective`
- Truth anchor: `D5/S3/Arith/GoldenResource/WeightedDiscreteLogNoGo.off_diagonal_det_loss`
- Truth anchor: `D5/S3/Arith/GoldenResource/WeightedDiscreteLogNoGo.one_sixth_mem_priceWindow`
- Truth anchor: `D5/S3/Arith/GoldenResource/WeightedDiscreteLogNoGo.priceWindow`
- Truth anchor: `D5/S3/Arith/GoldenResource/WeightedDiscreteLogNoGo.priceWindow_nonempty`
- Truth anchor: `D5/S3/Arith/GoldenResource/WeightedDiscreteLogNoGo.selectedMatrix`
- Truth anchor: `D5/S3/Arith/GoldenResource/WeightedDiscreteLogNoGo.selectedMatrix_not_scalar`
- Truth anchor: `D5/S3/Arith/GoldenResource/WeightedDiscreteLogNoGo.selectedMatrix_posDef`
- Truth anchor: `D5/S3/Arith/GoldenResource/WeightedDiscreteLogNoGo.uniformSelection`
- Truth anchor: `D5/S3/Arith/GoldenResource/WeightedDiscreteLogNoGo.weighted_selector_refutes_uniformity`
- Truth anchor: `D5/S3/Arith/GoldenResource/WeightedDiscreteLogNoGo.weighted_unique_maximum`
- Dependency: [D5/S3/Arith/GoldenResource/DiscreteLogSelector](DiscreteLogSelector.md)
