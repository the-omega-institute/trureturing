# Hadamard Bound for Integer Matrices

## Abstract

A positive definite integer matrix has a positive integer determinant bounded by its diagonal product, with equality exactly for a diagonal matrix.

Let n be a finite index type. For an integer matrix T, let R(T) denote its entrywise inclusion into the real matrices and let D(T) denote the diagonal matrix with the same diagonal entries. Positive definiteness of R(T) includes symmetry. Products are over all indices in n, with the empty product equal to one.

**Theorem 1.1 (Positive integer determinant and equality condition).**

$$\begin{gathered}\forall n: Type, [Fintype\left(n\right)] [DecidableEq\left(n\right)],\\\forall T: Matrix\left(n, n, \mathbb{Z}\right),\\PosDef\left(R\left(T\right)\right) \Rightarrow \left(\left(\forall i \in n,\; 0 < T\left(i, i\right)\right) \land \left(0 < det\left(T\right) \land \left(det\left(T\right) \le \prod_{i:n} T\left(i, i\right) \land \left(det\left(T\right) = \prod_{i:n} T\left(i, i\right) \Leftrightarrow T = D\left(T\right)\right)\right)\right)\right)\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/IntegerHadamard.integer_posDef_hadamard` (`✓ std3`). ∎

*Citation.* Minghua Lin and Gord Sinnamon (2020). *Revisiting a sharpened version of Hadamard's determinant inequality*. DOI: [10.1016/j.laa.2020.07.032](https://doi.org/10.1016/j.laa.2020.07.032).

*Commentary.*

The diagonal entries are positive by positive definiteness. Their diagonal matrix is positive definite as well. The divergence between T and this diagonal matrix equals the logarithm of the diagonal product minus the logarithm of the determinant: its trace correction vanishes. Nonnegativity gives the determinant bound, and vanishing of the divergence gives precisely the diagonal equality condition. The determinant belongs to the integers because the determinant is a polynomial with integer coefficients.

**Theorem 1.2 (An integer loss away from diagonal matrices).**

$$\begin{gathered}\forall n: Type, [Fintype\left(n\right)] [DecidableEq\left(n\right)],\\\forall T: Matrix\left(n, n, \mathbb{Z}\right),\\\left(PosDef\left(R\left(T\right)\right) \land T \ne D\left(T\right)\right) \Rightarrow det\left(T\right) + 1 \le \prod_{i:n} T\left(i, i\right)\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/IntegerHadamard.nondiagonal_integer_det_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nondiagonal matrix the equality condition makes the determinant bound strict. Both sides are integers, so their difference is at least one.

## References

- Truth anchor: `D5/S3/Arith/GoldenResource/IntegerHadamard.integer_posDef_hadamard`
- Truth anchor: `D5/S3/Arith/GoldenResource/IntegerHadamard.nondiagonal_integer_det_gap`
- Dependency: [D5/S3/Resource/LogDetDivergenceEquality](../../Resource/LogDetDivergenceEquality.md)
