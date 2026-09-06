# Positive Jacobi Cholesky Weights

## Abstract

A symmetric Jacobi matrix with positive characteristic roots has positive recursive Cholesky weights and the forbidden-neighbour determinant polynomial.

**Theorem 1.1 (Positive roots give the recursive positive chain factor).**

$$\begin{aligned}\forall d \in \mathbb{N}, 0 < d, alpha,beta: \mathbb{N} \to \mathbb{R},\\K: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{R}\right),\\\operatorname{IsHermitian}\left(K\right) \land (\forall r \in \mathbb{R}, \operatorname{IsRoot}\left(\operatorname{charpoly}\left(K\right), r\right) \Rightarrow 0 < r) \land\\(\forall i,j \in \operatorname{Fin}\left(d\right), j + 1 < i \Rightarrow K_{i,j} = 0) \land\\(\forall i \in \operatorname{Fin}\left(d\right), K_{i,i} = alpha\left(i\right)) \land\\(\forall j \in \mathbb{N}, j + 1 < d \Rightarrow K_{j + 1,j} = \sqrt{beta\left(j + 1\right)} \land 0 < beta\left(j + 1\right)) \Rightarrow\\w = \operatorname{jacobiWeights}\left(alpha, beta\right), K > 0 \land\\(\forall i \in \operatorname{Fin}\left(2d - 1\right), 0 < w\left(i\right)) \land w\left(0\right) = alpha\left(0\right) \land\\(\forall j \in \mathbb{N}, j + 1 < d \Rightarrow w\left(2j + 1\right) = \frac{beta\left(j + 1\right)}{w\left(2j\right)} \land w\left(2j + 2\right) = alpha\left(j + 1\right) - w\left(2j + 1\right)) \land\\K = \operatorname{lowerBidiagonal}\left(w\right) \operatorname{lowerBidiagonal}\left(w\right)^{T} \land\\\operatorname{det}\left(I + vK\right) = \operatorname{det}\left(I + v\operatorname{lowerBidiagonal}\left(w\right)^{T} \operatorname{lowerBidiagonal}\left(w\right)\right) = \operatorname{forbiddenPartition}\left(w\right)\left(v\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Moments/PositiveJacobiCholesky.positive_jacobi_cholesky` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let d be positive and let K be a real symmetric d by d matrix. Its diagonal entries are alpha(j), its entries immediately below the diagonal are the positive square roots of beta(j+1), and all lower entries farther from the diagonal vanish. Assume beta(j+1) is strictly positive for j+1<d and every real root of the characteristic polynomial of K is strictly positive. Symmetry supplies the upper entries and the spectral theorem then gives positive definiteness.

The recursion is an actual definition: p(0)=alpha(0) and p(j+1)=alpha(j+1)-beta(j+1)/p(j). The zero-based weight function has w(2j)=p(j) and w(2j+1)=beta(j+1)/p(j). Hence its indices 0 through 2d-2 correspond to the usual weights w_1 through w_(2d-1).

The proof reuses the pinned LDL decomposition, constructs a lower Cholesky factor, and proves by column induction that it is bidiagonal. A second induction identifies every recursively computed pivot with the square of a nonzero diagonal entry. Thus every divisor and every new difference is strictly positive. Column sign normalization identifies the factor with the existing lowerBidiagonal definition built from positive square roots.

The polynomial determinant identity uses the existing forbidden_neighbour_determinant theorem and the identity det(I+AB)=det(I+BA). It holds as equality of real polynomials, and therefore at every real or complex evaluation.

This is the matrix construction layer. Root positivity and the symmetric Jacobi presentation are explicit hypotheses. The theorem does not derive them from coefficient Hankel data, change the previous monic basis into an orthonormal basis, or identify a separately supplied coefficient polynomial P with det(I+vK). It gives P=C_w when P denotes that determinant polynomial. The singular Hankel branch and its multiplicity bookkeeping remain outside this declaration.

## References

- Truth anchor: `D5/S3/Constants/Moments/PositiveJacobiCholesky.positive_jacobi_cholesky`
- Dependency: [D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant](../../Quantum/FockSpace/ForbiddenNeighbourDeterminant.md)
