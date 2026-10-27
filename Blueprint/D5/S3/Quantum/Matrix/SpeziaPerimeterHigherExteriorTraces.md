# Higher exterior traces of the perimeter matrix

## Abstract

Higher exterior traces of the Spezia perimeter matrix vanish.

**Definition 1.1 (The perimeter matrix).**

$$\forall (n: \mathbb{N}), \operatorname{M}\left(n\right) = (\operatorname{fun} (i: \operatorname{Fin}\left(n\right)) \mapsto (\operatorname{fun} (j: \operatorname{Fin}\left(n\right)) \mapsto \operatorname{if} \operatorname{val}\left(i\right) + 1 < 3 \lor \operatorname{val}\left(j\right) + 1 < 3 \operatorname{then} ((\operatorname{Nat.cast}\left(\operatorname{val}\left(i\right)\right): \mathbb{C}) + 1) \cdot ((\operatorname{Nat.cast}\left(\operatorname{val}\left(j\right)\right): \mathbb{C}) + 1) \operatorname{else} 2 \cdot (((\operatorname{Nat.cast}\left(\operatorname{val}\left(i\right)\right): \mathbb{C}) + 1) + ((\operatorname{Nat.cast}\left(\operatorname{val}\left(j\right)\right): \mathbb{C}) + 1)) - 4))$$

*Formalization.* `D5/S3/Quantum/Matrix/SpeziaPerimeterHigherExteriorTraces.M` (`✓ std3`).

*Citation.* Stefano Spezia (2019). *OEIS A330700, second exterior-trace conjecture*. URL: <https://oeis.org/A330700>.

*Commentary.*

OEIS A330287, COMMENTS, revision 31 (unpaginated): “The matrix M(n) is defined as M[i,j,n] = i*j if i < 3 or j < 3 and M[i,j,n] = 2*(i + j) - 4 otherwise.” The row and column types are Fin n; source indices are val(i)+1 and val(j)+1. Entries lie in ℂ. The casts shown in the formula embed natural numbers in ℂ; the comparisons use natural numbers and the subtraction uses ℂ.

**Definition 1.2 (Spezia's second exterior-trace conjecture).**

$$claim = (\forall (n: \mathbb{N}), (0 < n) \Rightarrow (\forall (k: \mathbb{N}), (2 < k) \Rightarrow (\operatorname{Matrix.trace}\left(\operatorname{compoundMatrix}\left(\operatorname{M}\left(n\right), k\right)\right) = 0)))$$

*Formalization.* `D5/S3/Quantum/Matrix/SpeziaPerimeterHigherExteriorTraces.claim` (`✓ std3`).

*Citation.* Stefano Spezia (2019). *OEIS A330700, second exterior-trace conjecture*. URL: <https://oeis.org/A330700>.

*Commentary.*

OEIS A330700, COMMENTS, revision 23, second line of the Conjectures block (unpaginated): “For k > 2, the trace of the k-th exterior power of M(n) is equal to zero.” Here n is any positive natural number and k is any natural number greater than two. The existing compoundMatrix is the matrix of the exterior power: its entries are determinants of the ordered k-by-k submatrices. Matrix.trace sums its diagonal entries. For k > n its index type is empty, so this includes the zero-dimensional exterior space.

**Theorem 1.3 (All exterior traces above order two vanish).**

$$\forall (n: \mathbb{N}), (0 < n) \Rightarrow (\forall (k: \mathbb{N}), (2 < k) \Rightarrow (\operatorname{Matrix.trace}\left(\operatorname{compoundMatrix}\left(\operatorname{M}\left(n\right), k\right)\right) = 0))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/SpeziaPerimeterHigherExteriorTraces.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Stefano Spezia (2019). *OEIS A330700, second exterior-trace conjecture*. URL: <https://oeis.org/A330700>.

*Commentary.*

Write v(i)=val(i)+1 and w(i)=max(val(i)−1,0), interpreted in ℂ. The entry formula gives M(n)=vvᵀ−wwᵀ, hence a product of an n-by-two matrix and a two-by-n matrix. For k > 2, Cauchy–Binet expresses every k-by-k minor as a sum over k-element subsets of Fin 2. There are no such subsets. Thus the whole higher compound matrix is zero, and taking its trace gives zero. The assertion concerns the second conjecture; the separate scalar sequence and its second-exterior-trace conjecture are separate questions.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/SpeziaPerimeterHigherExteriorTraces.M`
- Truth anchor: `D5/S3/Quantum/Matrix/SpeziaPerimeterHigherExteriorTraces.claim`
- Truth anchor: `D5/S3/Quantum/Matrix/SpeziaPerimeterHigherExteriorTraces.result`
- Dependency: [D5/S3/Quantum/Schatten/CompoundMatrices](../Schatten/CompoundMatrices.md)
