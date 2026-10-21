# Spectral coefficients from part sizes

## Abstract

The reciprocal adjacency determinant of a complete multipartite graph.

**Theorem 1.1 (Equality with the part recurrence).**

Lean statement: `D5/S3/Combinatorics/Graph/MultipartiteCHS/Spectral.chs_eq_recH`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/MultipartiteCHS/Spectral.chs_eq_recH` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ángel Chávez, Sarah Fullerton, Matilda LaFortune, Keyron Linarez, Nethmin Liyanage, Justin Son and Tyler Ting (2023). *Extremal polynomial norms of graphs*. DOI: [10.48550/arXiv.2311.04689](https://doi.org/10.48550/arXiv.2311.04689). URL: <https://arxiv.org/abs/2311.04689v3>.

*Commentary.*

For every natural number of parts r, every family a of natural part sizes, and every degree d, the complete homogeneous symmetric polynomial of degree d in the real adjacency eigenvalues equals recH(a,d). No positivity assumption on the part sizes or parity assumption on d is needed.

Factor the vertex adjacency matrix through the part-index space. The Weinstein-Aronszajn identity reduces its determinant pencil to the r by r matrix with zero diagonal and entry a(j) off the diagonal. Each principal minor of its negative has determinant (1-j) times the product of its j part sizes: column scaling reduces it to the identity minus the all-ones matrix, and the matrix determinant lemma evaluates the latter.

The determinant is therefore 1 minus the sum, for j from 2 through r, of (j-1)e_j(a)t^j. Mathlib's Hermitian characteristic-polynomial factorization and polynomial reversal identify it with the product of 1-lambda(i)t. The complete homogeneous generating-series identity from PathCHSNormClosedForm then gives the reciprocal determinant. Comparing coefficients yields H(0)=1 and H(d)=sum over 2<=j<=d of (j-1)e_j(a)H(d-j). Strong induction identifies these coefficients with recH. This is an algebraic identity for the literal adjacency matrix; it is independent of any extremality assertion. The spectral definition is Theorem 1.4 of the cited article; the complete multipartite branch of its Problem 3 is the application.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/MultipartiteCHS/Spectral.chs_eq_recH`
- Dependency: [D5/S3/Combinatorics/Graph/MultipartiteCHS/Defs](Defs.md)
- Dependency: [D5/S3/Combinatorics/Graph/MultipartiteCHS/Recurrence](Recurrence.md)
- Dependency: [D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormClosedForm](../PathCHS/PathCHSNormClosedForm.md)
