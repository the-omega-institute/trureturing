# Binary kite-shaped quadratic forms

## Abstract

Binary kite forms are doubly perfect exactly off one residue modulo three.

**Definition 1.1 (The kite matrix).**

$$\forall (n: \mathbb{N}), \forall (i: \operatorname{Fin}\left(n\right)), \forall (j: \operatorname{Fin}\left(n\right)), (\operatorname{kite}\left(n, i, j\right): \operatorname{ZMod}\left(2\right)) = \operatorname{ite}\left((\operatorname{Fin.val}\left(i\right): \mathbb{N}) + (\operatorname{Fin.val}\left(j\right): \mathbb{N}) + 2 \le n + 1, (1: \operatorname{ZMod}\left(2\right)), (0: \operatorname{ZMod}\left(2\right))\right)$$

*Formalization.* `D5/S3/Quantum/Information/KiteShapedDoublyPerfectForm.kite` (`✓ std3`).

*Citation.* David Gross; Paulina Goedicke (2025). *Thirty-six officers, artisanally entangled*. DOI: [10.48550/arXiv.2504.15401](https://doi.org/10.48550/arXiv.2504.15401). URL: <https://arxiv.org/abs/2504.15401v2>.

*Commentary.*

The matrix has entries in the binary field ZMod 2, with rows and columns indexed by Fin n. Fin.val explicitly converts each index to a natural number. Its entry is one exactly when the sum of the two zero-based indices plus two is at most n plus one, and zero otherwise. Adding one to each index gives the source's one-based kite-shaped support (artisanal.tex, line 2316). The definition also includes the empty matrix at n equal to zero.

**Definition 1.2 (The block-diagonal quadratic form).**

$$\forall (n: \mathbb{N}), (\operatorname{quadraticForm}\left(n\right): \operatorname{Matrix}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right)\right), \operatorname{Sum}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right)\right), \operatorname{ZMod}\left(2\right)\right)) = \operatorname{Matrix.fromBlocks}\left(\operatorname{kite}\left(n\right), (0: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \operatorname{ZMod}\left(2\right)\right)), (0: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \operatorname{ZMod}\left(2\right)\right)), \operatorname{kite}\left(n\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/KiteShapedDoublyPerfectForm.quadraticForm` (`✓ std3`).

*Citation.* David Gross; Paulina Goedicke (2025). *Thirty-six officers, artisanally entangled*. DOI: [10.48550/arXiv.2504.15401](https://doi.org/10.48550/arXiv.2504.15401). URL: <https://arxiv.org/abs/2504.15401v2>.

*Commentary.*

The two diagonal blocks are the same kite matrix, and both off-diagonal blocks are zero. Sum (Fin n) (Fin n) is the disjoint union indexing the two blocks. This is the symmetric coefficient matrix N in the source's quadratic-phase construction (artisanal.tex, lines 2226–2230 and 2315–2316).

**Definition 1.3 (The exact residue criterion).**

$$(\operatorname{claim}: \operatorname{Prop}) = (\forall (n: \mathbb{N}), (1 \le n) \Rightarrow ((\operatorname{Matrix.IsSymm}\left(\operatorname{kite}\left(n\right)\right)) \land ((\operatorname{Matrix.SeparatingRight}\left(\operatorname{kite}\left(n\right)\right)) \land ((\operatorname{Matrix.SeparatingRight}\left(\operatorname{quadraticForm}\left(n\right)\right)) \land (((\operatorname{Matrix.SeparatingRight}\left(\operatorname{kite}\left(n\right) \cdot \operatorname{kite}\left(n\right) - (1: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \operatorname{ZMod}\left(2\right)\right))\right)) \Leftrightarrow (n \bmod 3 \ne 1)) \land ((\operatorname{Matrix.SeparatingRight}\left(\operatorname{quadraticForm}\left(n\right) + \operatorname{Matrix.J}\left(\operatorname{Fin}\left(n\right), \operatorname{ZMod}\left(2\right)\right)\right)) \Leftrightarrow (n \bmod 3 \ne 1)))))))$$

*Formalization.* `D5/S3/Quantum/Information/KiteShapedDoublyPerfectForm.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Gross; Paulina Goedicke (2025). *Thirty-six officers, artisanally entangled*. DOI: [10.48550/arXiv.2504.15401](https://doi.org/10.48550/arXiv.2504.15401). URL: <https://arxiv.org/abs/2504.15401v2>.

*Commentary.*

For every positive n, the kite matrix is symmetric and has trivial right kernel, as does its block-diagonal quadratic form. Each of the two remaining right kernels is trivial exactly when n is not one modulo three. Matrix.SeparatingRight expresses triviality of the right kernel for these matrices. The sufficient direction is the source's observation (artisanal.tex, lines 2304–2316); the converse specifies precisely when this construction fails. Matrix.J (Fin n) (ZMod 2) is Mathlib's block matrix with blocks 0, -1, 1, 0. The source uses blocks 0, 1, -1, 0 (lines 349–358); over ZMod 2 the two matrices coincide. The quadratic-phase criterion then identifies the nonsingular cases with doubly perfect quadratic exponentials (lines 2226–2230).

**Theorem 1.4 (The kite construction succeeds exactly outside one residue).**

$$\forall (n: \mathbb{N}), (1 \le n) \Rightarrow ((\operatorname{Matrix.IsSymm}\left(\operatorname{kite}\left(n\right)\right)) \land ((\operatorname{Matrix.SeparatingRight}\left(\operatorname{kite}\left(n\right)\right)) \land ((\operatorname{Matrix.SeparatingRight}\left(\operatorname{quadraticForm}\left(n\right)\right)) \land (((\operatorname{Matrix.SeparatingRight}\left(\operatorname{kite}\left(n\right) \cdot \operatorname{kite}\left(n\right) - (1: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \operatorname{ZMod}\left(2\right)\right))\right)) \Leftrightarrow (n \bmod 3 \ne 1)) \land ((\operatorname{Matrix.SeparatingRight}\left(\operatorname{quadraticForm}\left(n\right) + \operatorname{Matrix.J}\left(\operatorname{Fin}\left(n\right), \operatorname{ZMod}\left(2\right)\right)\right)) \Leftrightarrow (n \bmod 3 \ne 1))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/KiteShapedDoublyPerfectForm.result` (`✓ std3`). ∎

*Resolves.* `Problems/gross-goedicke-2025-kite-shaped-quadratic-forms` (proved) by `D5/S3/Quantum/Information/KiteShapedDoublyPerfectForm.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"gross-goedicke-2025-kite-shaped-quadratic-forms","declaration_gid":"D5/S3/Quantum/Information/KiteShapedDoublyPerfectForm.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* David Gross; Paulina Goedicke (2025). *Thirty-six officers, artisanally entangled*. DOI: [10.48550/arXiv.2504.15401](https://doi.org/10.48550/arXiv.2504.15401). URL: <https://arxiv.org/abs/2504.15401v2>.

*Commentary.*

Write K for the kite matrix. Symmetry follows because its entry condition is unchanged when the two indices are exchanged. Define a binary matrix H whose (i,j) entry is the sum of the indicator of i+j+1=n and the indicator of i+j=n, using zero-based natural indices. For any row f, the jth entry of fH is f(n-1-j), together with f(n-j) when j>0. Applying this identity to every row of K gives KH=1: the two threshold indicators cancel in characteristic two except on the diagonal. Thus K has nonzero determinant, and its determinant is one because one is the only nonzero element of ZMod 2.

Let T have first diagonal entry zero, every other diagonal entry one, adjacent off-diagonal entries one, and all remaining entries zero. Applying the same column identity to H shows that T=1+HH. To compute d(n+2), reverse both row and column orders of T of size n+2. This leaves the determinant unchanged and places a sparse row and column first. Removing their first indices gives the reversed matrix of size n+1; removing their first two indices gives the reversed matrix of size n. Expansion therefore gives d(n+2)=d(n+1)+d(n), where d(n) is the determinant of T of size n. The initial determinants are d(0)=1 and d(1)=0. Two-step induction, separating the three residues modulo three, yields d(n)=0 when n is one modulo three and d(n)=1 otherwise.

The identity KH=1 implies KKHH=1, so KKT=KK+1. In characteristic two, subtracting the identity is the same as adding it. Taking determinants and using det K=1 therefore gives det(KK-1)=det T. The determinant of the block-diagonal quadratic form is the product of its two diagonal determinants, hence is also one.

Adding Matrix.J to the quadratic form gives the block matrix with diagonal blocks K and off-diagonal blocks 1. Since K is invertible with inverse H, its Schur complement gives determinant det K times det(K-H). Multiplying K-H by K on the left gives KK-1, so this block determinant equals det(KK-1), and hence det T. Finally, a square matrix over ZMod 2 is right-separating exactly when its determinant is nonzero. The determinant values give the two unconditional trivial-kernel assertions and both equivalences for every positive n.

## References

- Truth anchor: `D5/S3/Quantum/Information/KiteShapedDoublyPerfectForm.claim`
- Truth anchor: `D5/S3/Quantum/Information/KiteShapedDoublyPerfectForm.kite`
- Truth anchor: `D5/S3/Quantum/Information/KiteShapedDoublyPerfectForm.quadraticForm`
- Truth anchor: `D5/S3/Quantum/Information/KiteShapedDoublyPerfectForm.result`
- Dependency: [D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant](../FockSpace/ForbiddenNeighbourDeterminant.md)
