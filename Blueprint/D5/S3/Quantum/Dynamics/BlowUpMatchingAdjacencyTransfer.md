# Adjacency transfer through uniform clone matchings

## Abstract

Integral adjacency support gives perfect state transfer at pi/2 after adding the same perfect matching in every clone set.

**Definition 1.1 (Integral adjacency eigenvalue support).**

$$\forall (m: \mathbb{N}), (\forall (g: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(m\right)\right)), ([\operatorname{DecidableRel}\left(\operatorname{SimpleGraph.Adj}\left(g\right)\right)], (\forall (v: \operatorname{Fin}\left(m\right)), ((\operatorname{D5.S3.Quantum.Dynamics.BlowUpMatchingAdjacencyTransfer.IntegralSupport}\left(g, v\right)) \Leftrightarrow (\forall (l: \mathbb{R}), (\forall (x: (\operatorname{Fin}\left(m\right)) \to (\mathbb{C})), ((\operatorname{Matrix.mulVec}\left(\operatorname{SimpleGraph.adjMatrix}\left(\mathbb{C}, g\right), x\right) = (\operatorname{Complex.ofReal}\left(l\right)) \cdot (x)) \to ((x\left(v\right) \ne (0: \mathbb{C})) \to (\exists (z: \mathbb{Z}), (l = (\operatorname{Int.cast}\left(z\right): \mathbb{R})))))))))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/BlowUpMatchingAdjacencyTransfer.IntegralSupport` (`✓ std3`).

*Citation.* Hermie Monterde; Hiranmoy Pal; Steve Kirkland (2025). *Laplacian quantum walks on blow-up graphs*. DOI: [10.1016/j.laa.2025.10.001](https://doi.org/10.1016/j.laa.2025.10.001). URL: <https://arxiv.org/abs/2504.11585v1>.

*Commentary.*

IntegralSupport g v says that every real eigenvalue l of the complex adjacency matrix having an eigenvector x with x(v) nonzero is an integer. The eigenvector equation includes l in the complex scalars; the conclusion includes an integer z in the reals. The source defines eigenvalue support by the nonzero spectral projection of a coordinate vector in main.tex, lines 156–158. Here that notion is applied to the adjacency matrix rather than the Laplacian: a nonzero projection onto a real eigenspace is equivalent to an eigenvector in that eigenspace with nonzero v-coordinate.

**Definition 1.2 (The blow-up with a uniform matching perturbation).**

$$\forall (m: \mathbb{N}), (\forall (g: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(m\right)\right)), ([\operatorname{DecidableRel}\left(\operatorname{SimpleGraph.Adj}\left(g\right)\right)], (\forall (n: \mathbb{N}), (\forall (\rho: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(n\right)\right)), ((\operatorname{D5.S3.Quantum.Dynamics.BlowUpMatchingAdjacencyTransfer.blowUpMatching}\left(g, n, \rho\right): \operatorname{Matrix}\left((\operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right)), (\operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right)), \mathbb{C}\right)) = \operatorname{Matrix.kroneckerMap}\left((\operatorname{HMul.hMul}: (\mathbb{C}) \to ((\mathbb{C}) \to (\mathbb{C}))), \operatorname{SimpleGraph.adjMatrix}\left(\mathbb{C}, g\right), \operatorname{Matrix.of}\left(\operatorname{Function.const}\left(\operatorname{Fin}\left(n\right), \operatorname{Function.const}\left(\operatorname{Fin}\left(n\right), (1: \mathbb{C})\right)\right)\right)\right) + \operatorname{Matrix.kroneckerMap}\left((\operatorname{HMul.hMul}: (\mathbb{C}) \to ((\mathbb{C}) \to (\mathbb{C}))), (1: \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right)), \operatorname{Equiv.Perm.permMatrix}\left(\mathbb{C}, \rho\right)\right))))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/BlowUpMatchingAdjacencyTransfer.blowUpMatching` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hermie Monterde; Hiranmoy Pal; Steve Kirkland (2025). *Laplacian quantum walks on blow-up graphs*. DOI: [10.1016/j.laa.2025.10.001](https://doi.org/10.1016/j.laa.2025.10.001). URL: <https://arxiv.org/abs/2504.11585v1>.

*Commentary.*

The indices are pairs (vertex, clone). The first summand is the adjacency matrix of the n-fold blow-up: replace every vertex by n independent clones and every edge by all edges between the corresponding clone sets. The source gives this construction in main.tex, lines 126–128, with the clone coordinate first. The all-ones matrix is written as Matrix.of of two constant functions. The second summand repeats the permutation matrix of ρ in every clone set. The definition allows any permutation; when ρ is a fixed-point-free involution, this summand inserts the same perfect matching in every clone set. The permutation matrix sends a coordinate vector to its inverse image, which equals its image for an involution.

**Theorem 1.3 (Perfect state transfer across each matching edge above v).**

$$\forall (m: \mathbb{N}), (\forall (n: \mathbb{N}), (\forall (g: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(m\right)\right)), ([\operatorname{DecidableRel}\left(\operatorname{SimpleGraph.Adj}\left(g\right)\right)], (\forall (v: \operatorname{Fin}\left(m\right)), (\forall (\rho: \operatorname{D5.S3.Zeros.Convolution.PerfectMatchingCount.FixedPointFreeInvolution}\left(\operatorname{Fin}\left(n\right)\right)), ((\operatorname{D5.S3.Quantum.Dynamics.BlowUpMatchingAdjacencyTransfer.IntegralSupport}\left(g, v\right)) \to (((4: \mathbb{N}) \mid n) \to (\forall (j: \operatorname{Fin}\left(n\right)), (\operatorname{D5.S3.Quantum.Dynamics.RationalWeightPathTransfer.HasPST}\left(\operatorname{D5.S3.Quantum.Dynamics.BlowUpMatchingAdjacencyTransfer.blowUpMatching}\left(g, n, \operatorname{Subtype.val}\left(\rho\right)\right), \frac{\operatorname{Real.pi}}{(2: \mathbb{R})}, (v, j), (v, \operatorname{Subtype.val}\left(\rho\right)\left(j\right))\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/BlowUpMatchingAdjacencyTransfer.result` (`✓ std3`). ∎

*Resolves.* `Problems/monterde-pal-kirkland-2025-blowup-matching-adjacency-transfer` (proved) by `D5/S3/Quantum/Dynamics/BlowUpMatchingAdjacencyTransfer.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"monterde-pal-kirkland-2025-blowup-matching-adjacency-transfer","declaration_gid":"D5/S3/Quantum/Dynamics/BlowUpMatchingAdjacencyTransfer.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Hermie Monterde; Hiranmoy Pal; Steve Kirkland (2025). *Laplacian quantum walks on blow-up graphs*. DOI: [10.1016/j.laa.2025.10.001](https://doi.org/10.1016/j.laa.2025.10.001). URL: <https://arxiv.org/abs/2504.11585v1>.

*Commentary.*

Let g be a finite simple graph, let v have integral adjacency eigenvalue support, and let 4 divide n. A fixed-point-free involution ρ on Fin n specifies a perfect matching of the clone indices. Adding this same perfect matching in every clone set gives adjacency perfect state transfer at π/2 between (v,j) and (v,ρ.val j) for every j. HasPST means that the squared modulus of the corresponding entry of exp(i t H) is one. No connectivity hypothesis is needed. The source asks about an appropriate matching in main.tex, line 814, following its Laplacian theorem at lines 666–668. The literal analogue with a matching only among the clones of v is not claimed.

First, write n = 4q. For any integer z, exp(iπnz/2) = exp(2πi(qz)) = 1. Diagonalize the Hermitian adjacency matrix A of g as A = U D U*, with U a unitary eigenvector matrix and D the diagonal eigenvalue matrix. For an eigenvector whose v-coordinate vanishes, its contribution to the v-column vanishes. For every other eigenvector, IntegralSupport makes its real eigenvalue an integer, so the preceding phase identity applies. Thus every term of the v-column of U exp(iπnD/2) U* equals the corresponding term of U U*. Since U U* is the identity, exp(iπnA/2)eᵥ = eᵥ.

Let J be the n by n all-ones matrix, put A₀ = A ⊗ J, and put B = I ⊗ P, where P is the permutation matrix of ρ.val. Both J P and P J equal J, since permuting rows or columns preserves J. The Kronecker multiplication identity therefore gives A₀ B = B A₀.

For any complex square matrix b with b² = I, consider the complex algebra map from ℂ × ℂ to matrices that sends (a,d) to ((a+d)/2)I + ((a−d)/2)b. It sends (c,−c) to cb and commutes with the exponential, by continuity in finite dimension. At c = iπ/2 the two scalar exponentials are i and −i, so exp(iπb/2) = ib. The involutivity of ρ.val gives P² = I, and the Kronecker multiplication identity then gives B² = I. Consequently exp(iπB/2) = iB.

Next J² = nJ gives, by induction on r, (A ⊗ J)^(r+1) = n^r (A^(r+1) ⊗ J). For n nonzero, apply the continuous coordinate evaluation maps to the convergent matrix exponential series. Every positive-degree coefficient agrees with n⁻¹ times the corresponding coefficient for exp((cn)A); the degree-zero coefficient supplies the identity correction. Uniqueness of the sums gives the following column formula: the p-coordinate of exp(cA₀)e_(v,k) is the p-coordinate of e_(v,k) plus n⁻¹ times the p.1-coordinate of exp((cn)A)eᵥ − eᵥ. Here n and n⁻¹ are interpreted in ℂ.

The permutation-matrix action and involutivity give Be_(v,j) = e_(v,ρ.val j). The existence of j in Fin n ensures n is nonzero. With c = iπ/2, the periodicity of eᵥ makes the correction in the column formula zero, so exp(iπA₀/2) fixes e_(v,ρ.val j). Since A₀ and B commute, the exponential of their sum factors. Acting first by exp(iπB/2) = iB and then by exp(iπA₀/2) yields exp(iπ(A₀+B)/2)e_(v,j) = i e_(v,ρ.val j).

Finally apply this column identity with ρ.val j in place of j and evaluate at (v,j). Involutivity gives ρ.val (ρ.val j) = j, so the matrix entry with row (v,j) and column (v,ρ.val j) equals i. The propagator at negative time −π/2 is exactly this positive-sign matrix exponential. Since Complex.normSq i = 1, the asserted HasPST follows.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/BlowUpMatchingAdjacencyTransfer.IntegralSupport`
- Truth anchor: `D5/S3/Quantum/Dynamics/BlowUpMatchingAdjacencyTransfer.blowUpMatching`
- Truth anchor: `D5/S3/Quantum/Dynamics/BlowUpMatchingAdjacencyTransfer.result`
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/FiniteEndpointPairing](../../Combinatorics/PerfectMatchings/FiniteEndpointPairing.md)
- Dependency: [D5/S3/Quantum/Dynamics/RationalWeightPathTransfer](RationalWeightPathTransfer.md)
- Dependency: [D5/S3/Zeros/Convolution/PerfectMatchingCount](../../Zeros/Convolution/PerfectMatchingCount.md)
