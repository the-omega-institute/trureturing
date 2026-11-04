# No reverse perfect state transfer in the seven-state bipartite walk

## Abstract

Neither seven-state matrix transfers the sixth coordinate state to the first at any natural step.

**Definition 1.1 (The first projection).**

$$(\operatorname{D5.S3.Quantum.Walks.BipartiteWalkReverseStateTransfer.P}: \operatorname{Matrix}\left(\operatorname{Fin}\left(7\right), \operatorname{Fin}\left(7\right), \mathbb{C}\right)) = \begin{bmatrix}\frac{(1: \mathbb{C})}{(3: \mathbb{C})}&(0: \mathbb{C})&\frac{(1: \mathbb{C})}{(3: \mathbb{C})}&\frac{(1: \mathbb{C})}{(3: \mathbb{C})}&(0: \mathbb{C})&(0: \mathbb{C})&(0: \mathbb{C})\\(0: \mathbb{C})&\frac{(1: \mathbb{C})}{(2: \mathbb{C})}&(0: \mathbb{C})&(0: \mathbb{C})&(0: \mathbb{C})&\frac{(1: \mathbb{C})}{(2: \mathbb{C})}&(0: \mathbb{C})\\\frac{(1: \mathbb{C})}{(3: \mathbb{C})}&(0: \mathbb{C})&\frac{(1: \mathbb{C})}{(3: \mathbb{C})}&\frac{(1: \mathbb{C})}{(3: \mathbb{C})}&(0: \mathbb{C})&(0: \mathbb{C})&(0: \mathbb{C})\\\frac{(1: \mathbb{C})}{(3: \mathbb{C})}&(0: \mathbb{C})&\frac{(1: \mathbb{C})}{(3: \mathbb{C})}&\frac{(1: \mathbb{C})}{(3: \mathbb{C})}&(0: \mathbb{C})&(0: \mathbb{C})&(0: \mathbb{C})\\(0: \mathbb{C})&(0: \mathbb{C})&(0: \mathbb{C})&(0: \mathbb{C})&(1: \mathbb{C})&(0: \mathbb{C})&(0: \mathbb{C})\\(0: \mathbb{C})&\frac{(1: \mathbb{C})}{(2: \mathbb{C})}&(0: \mathbb{C})&(0: \mathbb{C})&(0: \mathbb{C})&\frac{(1: \mathbb{C})}{(2: \mathbb{C})}&(0: \mathbb{C})\\(0: \mathbb{C})&(0: \mathbb{C})&(0: \mathbb{C})&(0: \mathbb{C})&(0: \mathbb{C})&(0: \mathbb{C})&(1: \mathbb{C})\end{bmatrix}$$

*Formalization.* `D5/S3/Quantum/Walks/BipartiteWalkReverseStateTransfer.P` (`✓ std3`).

*Citation.* Qiuting Chen; Chris Godsil; Mariia Sobchuk; Hanmeng Zhan (2024). *Hamiltonians of bipartite walks*. DOI: [10.37236/12040](https://doi.org/10.37236/12040). URL: <https://arxiv.org/abs/2207.01673v1>.

*Commentary.*

P is the complex matrix displayed in Hamiltonian_7.tex, lines 320–329. It averages coordinates within the cells {0,2,3}, {1,5}, {4} and {6}. Indices run from zero to six; source edge i has index i minus one.

**Definition 1.2 (The second projection).**

$$(\operatorname{D5.S3.Quantum.Walks.BipartiteWalkReverseStateTransfer.Q}: \operatorname{Matrix}\left(\operatorname{Fin}\left(7\right), \operatorname{Fin}\left(7\right), \mathbb{C}\right)) = \begin{bmatrix}\frac{(1: \mathbb{C})}{(2: \mathbb{C})}&\frac{(1: \mathbb{C})}{(2: \mathbb{C})}&(0: \mathbb{C})&(0: \mathbb{C})&(0: \mathbb{C})&(0: \mathbb{C})&(0: \mathbb{C})\\\frac{(1: \mathbb{C})}{(2: \mathbb{C})}&\frac{(1: \mathbb{C})}{(2: \mathbb{C})}&(0: \mathbb{C})&(0: \mathbb{C})&(0: \mathbb{C})&(0: \mathbb{C})&(0: \mathbb{C})\\(0: \mathbb{C})&(0: \mathbb{C})&\frac{(1: \mathbb{C})}{(2: \mathbb{C})}&(0: \mathbb{C})&\frac{(1: \mathbb{C})}{(2: \mathbb{C})}&(0: \mathbb{C})&(0: \mathbb{C})\\(0: \mathbb{C})&(0: \mathbb{C})&(0: \mathbb{C})&(1: \mathbb{C})&(0: \mathbb{C})&(0: \mathbb{C})&(0: \mathbb{C})\\(0: \mathbb{C})&(0: \mathbb{C})&\frac{(1: \mathbb{C})}{(2: \mathbb{C})}&(0: \mathbb{C})&\frac{(1: \mathbb{C})}{(2: \mathbb{C})}&(0: \mathbb{C})&(0: \mathbb{C})\\(0: \mathbb{C})&(0: \mathbb{C})&(0: \mathbb{C})&(0: \mathbb{C})&(0: \mathbb{C})&\frac{(1: \mathbb{C})}{(2: \mathbb{C})}&\frac{(1: \mathbb{C})}{(2: \mathbb{C})}\\(0: \mathbb{C})&(0: \mathbb{C})&(0: \mathbb{C})&(0: \mathbb{C})&(0: \mathbb{C})&\frac{(1: \mathbb{C})}{(2: \mathbb{C})}&\frac{(1: \mathbb{C})}{(2: \mathbb{C})}\end{bmatrix}$$

*Formalization.* `D5/S3/Quantum/Walks/BipartiteWalkReverseStateTransfer.Q` (`✓ std3`).

*Citation.* Qiuting Chen; Chris Godsil; Mariia Sobchuk; Hanmeng Zhan (2024). *Hamiltonians of bipartite walks*. DOI: [10.37236/12040](https://doi.org/10.37236/12040). URL: <https://arxiv.org/abs/2207.01673v1>.

*Commentary.*

Q is the complex matrix displayed in Hamiltonian_7.tex, lines 330–338. It averages coordinates within the cells {0,1}, {2,4}, {3} and {5,6}.

**Definition 1.3 (The displayed transition matrix).**

$$(\operatorname{D5.S3.Quantum.Walks.BipartiteWalkReverseStateTransfer.Udisp}: \operatorname{Matrix}\left(\operatorname{Fin}\left(7\right), \operatorname{Fin}\left(7\right), \mathbb{C}\right)) = \begin{bmatrix}(0: \mathbb{C})&\frac{-(1: \mathbb{C})}{(3: \mathbb{C})}&(0: \mathbb{C})&\frac{(2: \mathbb{C})}{(3: \mathbb{C})}&\frac{(2: \mathbb{C})}{(3: \mathbb{C})}&(0: \mathbb{C})&(0: \mathbb{C})\\(0: \mathbb{C})&(0: \mathbb{C})&(0: \mathbb{C})&(0: \mathbb{C})&(0: \mathbb{C})&(0: \mathbb{C})&(1: \mathbb{C})\\(0: \mathbb{C})&\frac{(2: \mathbb{C})}{(3: \mathbb{C})}&(0: \mathbb{C})&\frac{(2: \mathbb{C})}{(3: \mathbb{C})}&\frac{(1: \mathbb{C})}{(3: \mathbb{C})}&(0: \mathbb{C})&(0: \mathbb{C})\\(0: \mathbb{C})&\frac{(2: \mathbb{C})}{(3: \mathbb{C})}&(0: \mathbb{C})&\frac{-(1: \mathbb{C})}{(3: \mathbb{C})}&\frac{(2: \mathbb{C})}{(3: \mathbb{C})}&(0: \mathbb{C})&(0: \mathbb{C})\\(0: \mathbb{C})&(0: \mathbb{C})&(1: \mathbb{C})&(0: \mathbb{C})&(0: \mathbb{C})&(0: \mathbb{C})&(0: \mathbb{C})\\(1: \mathbb{C})&(0: \mathbb{C})&(0: \mathbb{C})&(0: \mathbb{C})&(0: \mathbb{C})&(0: \mathbb{C})&(0: \mathbb{C})\\(0: \mathbb{C})&(0: \mathbb{C})&(0: \mathbb{C})&(0: \mathbb{C})&(0: \mathbb{C})&(1: \mathbb{C})&(0: \mathbb{C})\end{bmatrix}$$

*Formalization.* `D5/S3/Quantum/Walks/BipartiteWalkReverseStateTransfer.Udisp` (`✓ std3`).

*Citation.* Qiuting Chen; Chris Godsil; Mariia Sobchuk; Hanmeng Zhan (2024). *Hamiltonians of bipartite walks*. DOI: [10.37236/12040](https://doi.org/10.37236/12040). URL: <https://arxiv.org/abs/2207.01673v1>.

*Commentary.*

Udisp is the matrix printed in Hamiltonian_7.tex, lines 340–351, and repeated in the open questions at lines 1276–1287. Its entry at row 2, column 4 is positive one third.

**Definition 1.4 (The product of the two reflections).**

$$(\operatorname{D5.S3.Quantum.Walks.BipartiteWalkReverseStateTransfer.Udef}: \operatorname{Matrix}\left(\operatorname{Fin}\left(7\right), \operatorname{Fin}\left(7\right), \mathbb{C}\right)) = ((((2: \mathbb{N})) \cdot (\operatorname{D5.S3.Quantum.Walks.BipartiteWalkReverseStateTransfer.P})) - ((1: \operatorname{Matrix}\left(\operatorname{Fin}\left(7\right), \operatorname{Fin}\left(7\right), \mathbb{C}\right)))) \cdot ((((2: \mathbb{N})) \cdot (\operatorname{D5.S3.Quantum.Walks.BipartiteWalkReverseStateTransfer.Q})) - ((1: \operatorname{Matrix}\left(\operatorname{Fin}\left(7\right), \operatorname{Fin}\left(7\right), \mathbb{C}\right))))$$

*Formalization.* `D5/S3/Quantum/Walks/BipartiteWalkReverseStateTransfer.Udef` (`✓ std3`).

*Citation.* Qiuting Chen; Chris Godsil; Mariia Sobchuk; Hanmeng Zhan (2024). *Hamiltonians of bipartite walks*. DOI: [10.37236/12040](https://doi.org/10.37236/12040). URL: <https://arxiv.org/abs/2207.01673v1>.

*Commentary.*

Udef is the product of the reflections associated with P and Q, as in Hamiltonian_7.tex, lines 154–163. The scalar two acts by natural scalar multiplication, and the subtracted one is the identity matrix. This product agrees with Udisp except that its entry at row 2, column 4 is negative one third.

**Definition 1.5 (Perfect state transfer).**

$$\forall (n: \mathbb{N}), (\forall (U: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), (\forall (a: \operatorname{Fin}\left(n\right)), (\forall (b: \operatorname{Fin}\left(n\right)), ((\operatorname{D5.S3.Quantum.Walks.BipartiteWalkReverseStateTransfer.PerfectStateTransfer}\left(U, a, b\right)) \Leftrightarrow (\exists (k: \mathbb{N}), (\exists (\gamma: \mathbb{C}), ((\left\lVert \gamma \right\rVert = (1: \mathbb{R})) \land (\operatorname{Matrix.mulVec}\left((U)^{k}, \operatorname{Pi.single}\left(a, (1: \mathbb{C})\right)\right) = (\gamma) \cdot (\operatorname{Pi.single}\left(b, (1: \mathbb{C})\right))))))))))$$

*Formalization.* `D5/S3/Quantum/Walks/BipartiteWalkReverseStateTransfer.PerfectStateTransfer` (`✓ std3`).

*Citation.* Qiuting Chen; Chris Godsil; Mariia Sobchuk; Hanmeng Zhan (2024). *Hamiltonians of bipartite walks*. DOI: [10.37236/12040](https://doi.org/10.37236/12040). URL: <https://arxiv.org/abs/2207.01673v1>.

*Commentary.*

For a complex matrix U on Fin n, perfect state transfer from a to b means that some natural power sends the coordinate vector at a to the coordinate vector at b times a complex phase of norm one. The evolution by powers is described in Hamiltonian_7.tex, lines 135–142, and the direction of transfer in line 1288. The predicate allows step zero and equal endpoints, and imposes no unitarity hypothesis on U.

**Definition 1.6 (No transfer from the sixth coordinate to the first).**

$$(\operatorname{D5.S3.Quantum.Walks.BipartiteWalkReverseStateTransfer.claim}) \Leftrightarrow ((\neg (\operatorname{D5.S3.Quantum.Walks.BipartiteWalkReverseStateTransfer.PerfectStateTransfer}\left(\operatorname{D5.S3.Quantum.Walks.BipartiteWalkReverseStateTransfer.Udef}, (5: \operatorname{Fin}\left(7\right)), (0: \operatorname{Fin}\left(7\right))\right))) \land (\neg (\operatorname{D5.S3.Quantum.Walks.BipartiteWalkReverseStateTransfer.PerfectStateTransfer}\left(\operatorname{D5.S3.Quantum.Walks.BipartiteWalkReverseStateTransfer.Udisp}, (5: \operatorname{Fin}\left(7\right)), (0: \operatorname{Fin}\left(7\right))\right))))$$

*Formalization.* `D5/S3/Quantum/Walks/BipartiteWalkReverseStateTransfer.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Qiuting Chen; Chris Godsil; Mariia Sobchuk; Hanmeng Zhan (2024). *Hamiltonians of bipartite walks*. DOI: [10.37236/12040](https://doi.org/10.37236/12040). URL: <https://arxiv.org/abs/2207.01673v1>.

*Commentary.*

Neither the product of reflections nor the printed matrix admits perfect state transfer from index 5 to index 0. These are the source's sixth and first coordinate states. This states the suspicion in Hamiltonian_7.tex, line 1288, for both choices of matrix, including the discrepancy in their row 2, column 4 entries.

**Theorem 1.7 (The modulo-three obstruction).**

$$\operatorname{D5.S3.Quantum.Walks.BipartiteWalkReverseStateTransfer.claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Walks/BipartiteWalkReverseStateTransfer.result` (`✓ std3`). ∎

*Resolves.* `Problems/chen-godsil-sobchuk-zhan-2024-bipartite-walk-reverse-state-transfer` (proved) by `D5/S3/Quantum/Walks/BipartiteWalkReverseStateTransfer.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"chen-godsil-sobchuk-zhan-2024-bipartite-walk-reverse-state-transfer","declaration_gid":"D5/S3/Quantum/Walks/BipartiteWalkReverseStateTransfer.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Qiuting Chen; Chris Godsil; Mariia Sobchuk; Hanmeng Zhan (2024). *Hamiltonians of bipartite walks*. DOI: [10.37236/12040](https://doi.org/10.37236/12040). URL: <https://arxiv.org/abs/2207.01673v1>.

*Commentary.*

Use zero-based coordinate vectors eⱼ. For an integer s, let Aₛ be the integer matrix whose entries are those of 3 Udisp, except that the entry at row 2, column 4 is s. Entrywise inclusion of integers into the complex numbers gives 3 • Udef = A₋₁ and 3 • Udisp = A₁. Thus either matrix U has the form U = (1/3) • Aₛ for its corresponding s.

Set x = (−1,0,2,2,0,0,0) and y = (2,0,0,−2,2,−1,0), as integer column vectors. Direct multiplication gives Aₛ e₁ = x and Aₛ x = (4,0,4,−2,6,−3,0) = 2 • x + 3 • y, independently of s. The same matrix entries and the scaling of U give U e₅ = e₆ and U e₆ = e₁.

Reduce the integer matrix and vector entrywise to ZMod 3. The image of x is a nonzero eigenvector of the image of Aₛ with eigenvalue 2: its coordinate zero is −1. Taking the nth power of this eigenvector identity gives Aₛⁿ x = 2ⁿ • x in ZMod 3 for every natural n.

Now include the integer vectors entrywise in the complex vector space. The first two steps and Aₛ e₁ = x give U³ e₅ = (1/3) • x. The equality U = (1/3) • Aₛ gives Uⁿ x = (1/3)ⁿ • Aₛⁿ x, hence Uⁿ⁺³ e₅ = (1/3)ⁿ⁺¹ • Aₛⁿ x. If aₙ is coordinate zero of the integer vector Aₛⁿ x, the zero coordinate of Uⁿ⁺³ e₅ is the complex inclusion of aₙ divided by 3ⁿ⁺¹.

For any integer a with nonzero image in ZMod 3, the complex number a/3ⁿ⁺¹ cannot have norm one. Otherwise the complex norm identity gives |a| = 3ⁿ⁺¹ first in the reals and then in the integers. Since n + 1 is positive, 3 divides |a| and therefore a, contrary to its nonzero image.

At steps zero, one and two, the zero coordinate of Uᵏ e₅ is zero. At step n + 3, the congruence gives aₙ = −2ⁿ in ZMod 3. Here 2 = −1 is a unit, so aₙ is nonzero modulo three. The preceding norm argument therefore excludes a unit-norm zero coordinate at every natural step.

If perfect state transfer from index 5 to index 0 existed with phase γ, coordinate zero of Uᵏ e₅ = γ • e₀ would equal γ and would have norm one. This contradicts the coordinate bound. Applying the argument with s = −1 to Udef and with s = 1 to Udisp proves both exclusions.

## References

- Truth anchor: `D5/S3/Quantum/Walks/BipartiteWalkReverseStateTransfer.P`
- Truth anchor: `D5/S3/Quantum/Walks/BipartiteWalkReverseStateTransfer.PerfectStateTransfer`
- Truth anchor: `D5/S3/Quantum/Walks/BipartiteWalkReverseStateTransfer.Q`
- Truth anchor: `D5/S3/Quantum/Walks/BipartiteWalkReverseStateTransfer.Udef`
- Truth anchor: `D5/S3/Quantum/Walks/BipartiteWalkReverseStateTransfer.Udisp`
- Truth anchor: `D5/S3/Quantum/Walks/BipartiteWalkReverseStateTransfer.claim`
- Truth anchor: `D5/S3/Quantum/Walks/BipartiteWalkReverseStateTransfer.result`
