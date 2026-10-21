# A positive block does not force normality

## Abstract

An admissible scalar pair gives a positive block for a nonnormal complex matrix.

**Definition 1.1 (The source block matrix).**

$$\forall (f: \mathbb{R}\to\mathbb{R}), \forall (g: \mathbb{R}\to\mathbb{R}), \forall (n: \mathbb{N}), \forall (A: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), \operatorname{block}\left(f, g, A\right) = \operatorname{Matrix.fromBlocks}\left(\operatorname{cfc}\left(f, \operatorname{CFC.sqrt}\left(\operatorname{Matrix.conjTranspose}\left(A\right) \cdot A\right)\right), \operatorname{Matrix.conjTranspose}\left(A\right), A, \operatorname{cfc}\left(g, \operatorname{CFC.sqrt}\left(\operatorname{Matrix.conjTranspose}\left(A\right) \cdot A\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Matrix/ZhangJingBlockNormalityRefutation.block` (`✓ std3`).

*Citation.* Feng Zhang; Hefang Jing (2025). *More inequalities for positive semidefinite matrices*. DOI: [10.13001/ela.2025.9201](https://doi.org/10.13001/ela.2025.9201). URL: <https://doi.org/10.13001/ela.2025.9201>.

*Commentary.*

The source defines ‘|A| = (A*A)^{1/2} and A* is the conjugate transpose of A’ (p. 595). Question 2.14 (p. 601) states: “Let A ∈ M_n. Then [[f(|A|), A*], [A, g(|A|)]] ≥ 0 if and only if A is normal under the conditions that f(x)g(x) = x² for x ≥ 0, f(x) ≥ g(x) (x ≥ 1) and g(x) ≥ f(x) (0 ≤ x ≤ 1).” Here Matrix.conjTranspose is A*, and CFC.sqrt gives the positive square root of A* A. The real functions are applied by cfc. Matrix.fromBlocks places these four blocks in the displayed order; its index type is Fin n ⊕ Fin n.

**Definition 1.2 (Question 2.14 as a universal equivalence).**

$$(claim) \Leftrightarrow (\forall (f: \mathbb{R}\to\mathbb{R}), \forall (g: \mathbb{R}\to\mathbb{R}), (\forall (x: \mathbb{R}), (0 \le x) \Rightarrow (f\left(x\right) \cdot g\left(x\right) = x^{2})) \Rightarrow ((\forall (x: \mathbb{R}), (1 \le x) \Rightarrow (g\left(x\right) \le f\left(x\right))) \Rightarrow ((\forall (x: \mathbb{R}), (0 \le x) \Rightarrow ((x \le 1) \Rightarrow (f\left(x\right) \le g\left(x\right)))) \Rightarrow (\forall (n: \mathbb{N}), \forall (A: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), (\operatorname{Matrix.PosSemidef}\left(\operatorname{block}\left(f, g, A\right)\right)) \Leftrightarrow (\operatorname{Matrix.conjTranspose}\left(A\right) \cdot A = A \cdot \operatorname{Matrix.conjTranspose}\left(A\right))))))$$

*Formalization.* `D5/S3/Quantum/Matrix/ZhangJingBlockNormalityRefutation.claim` (`✓ std3`).

*Citation.* Feng Zhang; Hefang Jing (2025). *More inequalities for positive semidefinite matrices*. DOI: [10.13001/ela.2025.9201](https://doi.org/10.13001/ela.2025.9201). URL: <https://doi.org/10.13001/ela.2025.9201>.

*Commentary.*

Question 2.14 (p. 601): “Let A ∈ M_n. Then [[f(|A|), A*], [A, g(|A|)]] ≥ 0 if and only if A is normal under the conditions that f(x)g(x) = x² for x ≥ 0, f(x) ≥ g(x) (x ≥ 1) and g(x) ≥ f(x) (0 ≤ x ≤ 1).” The proposition quantifies over every pair of real functions f,g satisfying the three scalar conditions, every natural dimension n, and every complex matrix on Fin n. Nonnegativity of the block is Matrix.PosSemidef, and normality is the equality of A* A and A A*. Fin n labels the source's n indices from zero. No continuity, invertibility or spectral injectivity hypothesis is added.

**Theorem 1.3 (The universal equivalence is false).**

$$\neg (\forall (f: \mathbb{R}\to\mathbb{R}), \forall (g: \mathbb{R}\to\mathbb{R}), (\forall (x: \mathbb{R}), (0 \le x) \Rightarrow (f\left(x\right) \cdot g\left(x\right) = x^{2})) \Rightarrow ((\forall (x: \mathbb{R}), (1 \le x) \Rightarrow (g\left(x\right) \le f\left(x\right))) \Rightarrow ((\forall (x: \mathbb{R}), (0 \le x) \Rightarrow ((x \le 1) \Rightarrow (f\left(x\right) \le g\left(x\right)))) \Rightarrow (\forall (n: \mathbb{N}), \forall (A: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), (\operatorname{Matrix.PosSemidef}\left(\operatorname{block}\left(f, g, A\right)\right)) \Leftrightarrow (\operatorname{Matrix.conjTranspose}\left(A\right) \cdot A = A \cdot \operatorname{Matrix.conjTranspose}\left(A\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/ZhangJingBlockNormalityRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/zhang-jing-2025-block-normality-question-2-14` (refuted) by `D5/S3/Quantum/Matrix/ZhangJingBlockNormalityRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zhang-jing-2025-block-normality-question-2-14","declaration_gid":"D5/S3/Quantum/Matrix/ZhangJingBlockNormalityRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Feng Zhang; Hefang Jing (2025). *More inequalities for positive semidefinite matrices*. DOI: [10.13001/ela.2025.9201](https://doi.org/10.13001/ela.2025.9201). URL: <https://doi.org/10.13001/ela.2025.9201>.

*Commentary.*

Set g(x)=1+(x−1)/(1+(x−1)²) and f(x)=x²/g(x). The denominator is positive, g is positive on the real line, and the three scalar conditions hold on their respective ranges. Take A=[[0,3/2],[3,0]]. Then |A|=diag(3,3/2), f(|A|)=diag(45/7,45/28), and g(|A|)=(7/5)I: the distinct singular values 3 and 3/2 have the same value under g. For the block row Q=[A,(7/5)I], the block equals (5/7)Q*Q and is positive semidefinite. However, the (0,0) entries of A* A and A A* are 9 and 9/4, so A is not normal. The refutation uses this fixed two-dimensional example; no general injectivity criterion or classification of singular matrices is asserted. In this pair f(0)=0; strict positivity of f holds only for x>0.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/ZhangJingBlockNormalityRefutation.block`
- Truth anchor: `D5/S3/Quantum/Matrix/ZhangJingBlockNormalityRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Matrix/ZhangJingBlockNormalityRefutation.result`
- Dependency: [D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity](../Dynamics/EntropyProductionCoherenceDeletionIdentity.md)
