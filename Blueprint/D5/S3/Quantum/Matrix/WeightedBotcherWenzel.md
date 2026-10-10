# Weighted Bottcher-Wenzel, case (ii)

## Abstract

The squared weighted Bottcher-Wenzel conjecture holds for every positive definite weight.

**Definition 1.1 (Squared weighted Frobenius norm).**

$$\forall n \in \mathbb{N}, A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), W \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; \operatorname{weightedSq}\left(A, W\right) = \operatorname{Complex.re}(\operatorname{Matrix.trace}(\operatorname{Matrix.conjTranspose}(A) \cdot A \cdot W))$$

*Formalization.* `D5/S3/Quantum/Matrix/WeightedBotcherWenzel.weightedSq` (`✓ std3`).

*Citation.* Aina Mayumi; Gen Kimura; Hiromichi Ohno; Dariusz Chruściński (2024). *Böttcher-Wenzel inequality for weighted Frobenius norms and its application to quantum physics*. DOI: [10.1016/j.laa.2024.07.013](https://doi.org/10.1016/j.laa.2024.07.013). URL: <https://arxiv.org/abs/2403.04199v2>.

*Commentary.*

The source defines: “In what follows we call ω-weighted Frobenius norm” followed by “‖A‖ω := √tr(A∗Aω)” (equation (2), page 2). This is its literal squared trace expression, using the real part for the real-valued result.

**Theorem 1.2 (Additive weight dependence).**

$$\forall n \in \mathbb{N}, A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), W \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), V \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; \operatorname{weightedSq}\left(A, W + V\right) = \operatorname{weightedSq}\left(A, W\right) + \operatorname{weightedSq}\left(A, V\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/WeightedBotcherWenzel.weighted_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Trace and right matrix multiplication are additive in the weight.

**Theorem 1.3 (Real scaling of the weight).**

$$\forall n \in \mathbb{N}, A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), W \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), t \in \mathbb{R},\; \operatorname{weightedSq}\left(A, t\cdot(W)\right) = t \cdot \operatorname{weightedSq}\left(A, W\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/WeightedBotcherWenzel.weighted_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real part of the trace respects real scalar multiplication.

**Theorem 1.4 (Identity weight).**

$$\forall n \in \mathbb{N}, A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; \operatorname{weightedSq}\left(A, 1\right) = \operatorname{RHLinalg.frobSq}(A)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/WeightedBotcherWenzel.weighted_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The identity weight gives the ordinary Frobenius square.

**Theorem 1.5 (Projection weight equals projected norm).**

$$\forall n \in \mathbb{N}, A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), P \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; \left(\operatorname{Matrix.IsHermitian}(P) \land P \cdot P = P\right) \Rightarrow \operatorname{weightedSq}\left(A, P\right) = \operatorname{RHLinalg.frobSq}(A \cdot P)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/WeightedBotcherWenzel.projected_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Hermiticity and idempotence permit trace cycling to the Gram matrix of AP.

**Theorem 1.6 (Projection commutator channel bound).**

$$\forall n \in \mathbb{N}, A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), B \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), P \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; \left(\operatorname{Matrix.IsHermitian}(P) \land P \cdot P = P\right) \Rightarrow \operatorname{RHLinalg.frobSq}(\operatorname{commutator}\left(A, B\right) \cdot P) \le \left(\operatorname{RHLinalg.frobSq}(A) + 2 \cdot \operatorname{RHLinalg.frobSq}(A \cdot P) + 2 \cdot \operatorname{Real.sqrt}(\operatorname{RHLinalg.frobSq}(A \cdot P) \cdot \operatorname{gap}\left(A\right))\right) \cdot \operatorname{RHLinalg.frobSq}(B)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/WeightedBotcherWenzel.projection_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The SVD expresses a contraction as an average of two actual unitaries. A common-radius bound for scalar pencils transfers to the projected adjoint channel, for every projection rank and including zero input matrices.

**Definition 1.7 (Attained spectral endpoints).**

$$\forall n \in \mathbb{N}, W \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), lo \in \mathbb{R}, hi \in \mathbb{R},\; \operatorname{SpectralExtrema}\left(W, lo, hi\right) \Leftrightarrow \left(\exists h \in \operatorname{Matrix.IsHermitian}(W),\; \left(\forall i \in \operatorname{Fin}\left(n\right),\; lo \le \operatorname{eigenvalues}\left(h\right)(i) \land \operatorname{eigenvalues}\left(h\right)(i) \le hi\right) \land \left(\left(\exists i \in \operatorname{Fin}\left(n\right),\; \operatorname{eigenvalues}\left(h\right)(i) = lo\right) \land \left(\exists i \in \operatorname{Fin}\left(n\right),\; \operatorname{eigenvalues}\left(h\right)(i) = hi\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Matrix/WeightedBotcherWenzel.SpectralExtrema` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every eigenvalue lies between lo and hi, and each endpoint is attained. Thus these parameters are exactly the smallest and largest eigenvalues, including repeated eigenvalues.

**Definition 1.8 (Conjecture 1, equation (15)).**

$$claim \Leftrightarrow (\forall n \in \mathbb{N},\; 0 < n \Rightarrow \left(\forall W \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), lo \in \mathbb{R}, hi \in \mathbb{R},\; \operatorname{Matrix.PosDef}(W) \Rightarrow \left(0 < lo \Rightarrow \left(\operatorname{SpectralExtrema}\left(W, lo, hi\right) \Rightarrow \left(\forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), B \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; \operatorname{weightedSq}\left(\operatorname{commutator}\left(A, B\right), W\right) \le \left(1 + \frac{hi}{lo}\right) \cdot \operatorname{weightedSq}\left(A, W\right) \cdot \operatorname{RHLinalg.frobSq}(B)\right)\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/Matrix/WeightedBotcherWenzel.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Aina Mayumi; Gen Kimura; Hiromichi Ohno; Dariusz Chruściński (2024). *Böttcher-Wenzel inequality for weighted Frobenius norms and its application to quantum physics*. DOI: [10.1016/j.laa.2024.07.013](https://doi.org/10.1016/j.laa.2024.07.013). URL: <https://arxiv.org/abs/2403.04199v2>.

*Commentary.*

“Conjecture 1. For any matrices A, B ∈ Mₙ(ℂ),” followed by equation (15), “‖[A, B]‖ω ≤ √((λm + λM)/λm) ‖A‖ω ‖B‖” (arXiv:2403.04199v2, page 6). The encoding uses Matrix (Fin n) (Fin n) ℂ for n greater than zero, PosDef for the positive definite weight, and SpectralExtrema for the attained endpoints lo = λm and hi = λM. Squaring the nonnegative norms gives constant 1 + hi/lo. The weighted and ordinary squares are the real trace formulas; commutator means AB minus BA.

**Theorem 1.9 (The weighted inequality).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/WeightedBotcherWenzel.result` (`✓ std3`). ∎

*Resolves.* `Problems/mayumi-kimura-ohno-chruscinski-2024-weighted-bottcher-wenzel-ii` (proved) by `D5/S3/Quantum/Matrix/WeightedBotcherWenzel.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mayumi-kimura-ohno-chruscinski-2024-weighted-bottcher-wenzel-ii","declaration_gid":"D5/S3/Quantum/Matrix/WeightedBotcherWenzel.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Aina Mayumi; Gen Kimura; Hiromichi Ohno; Dariusz Chruściński (2024). *Böttcher-Wenzel inequality for weighted Frobenius norms and its application to quantum physics*. DOI: [10.1016/j.laa.2024.07.013](https://doi.org/10.1016/j.laa.2024.07.013). URL: <https://arxiv.org/abs/2403.04199v2>.

*Commentary.*

The projection channel bound and nonnegative commutator gap give a square-completion lower bound for every two-level weight. A spectral convex decomposition transfers the inequality to an arbitrary positive definite weight. This statement is case (ii). Cases (i) and (iv) are separate questions.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/WeightedBotcherWenzel.SpectralExtrema`
- Truth anchor: `D5/S3/Quantum/Matrix/WeightedBotcherWenzel.claim`
- Truth anchor: `D5/S3/Quantum/Matrix/WeightedBotcherWenzel.projected_trace`
- Truth anchor: `D5/S3/Quantum/Matrix/WeightedBotcherWenzel.projection_gap`
- Truth anchor: `D5/S3/Quantum/Matrix/WeightedBotcherWenzel.result`
- Truth anchor: `D5/S3/Quantum/Matrix/WeightedBotcherWenzel.weightedSq`
- Truth anchor: `D5/S3/Quantum/Matrix/WeightedBotcherWenzel.weighted_add`
- Truth anchor: `D5/S3/Quantum/Matrix/WeightedBotcherWenzel.weighted_one`
- Truth anchor: `D5/S3/Quantum/Matrix/WeightedBotcherWenzel.weighted_smul`
- Dependency: [D5/S3/Quantum/Foundation/FiniteTraceDistance](../Foundation/FiniteTraceDistance.md)
- Dependency: [D5/S3/Quantum/Matrix/CommutatorGap](CommutatorGap.md)
