# A counterexample to the negative-q commutator bound

## Abstract

A traceless complex matrix of size three and a rank-one projector violate the proposed q-deformed commutator inequality at q = −1.

**Definition 1.1 (The dimension-dependent coefficient).**

$$\forall n : \mathbb{N}, \operatorname{g}\left(n\right) = \frac{(n : \mathbb{R})^{2} - 3 \cdot (n : \mathbb{R}) + 3}{(n : \mathbb{R}) \cdot ((n : \mathbb{R}) - 1)}$$

*Formalization.* `D5/S3/QuantumBounds/QDeformedCommutatorNegativeQRefutation.g` (`✓ std3`).

*Citation.* D. Chruściński, G. Kimura, H. Ohno, T. Singal (2022). *Bounding the Frobenius norm of a q-deformed commutator*. DOI: [10.48550/arXiv.2202.11520](https://doi.org/10.48550/arXiv.2202.11520). URL: <https://arxiv.org/abs/2202.11520v2>.

*Commentary.*

Equation (24) defines the real coefficient g(n) = (n² − 3n + 3)/(n(n − 1)). The natural number n is embedded in the real numbers in every arithmetic operation. For n at least two, the denominator is positive. As a total real-valued function, g uses the real division convention also at n = 0 and n = 1; the inequality below only concerns n at least two.

**Definition 1.2 (The inequality in Conjecture 2).**

$$claim \iff \forall n : \mathbb{N}, 2 \leq n \to \forall q : \mathbb{R}, q \leq 0 \to \forall A B : Matrix (Fin n) (Fin n) \mathbb{C}, (\operatorname{trace}\left(A\right) = 0 \lor \operatorname{trace}\left(B\right) = 0) \to \operatorname{mass}\left(A \cdot B - (q : \mathbb{C}) \cdot (B \cdot A)\right) \leq \operatorname{max}\left(\operatorname{g}\left(n\right) \cdot (1 - q)^{2}, 1 + q^{2}\right) \cdot \operatorname{mass}\left(A\right) \cdot \operatorname{mass}\left(B\right)$$

*Formalization.* `D5/S3/QuantumBounds/QDeformedCommutatorNegativeQRefutation.claim` (`✓ std3`).

*Citation.* D. Chruściński, G. Kimura, H. Ohno, T. Singal (2022). *Bounding the Frobenius norm of a q-deformed commutator*. DOI: [10.48550/arXiv.2202.11520](https://doi.org/10.48550/arXiv.2202.11520). URL: <https://arxiv.org/abs/2202.11520v2>.

*Commentary.*

Chruściński, Kimura, Ohno and Singal define [A,B]q = AB − qBA. Conjecture 2 in Section 3 states that, for any q ≤ 0, if A or B is traceless, the sharp bound has coefficient max[g(n)(1 − q)², 1 + q²]. Here mass M = ∑ᵢ ∑ⱼ |M i j|² is the squared Frobenius norm. Fin n indexes rows and columns by 0,…,n−1. The real scalar q is embedded in the complex numbers for scalar multiplication of matrices. The displayed claim is the inequality clause for all dimensions n at least two, all nonpositive real q and all complex matrix pairs satisfying the disjunction of trace conditions. A violation of the inequality also refutes the assertion that it holds and is sharp.

**Theorem 1.3 (A three-dimensional counterexample).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/QDeformedCommutatorNegativeQRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/chruscinski-2022-qdeformed-commutator-negative-q-refutation` (refuted) by `D5/S3/QuantumBounds/QDeformedCommutatorNegativeQRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"chruscinski-2022-qdeformed-commutator-negative-q-refutation","declaration_gid":"D5/S3/QuantumBounds/QDeformedCommutatorNegativeQRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Commentary.*

Take n = 3, q = −1, A = diag(2,−1,−1) and B = diag(1,0,0). The trace of A is 2 − 1 − 1 = 0, while the trace of B is 1. Their squared Frobenius norms are mass A = 6 and mass B = 1. The products satisfy AB = BA = diag(2,0,0), so AB − qBA = diag(4,0,0) and its squared Frobenius norm is 16. Equation (24) gives g(3) = 1/2, hence max[g(3)(1 − (−1))², 1 + (−1)²] = 2. The proposed bound becomes 16 ≤ 2 · 6 · 1 = 12, a contradiction. The disjunction of trace conditions admits this pair because A is traceless; the pair does not satisfy the stronger condition that both matrices are traceless.

## References

- Truth anchor: `D5/S3/QuantumBounds/QDeformedCommutatorNegativeQRefutation.claim`
- Truth anchor: `D5/S3/QuantumBounds/QDeformedCommutatorNegativeQRefutation.g`
- Truth anchor: `D5/S3/QuantumBounds/QDeformedCommutatorNegativeQRefutation.result`
- Dependency: [D5/S3/Quantum/Entanglement/MoreauYosidaFormationSelectiveLoccRefutation](../Quantum/Entanglement/MoreauYosidaFormationSelectiveLoccRefutation.md)
