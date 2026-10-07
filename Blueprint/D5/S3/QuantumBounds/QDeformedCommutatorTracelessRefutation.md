# A traceless counterexample to the q-deformed commutator bound

## Abstract

Two traceless complex matrices of size five violate the proposed q-deformed commutator inequality at q = 2.

**Definition 1.1 (The inequality in Conjecture 1).**

$$claim \iff \forall n : \mathbb{N}, \forall q : \mathbb{R}, 0 < q \to \forall A B : Matrix (Fin n) (Fin n) \mathbb{C}, (\operatorname{trace}\left(A\right) = 0 \lor \operatorname{trace}\left(B\right) = 0) \to \operatorname{mass}\left(A B - q \cdot (B A)\right) \leq (1 + q^{2}) \cdot \operatorname{mass}\left(A\right) \cdot \operatorname{mass}\left(B\right)$$

*Formalization.* `D5/S3/QuantumBounds/QDeformedCommutatorTracelessRefutation.claim` (`✓ std3`).

*Citation.* D. Chruściński, G. Kimura, H. Ohno, T. Singal (2022). *Bounding the Frobenius norm of a q-deformed commutator*. DOI: [10.48550/arXiv.2202.11520](https://doi.org/10.48550/arXiv.2202.11520). URL: <https://arxiv.org/abs/2202.11520v2>.

*Commentary.*

Chruściński, Kimura, Ohno and Singal define the q-deformed commutator by [A,B]q = AB − qBA. Conjecture 1 in Section 3 states: “For any q > 0, if A or B is traceless, the inequality (7) holds and is sharp.” Here mass M = ∑ᵢ ∑ⱼ |M i j|² is the squared Frobenius norm, using the existing definition from the Moreau–Yosida module. Fin n indexes the rows and columns by 0,…,n−1. The real scalar q is embedded in C for scalar multiplication of matrices. The displayed claim is the inequality clause for every dimension n, every positive real q and every pair of complex matrices satisfying the disjunction of trace conditions. A violation of this clause also refutes the conjunction that the inequality holds and is sharp.

**Theorem 1.2 (A five-dimensional counterexample).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/QDeformedCommutatorTracelessRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/chruscinski-2022-qdeformed-commutator-traceless-refutation` (refuted) by `D5/S3/QuantumBounds/QDeformedCommutatorTracelessRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"chruscinski-2022-qdeformed-commutator-traceless-refutation","declaration_gid":"D5/S3/QuantumBounds/QDeformedCommutatorTracelessRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* D. Chruściński, G. Kimura, H. Ohno, T. Singal (2022). *Bounding the Frobenius norm of a q-deformed commutator*. DOI: [10.48550/arXiv.2202.11520](https://doi.org/10.48550/arXiv.2202.11520). URL: <https://arxiv.org/abs/2202.11520v2>.

*Commentary.*

Take q = 2 and n = 5. Let A = [6,42; 0,−3] ⊕ (−I₃) and B = [6,0; −42,−3] ⊕ (−I₃), where the bracketed arrays are two-by-two matrices and I₃ is the three-by-three identity. Both traces are 6 − 3 − 1 − 1 − 1 = 0. Their squared Frobenius norms are mass A = mass B = 1812. Direct multiplication gives AB − 2BA = [−1800,−630; 630,3519] ⊕ (−I₃), with mass (AB − 2BA) = 16417164. The proposed upper bound is (1 + 2²) · mass A · mass B = 5 · 1812² = 16416720. Thus 16417164 > 16416720, exceeding the bound by 444 and contradicting claim.

## References

- Truth anchor: `D5/S3/QuantumBounds/QDeformedCommutatorTracelessRefutation.claim`
- Truth anchor: `D5/S3/QuantumBounds/QDeformedCommutatorTracelessRefutation.result`
- Dependency: [D5/S3/Quantum/Entanglement/MoreauYosidaFormationSelectiveLoccRefutation](../Quantum/Entanglement/MoreauYosidaFormationSelectiveLoccRefutation.md)
