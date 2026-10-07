# HiguchiSudberyEntropyMaximum

## Abstract

The explicit Higuchi–Sudbery state attains the sharp upper bound for the average two-qubit marginal entropy.

**Definition 1.1 (The Higuchi–Sudbery amplitudes).**

$$\forall (i : \operatorname{Fin}\left(16\right)), (\operatorname{M4}\left(i\right) = \frac{1}{\operatorname{Complex.ofReal}\left(\operatorname{Real.sqrt}\left(6\right)\right)}\cdot (\operatorname{ite}\left((i = 3) \lor (i = 12), 1, \operatorname{ite}\left((i = 5) \lor (i = 10), \operatorname{QuditSwappingProductBoundRefutation.omega}\left(3\right), \operatorname{ite}\left((i = 6) \lor (i = 9), \operatorname{QuditSwappingProductBoundRefutation.omega}\left(3\right)^{2}, 0\right)\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/HiguchiSudbery/HiguchiSudberyEntropyMaximum.M4` (`✓ std3`).

*Citation.* A. Higuchi; A. Sudbery (2000). *How entangled can two couples get?*. DOI: [10.1016/S0375-9601(00)00506-4](https://doi.org/10.1016/S0375-9601(00)00506-4). URL: <https://arxiv.org/abs/quant-ph/0005013>.

*Commentary.*

Section 3, p. 5: |M₄⟩ = 1/√6 [|0011⟩ + |1100⟩ + ω(|1010⟩ + |0101⟩) + ω²(|1001⟩ + |0110⟩)]. The basis index is 8a+4b+2c+d. The piecewise values are complex and the real square root is coerced to Complex.

**Definition 1.2 (The Higuchi–Sudbery maximum claim).**

$$\operatorname{claim} = \left((\forall (z : \operatorname{Fin}\left(16\right) \to \operatorname{Complex}), (\forall (h : \sum_{i \in \operatorname{Fin}\left(16\right)} \operatorname{Complex.normSq}\left(z\left(i\right)\right) = 1), (\operatorname{averageEntropy}\left(z, h\right) \le 1+\frac{1}{2}\cdot \operatorname{Real.logb}\left(2, 3\right)))) \land (\exists (h : \sum_{i \in \operatorname{Fin}\left(16\right)} \operatorname{Complex.normSq}\left(\operatorname{M4}\left(i\right)\right) = 1), \operatorname{averageEntropy}\left(\operatorname{M4}, h\right) = 1+\frac{1}{2}\cdot \operatorname{Real.logb}\left(2, 3\right))\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/HiguchiSudbery/HiguchiSudberyEntropyMaximum.claim` (`✓ std3`).

*Citation.* A. Higuchi; A. Sudbery (2000). *How entangled can two couples get?*. DOI: [10.1016/S0375-9601(00)00506-4](https://doi.org/10.1016/S0375-9601(00)00506-4). URL: <https://arxiv.org/abs/quant-ph/0005013>.

*Commentary.*

Section 3, p. 5: “Given that a four-qubit state cannot have maximal entropy of entanglement for every two-qubit subset, we now ask what is the greatest possible average for such entropies, i.e. we seek to maximise”. The displayed average is one third of the AB, AC and AD entropies. The encoding uses all normalized vectors Fin 16 → Complex, with index 8a+4b+2c+d. The second conjunct is attainment at the explicit M4 and does not assert uniqueness.

**Theorem 1.3 (Sharp global bound and attainment).**

$$(\forall (z : \operatorname{Fin}\left(16\right) \to \operatorname{Complex}), (\forall (h : \sum_{i \in \operatorname{Fin}\left(16\right)} \operatorname{Complex.normSq}\left(z\left(i\right)\right) = 1), (\operatorname{averageEntropy}\left(z, h\right) \le 1+\frac{1}{2}\cdot \operatorname{Real.logb}\left(2, 3\right)))) \land (\exists (h : \sum_{i \in \operatorname{Fin}\left(16\right)} \operatorname{Complex.normSq}\left(\operatorname{M4}\left(i\right)\right) = 1), \operatorname{averageEntropy}\left(\operatorname{M4}, h\right) = 1+\frac{1}{2}\cdot \operatorname{Real.logb}\left(2, 3\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/HiguchiSudbery/HiguchiSudberyEntropyMaximum.result` (`✓ std3`). ∎

*Resolves.* `Problems/higuchi-sudbery-2000-four-qubit-average-entropy-maximum` (proved) by `D5/S3/Quantum/Entanglement/HiguchiSudbery/HiguchiSudberyEntropyMaximum.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"higuchi-sudbery-2000-four-qubit-average-entropy-maximum","declaration_gid":"D5/S3/Quantum/Entanglement/HiguchiSudbery/HiguchiSudberyEntropyMaximum.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* A. Higuchi; A. Sudbery (2000). *How entangled can two couples get?*. DOI: [10.1016/S0375-9601(00)00506-4](https://doi.org/10.1016/S0375-9601(00)00506-4). URL: <https://arxiv.org/abs/quant-ph/0005013>.

*Commentary.*

The proof combines the cubic negMulLog majorant, the purity lower bound, and the exact degree-six minor certificate. The marginal spectra of M4 attain equality.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/HiguchiSudbery/HiguchiSudberyEntropyMaximum.M4`
- Truth anchor: `D5/S3/Quantum/Entanglement/HiguchiSudbery/HiguchiSudberyEntropyMaximum.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/HiguchiSudbery/HiguchiSudberyEntropyMaximum.result`
- Dependency: [D5/S3/Quantum/Entanglement/HiguchiSudbery/PrimeHierarchyCertificate](PrimeHierarchyCertificate.md)
- Dependency: [D5/S3/Quantum/Entanglement/HiguchiSudbery/ReflectionEvaluation](ReflectionEvaluation.md)
- Dependency: [D5/S3/Quantum/Entanglement/QuditSwappingProductBoundRefutation](../QuditSwappingProductBoundRefutation.md)
