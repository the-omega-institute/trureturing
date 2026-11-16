# Page and Multi-entropy large-mode formulas

## Abstract

At replica order three, the Page and equal-tripartition configurations have logarithmic large-mode formulas with explicit errors for each fixed squeezing parameter.

**Definition 1.1 (The quantified answer).**

$$claim= (\forall (a: \mathbb{R}), ((1<a) \implies (\exists (K: \mathbb{R}), ((0<K) \land (\forall (k: \mathbb{N}), ((0<k) \implies ((\operatorname{abs}\left(\operatorname{GaussianMultiEntropyAsymptotic.GM3}\left(3, 2 \cdot k, k, k, a\right)+\frac{1}{12} \cdot \operatorname{Real.log}\left((4 \cdot (k: \mathbb{R})) \cdot (a^2-1)\right)-\frac{1}{12} \cdot \operatorname{Real.log}\left(\frac{400}{27}\right)\right) \leq \frac{K}{4 \cdot (k: \mathbb{R})}) \land (\operatorname{abs}\left(\operatorname{GaussianMultiEntropyAsymptotic.GM3}\left(3, k, k, k, a\right)+\frac{1}{12} \cdot \operatorname{Real.log}\left((3 \cdot (k: \mathbb{R})) \cdot (a^2-1)\right)-\frac{1}{12} \cdot \operatorname{Real.log}\left(\frac{27}{2}\right)\right) \leq \frac{K}{3 \cdot (k: \mathbb{R})}))))))))$$

*Formalization.* `D5/S3/Quantum/GaussianStates/PageMultiEntropyLargeN.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. A. Camargo, M. Nishida (2026). *Genuine Multi-Entropy of Fully Symmetric Gaussian States*. DOI: [10.48550/arXiv.2609.30754](https://doi.org/10.48550/arXiv.2609.30754). URL: <https://arxiv.org/abs/2609.30754v2>.

*Commentary.*

Section 6, printed page 18 (PDF page 19), after equations (63)–(64): “It would be very interesting to obtain similar analytic formulas for the subsystem configurations corresponding to the Page and Multi-entropy times in the large N regime. This would be particularly important to determine the behavior of GM₃³ in other relevant subsystem configurations.” The displayed proposition specifies an answer at replica order three; its coefficients are derived here. The real parameter a is fixed above one. The positive natural k indexes Page sizes (2k,k,k), of total 4k, and equal sizes (k,k,k), of total 3k. The same positive real K bounds both errors for every positive k and may depend on a. GM3 is the normalized Gaussian replica-integral quantity defined in GaussianMultiEntropyAsymptotic; the coercions of k in the logarithms and error denominators are into the reals.

**Theorem 1.2 (The two error bounds).**

$$\forall (a: \mathbb{R}), ((1<a) \implies (\exists (K: \mathbb{R}), ((0<K) \land (\forall (k: \mathbb{N}), ((0<k) \implies ((\operatorname{abs}\left(\operatorname{GaussianMultiEntropyAsymptotic.GM3}\left(3, 2 \cdot k, k, k, a\right)+\frac{1}{12} \cdot \operatorname{Real.log}\left((4 \cdot (k: \mathbb{R})) \cdot (a^2-1)\right)-\frac{1}{12} \cdot \operatorname{Real.log}\left(\frac{400}{27}\right)\right) \leq \frac{K}{4 \cdot (k: \mathbb{R})}) \land (\operatorname{abs}\left(\operatorname{GaussianMultiEntropyAsymptotic.GM3}\left(3, k, k, k, a\right)+\frac{1}{12} \cdot \operatorname{Real.log}\left((3 \cdot (k: \mathbb{R})) \cdot (a^2-1)\right)-\frac{1}{12} \cdot \operatorname{Real.log}\left(\frac{27}{2}\right)\right) \leq \frac{K}{3 \cdot (k: \mathbb{R})})))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/GaussianStates/PageMultiEntropyLargeN.result` (`✓ std3`). ∎

*Resolves.* `Problems/camni2609p` (proved) by `D5/S3/Quantum/GaussianStates/PageMultiEntropyLargeN.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"camni2609p","declaration_gid":"D5/S3/Quantum/GaussianStates/PageMultiEntropyLargeN.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* H. A. Camargo, M. Nishida (2026). *Genuine Multi-Entropy of Fully Symmetric Gaussian States*. DOI: [10.48550/arXiv.2609.30754](https://doi.org/10.48550/arXiv.2609.30754). URL: <https://arxiv.org/abs/2609.30754v2>.

*Commentary.*

The nine-replica Gram matrix has one constant mode and four paired character classes. Its determinant factors into the corresponding positive scalar factors. The source radical satisfies N²(a²−1)=(N−1)(1−r)²/r, which cancels r from the entropy expression. Substitution at the two tripartitions gives the constants 400/27 and 27/2. The inequalities for log(1+h) and log(1−1/N) give the common choice K=(2+30/(a²−1))/12. This estimate is for each fixed a>1 and does not assert uniformity as a approaches one.

## References

- Truth anchor: `D5/S3/Quantum/GaussianStates/PageMultiEntropyLargeN.claim`
- Truth anchor: `D5/S3/Quantum/GaussianStates/PageMultiEntropyLargeN.result`
- Dependency: [D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThree](../Entanglement/GaussianMultiEntropy/ReplicaThree.md)
- Dependency: [D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeScalar](../Entanglement/GaussianMultiEntropy/ReplicaThreeScalar.md)
- Dependency: [D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ResidualLimit](../Entanglement/GaussianMultiEntropy/ResidualLimit.md)
- Dependency: [D5/S3/Quantum/Entanglement/GaussianMultiEntropyAsymptotic](../Entanglement/GaussianMultiEntropyAsymptotic.md)
