# Burton--Anwar CSS meromorphic suppression

## Abstract

Every CSS code with logical X and Z strings has coherent error suppression of order at least its distance at 0, infinity, 1 and -1.

**Definition 1.1 (Binary Hamming weight).**

$$\forall n \in \mathbb{N},\; \forall x \in (\operatorname{Fin}\left(n\right)\to\operatorname{ZMod}\left(2\right)),\; \operatorname{wt}\left(x\right) = \operatorname{Finset.card}\left(\operatorname{Finset.filter}\left(\operatorname{fun} (i: \operatorname{Fin}\left(n\right)) \mapsto x\left(i\right) \ne 0, (\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right))\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/CSSMeromorphicSuppression.wt` (`✓ std3`).

*Citation.* Simon Burton; Hussain Anwar (2026). *Meromorphic Quantum Computing*. DOI: [10.48550/arXiv.2605.06251](https://doi.org/10.48550/arXiv.2605.06251). URL: <https://arxiv.org/abs/2605.06251v1>.

*Commentary.*

For a binary vector x on Fin(n), wt is the cardinality of the coordinates where x is nonzero.

**Definition 1.2 (The all-ones vector).**

$$\forall n \in \mathbb{N},\; \forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{one}\left(i\right) = 1$$

*Formalization.* `D5/S3/Quantum/Information/CSSMeromorphicSuppression.one` (`✓ std3`).

*Citation.* Simon Burton; Hussain Anwar (2026). *Meromorphic Quantum Computing*. DOI: [10.48550/arXiv.2605.06251](https://doi.org/10.48550/arXiv.2605.06251). URL: <https://arxiv.org/abs/2605.06251v1>.

*Commentary.*

The vector one has value 1 at every coordinate of Fin(n).

**Definition 1.3 (CSS code data).**

$$\forall n \in \mathbb{N},\; \operatorname{CSSCode}\left(n\right):= \{GX: \operatorname{Submodule}\left(\operatorname{ZMod}\left(2\right), (\operatorname{Fin}\left(n\right)\to\operatorname{ZMod}\left(2\right))\right); GZ: \operatorname{Submodule}\left(\operatorname{ZMod}\left(2\right), (\operatorname{Fin}\left(n\right)\to\operatorname{ZMod}\left(2\right))\right) \mid (\forall x \in (\operatorname{Fin}\left(n\right)\to\operatorname{ZMod}\left(2\right)),\; (x \in GX) \Rightarrow \left(\forall z \in (\operatorname{Fin}\left(n\right)\to\operatorname{ZMod}\left(2\right)),\; (z \in GZ) \Rightarrow \operatorname{dotProduct}\left(x, z\right) = 0\right)) \land ((\forall x \in (\operatorname{Fin}\left(n\right)\to\operatorname{ZMod}\left(2\right)),\; (x \in GX) \Rightarrow \operatorname{dotProduct}\left(x, \operatorname{one}\right) = 0) \land ((\forall z \in (\operatorname{Fin}\left(n\right)\to\operatorname{ZMod}\left(2\right)),\; (z \in GZ) \Rightarrow \operatorname{dotProduct}\left(z, \operatorname{one}\right) = 0) \land ((\neg (\operatorname{one} \in GX)) \land ((\neg (\operatorname{one} \in GZ)) \land ((\operatorname{Odd}\left(n\right)) \land (\operatorname{Module.finrank}\left(\operatorname{ZMod}\left(2\right), GX\right) + \operatorname{Module.finrank}\left(\operatorname{ZMod}\left(2\right), GZ\right) + 1 = n))))))\}$$

*Formalization.* `D5/S3/Quantum/Information/CSSMeromorphicSuppression.CSSCode` (`✓ std3`).

*Citation.* Simon Burton; Hussain Anwar (2026). *Meromorphic Quantum Computing*. DOI: [10.48550/arXiv.2605.06251](https://doi.org/10.48550/arXiv.2605.06251). URL: <https://arxiv.org/abs/2605.06251v1>.

*Commentary.*

A CSSCode n consists of the two displayed Submodule fields GX and GZ. The seven constraints, in order, are commutation, evenX, evenZ, one_not_X, one_not_Z, odd_length and one_qubit.

**Definition 1.4 (Logical Pauli representatives).**

$$\forall n \in \mathbb{N},\; \forall C \in \operatorname{CSSCode}\left(n\right),\; \forall x \in (\operatorname{Fin}\left(n\right)\to\operatorname{ZMod}\left(2\right)),\; \forall z \in (\operatorname{Fin}\left(n\right)\to\operatorname{ZMod}\left(2\right)),\; \operatorname{IsLogical}\left(C, x, z\right) = \left((\forall s \in (\operatorname{Fin}\left(n\right)\to\operatorname{ZMod}\left(2\right)),\; (s \in C.\operatorname{GZ}) \Rightarrow \operatorname{dotProduct}\left(x, s\right) = 0) \land ((\forall s \in (\operatorname{Fin}\left(n\right)\to\operatorname{ZMod}\left(2\right)),\; (s \in C.\operatorname{GX}) \Rightarrow \operatorname{dotProduct}\left(z, s\right) = 0) \land (\neg ((x \in C.\operatorname{GX}) \land (z \in C.\operatorname{GZ}))))\right)$$

*Formalization.* `D5/S3/Quantum/Information/CSSMeromorphicSuppression.IsLogical` (`✓ std3`).

*Citation.* Simon Burton; Hussain Anwar (2026). *Meromorphic Quantum Computing*. DOI: [10.48550/arXiv.2605.06251](https://doi.org/10.48550/arXiv.2605.06251). URL: <https://arxiv.org/abs/2605.06251v1>.

*Commentary.*

IsLogical requires each Pauli component to commute with the opposite stabilizer and excludes the pair in which both components are stabilizers.

**Definition 1.5 (Pauli weight).**

$$\forall n \in \mathbb{N},\; \forall x \in (\operatorname{Fin}\left(n\right)\to\operatorname{ZMod}\left(2\right)),\; \forall z \in (\operatorname{Fin}\left(n\right)\to\operatorname{ZMod}\left(2\right)),\; \operatorname{pauliWeight}\left(x, z\right) = \operatorname{Finset.card}\left(\operatorname{Finset.filter}\left(\operatorname{fun} (i: \operatorname{Fin}\left(n\right)) \mapsto (x\left(i\right) \ne 0) \lor (z\left(i\right) \ne 0), (\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right))\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/CSSMeromorphicSuppression.pauliWeight` (`✓ std3`).

*Citation.* Simon Burton; Hussain Anwar (2026). *Meromorphic Quantum Computing*. DOI: [10.48550/arXiv.2605.06251](https://doi.org/10.48550/arXiv.2605.06251). URL: <https://arxiv.org/abs/2605.06251v1>.

*Commentary.*

The Pauli weight counts coordinates where either the X or Z component is nonzero.

**Definition 1.6 (Code distance).**

$$\forall n \in \mathbb{N},\; \forall d \in \mathbb{N},\; \forall C \in \operatorname{CSSCode}\left(n\right),\; \operatorname{HasDistance}\left(C, d\right) = \left((\exists x \in (\operatorname{Fin}\left(n\right)\to\operatorname{ZMod}\left(2\right)),\; \exists z \in (\operatorname{Fin}\left(n\right)\to\operatorname{ZMod}\left(2\right)),\; (\operatorname{IsLogical}\left(C, x, z\right)) \land (\operatorname{pauliWeight}\left(x, z\right) = d)) \land (\forall x \in (\operatorname{Fin}\left(n\right)\to\operatorname{ZMod}\left(2\right)),\; \forall z \in (\operatorname{Fin}\left(n\right)\to\operatorname{ZMod}\left(2\right)),\; (\operatorname{IsLogical}\left(C, x, z\right)) \Rightarrow d \le \operatorname{pauliWeight}\left(x, z\right))\right)$$

*Formalization.* `D5/S3/Quantum/Information/CSSMeromorphicSuppression.HasDistance` (`✓ std3`).

*Citation.* Simon Burton; Hussain Anwar (2026). *Meromorphic Quantum Computing*. DOI: [10.48550/arXiv.2605.06251](https://doi.org/10.48550/arXiv.2605.06251). URL: <https://arxiv.org/abs/2605.06251v1>.

*Commentary.*

HasDistance records a logical Pauli of weight d and the universal lower bound d for every logical Pauli.

**Definition 1.7 (Decoder denominator).**

$$\forall n \in \mathbb{N},\; \forall C \in \operatorname{CSSCode}\left(n\right),\; \operatorname{decoderDen}\left(C\right) = \sum_{g\in \operatorname{Finset.filter}\left(\operatorname{fun} (g: (\operatorname{Fin}\left(n\right)\to\operatorname{ZMod}\left(2\right))) \mapsto g \in C.\operatorname{GX}, (\operatorname{Finset.univ}: \operatorname{Finset}\left((\operatorname{Fin}\left(n\right)\to\operatorname{ZMod}\left(2\right))\right))\right)} (X^{\operatorname{wt}\left(g\right)})$$

*Formalization.* `D5/S3/Quantum/Information/CSSMeromorphicSuppression.decoderDen` (`✓ std3`).

*Citation.* Simon Burton; Hussain Anwar (2026). *Meromorphic Quantum Computing*. DOI: [10.48550/arXiv.2605.06251](https://doi.org/10.48550/arXiv.2605.06251). URL: <https://arxiv.org/abs/2605.06251v1>.

*Commentary.*

For ψ_z = (1, z), |0_L⟩ ∝ ∑_{g ∈ G_X} |g⟩ and |1_L⟩ = X^{⊗n}|0_L⟩. Up to the common normalization, the denominator is ⟨0_L|ψ_z^{⊗n}⟩ = ∑_{g ∈ G_X} z^{wt(g)} and the numerator is ⟨1_L|ψ_z^{⊗n}⟩ = ∑_{g ∈ G_X} z^{wt(g + one)}. This is the codeword derivation of Theorem 4.4 and Appendix B of arXiv:2605.06251v1. The polynomial decoderDen records the denominator amplitude.

**Definition 1.8 (Decoder numerator).**

$$\forall n \in \mathbb{N},\; \forall C \in \operatorname{CSSCode}\left(n\right),\; \operatorname{decoderNum}\left(C\right) = \sum_{g\in \operatorname{Finset.filter}\left(\operatorname{fun} (g: (\operatorname{Fin}\left(n\right)\to\operatorname{ZMod}\left(2\right))) \mapsto g \in C.\operatorname{GX}, (\operatorname{Finset.univ}: \operatorname{Finset}\left((\operatorname{Fin}\left(n\right)\to\operatorname{ZMod}\left(2\right))\right))\right)} (X^{\operatorname{wt}\left(g + \operatorname{one}\right)})$$

*Formalization.* `D5/S3/Quantum/Information/CSSMeromorphicSuppression.decoderNum` (`✓ std3`).

*Citation.* Simon Burton; Hussain Anwar (2026). *Meromorphic Quantum Computing*. DOI: [10.48550/arXiv.2605.06251](https://doi.org/10.48550/arXiv.2605.06251). URL: <https://arxiv.org/abs/2605.06251v1>.

*Commentary.*

For ψ_z = (1, z), |0_L⟩ ∝ ∑_{g ∈ G_X} |g⟩ and |1_L⟩ = X^{⊗n}|0_L⟩. Up to the common normalization, the denominator is ⟨0_L|ψ_z^{⊗n}⟩ = ∑_{g ∈ G_X} z^{wt(g)} and the numerator is ⟨1_L|ψ_z^{⊗n}⟩ = ∑_{g ∈ G_X} z^{wt(g + one)}. This is the codeword derivation of Theorem 4.4 and Appendix B of arXiv:2605.06251v1. The polynomial decoderNum records the numerator amplitude.

**Definition 1.9 (Finite suppression order).**

$$\forall n \in \mathbb{N},\; \forall C \in \operatorname{CSSCode}\left(n\right),\; \forall a \in \mathbb{C},\; \operatorname{suppressionOrder}\left(C, a\right) = \operatorname{Polynomial.rootMultiplicity}\left(a, \operatorname{decoderNum}\left(C\right) - \operatorname{Polynomial.C}\left(a\right) \cdot \operatorname{decoderDen}\left(C\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/CSSMeromorphicSuppression.suppressionOrder` (`✓ std3`).

*Citation.* Simon Burton; Hussain Anwar (2026). *Meromorphic Quantum Computing*. DOI: [10.48550/arXiv.2605.06251](https://doi.org/10.48550/arXiv.2605.06251). URL: <https://arxiv.org/abs/2605.06251v1>.

*Commentary.*

At a finite point a, suppressionOrder is the root multiplicity of the numerator minus a times the denominator.

**Definition 1.10 (Suppression order at infinity).**

$$\forall n \in \mathbb{N},\; \forall C \in \operatorname{CSSCode}\left(n\right),\; \operatorname{suppressionOrderInf}\left(C\right) = \operatorname{Polynomial.rootMultiplicity}\left(0, \sum_{g\in \operatorname{Finset.filter}\left(\operatorname{fun} (g: (\operatorname{Fin}\left(n\right)\to\operatorname{ZMod}\left(2\right))) \mapsto g \in C.\operatorname{GX}, (\operatorname{Finset.univ}: \operatorname{Finset}\left((\operatorname{Fin}\left(n\right)\to\operatorname{ZMod}\left(2\right))\right))\right)} (X^{n - \operatorname{wt}\left(g\right)})\right)$$

*Formalization.* `D5/S3/Quantum/Information/CSSMeromorphicSuppression.suppressionOrderInf` (`✓ std3`).

*Citation.* Simon Burton; Hussain Anwar (2026). *Meromorphic Quantum Computing*. DOI: [10.48550/arXiv.2605.06251](https://doi.org/10.48550/arXiv.2605.06251). URL: <https://arxiv.org/abs/2605.06251v1>.

*Commentary.*

At infinity, suppressionOrderInf is the root multiplicity at zero of the degree-n reversed denominator.

**Definition 1.11 (Finite fixed point with order).**

$$\forall n \in \mathbb{N},\; \forall C \in \operatorname{CSSCode}\left(n\right),\; \forall a \in \mathbb{C},\; \operatorname{FixesWith}\left(C, a\right) = \left((\operatorname{Polynomial.eval}\left(a, \operatorname{decoderDen}\left(C\right)\right) \ne 0) \land (\operatorname{Polynomial.eval}\left(a, \operatorname{decoderNum}\left(C\right)\right) = a \cdot \operatorname{Polynomial.eval}\left(a, \operatorname{decoderDen}\left(C\right)\right))\right)$$

*Formalization.* `D5/S3/Quantum/Information/CSSMeromorphicSuppression.FixesWith` (`✓ std3`).

*Citation.* Simon Burton; Hussain Anwar (2026). *Meromorphic Quantum Computing*. DOI: [10.48550/arXiv.2605.06251](https://doi.org/10.48550/arXiv.2605.06251). URL: <https://arxiv.org/abs/2605.06251v1>.

*Commentary.*

FixesWith says that the denominator is nonzero and the decoder numerator equals a times the denominator at a.

**Definition 1.12 (The fixed point at infinity).**

$$\forall n \in \mathbb{N},\; \forall C \in \operatorname{CSSCode}\left(n\right),\; \operatorname{FixesWithInf}\left(C\right) = \left(\operatorname{Polynomial.eval}\left(0, \sum_{g\in \operatorname{Finset.filter}\left(\operatorname{fun} (g: (\operatorname{Fin}\left(n\right)\to\operatorname{ZMod}\left(2\right))) \mapsto g \in C.\operatorname{GX}, (\operatorname{Finset.univ}: \operatorname{Finset}\left((\operatorname{Fin}\left(n\right)\to\operatorname{ZMod}\left(2\right))\right))\right)} (X^{n - \operatorname{wt}\left(g + \operatorname{one}\right)})\right) \ne 0\right)$$

*Formalization.* `D5/S3/Quantum/Information/CSSMeromorphicSuppression.FixesWithInf` (`✓ std3`).

*Citation.* Simon Burton; Hussain Anwar (2026). *Meromorphic Quantum Computing*. DOI: [10.48550/arXiv.2605.06251](https://doi.org/10.48550/arXiv.2605.06251). URL: <https://arxiv.org/abs/2605.06251v1>.

*Commentary.*

FixesWithInf is the nonvanishing of the reversed numerator at zero.

**Definition 1.13 (Conjecture 4.8).**

$$\forall n \in \mathbb{N},\; \forall d \in \mathbb{N},\; \forall C \in \operatorname{CSSCode}\left(n\right),\; (\operatorname{HasDistance}\left(C, d\right)) \Rightarrow \left((\forall a \in \mathbb{C},\; (a \in \{0, 1, -1\}) \Rightarrow \left((\operatorname{FixesWith}\left(C, a\right)) \land (d \le \operatorname{suppressionOrder}\left(C, a\right))\right)) \land ((\operatorname{FixesWithInf}\left(C\right)) \land (d \le \operatorname{suppressionOrderInf}\left(C\right)))\right)$$

*Formalization.* `D5/S3/Quantum/Information/CSSMeromorphicSuppression.claim` (`✓ std3`).

*Citation.* Simon Burton; Hussain Anwar (2026). *Meromorphic Quantum Computing*. DOI: [10.48550/arXiv.2605.06251](https://doi.org/10.48550/arXiv.2605.06251). URL: <https://arxiv.org/abs/2605.06251v1>.

*Commentary.*

Conjecture 4.8 (Burton and Anwar, arXiv:2605.06251v1, Section 4, p. 14): "Any CSS code [[n,1,d]] with logical operators X^{⊗n}, Z^{⊗n} exhibits coherent error suppression O(ε^d) at the four stabilizer states z = 0, ∞, ±1." The encoding uses the binary CSS conventions above and states the lower bound on local degree.

**Theorem 1.14 (The four-point suppression theorem).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/CSSMeromorphicSuppression.result` (`✓ std3`). ∎

*Resolves.* `Problems/burton-anwar-2026-css-meromorphic-suppression` (proved) by `D5/S3/Quantum/Information/CSSMeromorphicSuppression.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"burton-anwar-2026-css-meromorphic-suppression","declaration_gid":"D5/S3/Quantum/Information/CSSMeromorphicSuppression.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Simon Burton; Hussain Anwar (2026). *Meromorphic Quantum Computing*. DOI: [10.48550/arXiv.2605.06251](https://doi.org/10.48550/arXiv.2605.06251). URL: <https://arxiv.org/abs/2605.06251v1>.

*Commentary.*

For ψ_z = (1, z), |0_L⟩ ∝ ∑_{g ∈ G_X} |g⟩ and |1_L⟩ = X^{⊗n}|0_L⟩. Up to the common normalization, the denominator is ⟨0_L|ψ_z^{⊗n}⟩ = ∑_{g ∈ G_X} z^{wt(g)} and the numerator is ⟨1_L|ψ_z^{⊗n}⟩ = ∑_{g ∈ G_X} z^{wt(g + one)}. This is the codeword derivation of Theorem 4.4 and Appendix B of arXiv:2605.06251v1. Adding the all-ones vector sends every X stabilizer to a logical-X representative, so the numerator is divisible by z^d and the denominator is 1 at zero. Degree-n reversal gives infinity. At 1 and -1, binary character orthogonality factors P-Q and P+Q through odd logical-Z representatives, giving the same distance divisibility and the fixed-point equalities.

## References

- Truth anchor: `D5/S3/Quantum/Information/CSSMeromorphicSuppression.CSSCode`
- Truth anchor: `D5/S3/Quantum/Information/CSSMeromorphicSuppression.FixesWith`
- Truth anchor: `D5/S3/Quantum/Information/CSSMeromorphicSuppression.FixesWithInf`
- Truth anchor: `D5/S3/Quantum/Information/CSSMeromorphicSuppression.HasDistance`
- Truth anchor: `D5/S3/Quantum/Information/CSSMeromorphicSuppression.IsLogical`
- Truth anchor: `D5/S3/Quantum/Information/CSSMeromorphicSuppression.claim`
- Truth anchor: `D5/S3/Quantum/Information/CSSMeromorphicSuppression.decoderDen`
- Truth anchor: `D5/S3/Quantum/Information/CSSMeromorphicSuppression.decoderNum`
- Truth anchor: `D5/S3/Quantum/Information/CSSMeromorphicSuppression.one`
- Truth anchor: `D5/S3/Quantum/Information/CSSMeromorphicSuppression.pauliWeight`
- Truth anchor: `D5/S3/Quantum/Information/CSSMeromorphicSuppression.result`
- Truth anchor: `D5/S3/Quantum/Information/CSSMeromorphicSuppression.suppressionOrder`
- Truth anchor: `D5/S3/Quantum/Information/CSSMeromorphicSuppression.suppressionOrderInf`
- Truth anchor: `D5/S3/Quantum/Information/CSSMeromorphicSuppression.wt`
- Dependency: [D5/S3/VertexAlgebra/LatticeTwistedGroundRealization](../../VertexAlgebra/LatticeTwistedGroundRealization.md)
