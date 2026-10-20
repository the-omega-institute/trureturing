# PathCHSNormBCSRemark43

## Abstract

Complete homogeneous symmetric functions of finite path spectra.

**Definition 1.1 (The trigonometric expression).**

$$\forall n \in \mathbb{N},\; \forall d \in \mathbb{N},\; \operatorname{trigForm}\left(n, d\right) = \frac{(2:\mathbb{R})^{n + d}}{(n:\mathbb{R}) + 1} \cdot \sum_{k \in \operatorname{Finset}.\operatorname{Icc}\left(1, n\right)} ((-1:\mathbb{R})^{k + 1} \cdot \operatorname{Real}.\operatorname{cos}\left(\frac{\operatorname{Real}.\operatorname{pi} \cdot (k:\mathbb{R})}{(n:\mathbb{R}) + 1}\right)^{n - 1 + d} \cdot \operatorname{Real}.\operatorname{sin}\left(\frac{\operatorname{Real}.\operatorname{pi} \cdot (k:\mathbb{R})}{(n:\mathbb{R}) + 1}\right)^{2})$$

*Formalization.* `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormBCSRemark43.trigForm` (`✓ std3`).

*Citation.* Ludovick Bouthat, Ángel Chávez and Sam Sheng (2026). *A general framework for inequalities on simple graphs*. DOI: [10.48550/arXiv.2606.17356](https://doi.org/10.48550/arXiv.2606.17356). URL: <https://arxiv.org/abs/2606.17356v1>.

*Commentary.*

Page 18, Remark 4.3: “While we have not been able to prove this fact, we have found that the following appears to hold for all n ≥ 1 and all even d ≥ 2: ‖P_n‖_{X,d}^d = (2^{n+d}/(n+1)) Σ_{k=1}^{n} (−1)^{k+1} cos^{n−1+d}(πk/(n+1)) sin²(πk/(n+1)) = Σ_{j=−∞}^{∞} [binom(n+d−1, (n+1)j + d/2) − binom(n+d−1, (n+1)j + d/2 − 1)].” The index k runs through the natural interval from 1 to n.

**Definition 1.2 (The bilateral binomial sum).**

$$\forall n \in \mathbb{N},\; \forall d \in \mathbb{N},\; \operatorname{bilateralForm}\left(n, d\right) = \left(\sum^{\operatorname{f}}\right)_{j:\mathbb{Z}} ((\operatorname{D5}.\operatorname{S0}.\operatorname{Conventions}.\operatorname{IntegerIndexBinomial}.\operatorname{binom}\left(n + d - 1, \left((n:\mathbb{Z}) + 1\right) \cdot j + (\operatorname{Nat}.\operatorname{div}\left(d, 2\right):\mathbb{Z})\right):\mathbb{Z}) - (\operatorname{D5}.\operatorname{S0}.\operatorname{Conventions}.\operatorname{IntegerIndexBinomial}.\operatorname{binom}\left(n + d - 1, \left((n:\mathbb{Z}) + 1\right) \cdot j + (\operatorname{Nat}.\operatorname{div}\left(d, 2\right):\mathbb{Z}) - 1\right):\mathbb{Z}))$$

*Formalization.* `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormBCSRemark43.bilateralForm` (`✓ std3`).

*Citation.* Ludovick Bouthat, Ángel Chávez and Sam Sheng (2026). *A general framework for inequalities on simple graphs*. DOI: [10.48550/arXiv.2606.17356](https://doi.org/10.48550/arXiv.2606.17356). URL: <https://arxiv.org/abs/2606.17356v1>.

*Commentary.*

Page 18, Remark 4.3: “While we have not been able to prove this fact, we have found that the following appears to hold for all n ≥ 1 and all even d ≥ 2: ‖P_n‖_{X,d}^d = (2^{n+d}/(n+1)) Σ_{k=1}^{n} (−1)^{k+1} cos^{n−1+d}(πk/(n+1)) sin²(πk/(n+1)) = Σ_{j=−∞}^{∞} [binom(n+d−1, (n+1)j + d/2) − binom(n+d−1, (n+1)j + d/2 − 1)].” The sum is finsum over integer j; only finitely many terms are nonzero. Nat.div is the natural quotient.

**Definition 1.3 (The two identities of Remark 4.3).**

$$\operatorname{claim} = \left(\forall n \in \mathbb{N},\; \forall d \in \mathbb{N},\; (1 \le n) \to (2 \le d) \to (\operatorname{Even}\left(d\right)) \to (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{Graph}.\operatorname{PathCHS}.\operatorname{PathCHSNormClosedForm}.\operatorname{chs}\left(n, d\right) = \operatorname{trigForm}\left(n, d\right)) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{Graph}.\operatorname{PathCHS}.\operatorname{PathCHSNormClosedForm}.\operatorname{chs}\left(n, d\right) = (\operatorname{bilateralForm}\left(n, d\right):\mathbb{R}))\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormBCSRemark43.claim` (`✓ std3`).

*Citation.* Ludovick Bouthat, Ángel Chávez and Sam Sheng (2026). *A general framework for inequalities on simple graphs*. DOI: [10.48550/arXiv.2606.17356](https://doi.org/10.48550/arXiv.2606.17356). URL: <https://arxiv.org/abs/2606.17356v1>.

*Commentary.*

Page 18, Remark 4.3: “While we have not been able to prove this fact, we have found that the following appears to hold for all n ≥ 1 and all even d ≥ 2: ‖P_n‖_{X,d}^d = (2^{n+d}/(n+1)) Σ_{k=1}^{n} (−1)^{k+1} cos^{n−1+d}(πk/(n+1)) sin²(πk/(n+1)) = Σ_{j=−∞}^{∞} [binom(n+d−1, (n+1)j + d/2) − binom(n+d−1, (n+1)j + d/2 − 1)].” The graph value is the complete homogeneous symmetric polynomial of the path adjacency eigenvalues.

**Theorem 1.4 (Proof of both identities).**

$$\forall n \in \mathbb{N},\; \forall d \in \mathbb{N},\; (1 \le n) \to (2 \le d) \to (\operatorname{Even}\left(d\right)) \to (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{Graph}.\operatorname{PathCHS}.\operatorname{PathCHSNormClosedForm}.\operatorname{chs}\left(n, d\right) = \operatorname{trigForm}\left(n, d\right)) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{Graph}.\operatorname{PathCHS}.\operatorname{PathCHSNormClosedForm}.\operatorname{chs}\left(n, d\right) = (\operatorname{bilateralForm}\left(n, d\right):\mathbb{R}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormBCSRemark43.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ludovick Bouthat, Ángel Chávez and Sam Sheng (2026). *A general framework for inequalities on simple graphs*. DOI: [10.48550/arXiv.2606.17356](https://doi.org/10.48550/arXiv.2606.17356). URL: <https://arxiv.org/abs/2606.17356v1>.

*Commentary.*

The recurrence identity tⁿ Sₙ(t⁻¹)=cont(t²;1,1;n) for nonzero t identifies the reciprocal product at the Chebyshev nodes. Partial fractions give the sine-square weights. Pairing the positive and negative integer indices gives the finite second-difference formula.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormBCSRemark43.bilateralForm`
- Truth anchor: `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormBCSRemark43.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormBCSRemark43.result`
- Truth anchor: `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormBCSRemark43.trigForm`
- Dependency: [D5/S0/Conventions/IntegerIndexBinomial](../../../../S0/Conventions/IntegerIndexBinomial.md)
- Dependency: [D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormClosedForm](PathCHSNormClosedForm.md)
- Dependency: [D5/S3/Combinatorics/NarayanaStrip/CiglerStripProductContinuants](../../NarayanaStrip/CiglerStripProductContinuants.md)
- Dependency: [D5/S3/QuantumBounds/ReferenceFrame/TopEigenspace](../../../QuantumBounds/ReferenceFrame/TopEigenspace.md)
