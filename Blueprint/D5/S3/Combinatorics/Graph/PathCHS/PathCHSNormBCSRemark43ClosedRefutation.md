# PathCHSNormBCSRemark43ClosedRefutation

## Abstract

Complete homogeneous symmetric functions of finite path spectra.

**Definition 1.1 (The proposed one-term formula).**

$$\operatorname{claim} = \left(\forall n \in \mathbb{N},\; \forall d \in \mathbb{N},\; (1 \le n) \to (2 \le d) \to (\operatorname{Even}\left(d\right)) \to (\operatorname{Nat}.\operatorname{div}\left(d, 2\right) \le n + 1) \to \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{Graph}.\operatorname{PathCHS}.\operatorname{PathCHSNormClosedForm}.\operatorname{chs}\left(n, d\right) = \frac{(n:\mathbb{R})^{2} + (n:\mathbb{R}) - (d:\mathbb{R})}{\left((n:\mathbb{R}) + (d:\mathbb{R})\right) \cdot \left((n:\mathbb{R}) + (d:\mathbb{R}) + 1\right)} \cdot (\operatorname{Nat}.\operatorname{choose}\left(n + d + 1, \operatorname{Nat}.\operatorname{div}\left(d, 2\right)\right):\mathbb{R})\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormBCSRemark43ClosedRefutation.claim` (`✓ std3`).

*Citation.* Ludovick Bouthat, Ángel Chávez and Sam Sheng (2026). *A general framework for inequalities on simple graphs*. DOI: [10.48550/arXiv.2606.17356](https://doi.org/10.48550/arXiv.2606.17356). URL: <https://arxiv.org/abs/2606.17356v1>.

*Commentary.*

Page 18, Remark 4.3: “In particular, if n+1 ≥ d/2, the sum becomes ‖P_n‖_{X,d}^d = ((n² + n − d)/((n + d)(n + d + 1))) binom(n+d+1, d/2).” The hypotheses also require n ≥ 1 and even d ≥ 2. Nat.div is natural-number quotient, exact here because d is even.

**Theorem 1.2 (A boundary counterexample).**

$$\neg (\forall n \in \mathbb{N},\; \forall d \in \mathbb{N},\; (1 \le n) \to (2 \le d) \to (\operatorname{Even}\left(d\right)) \to (\operatorname{Nat}.\operatorname{div}\left(d, 2\right) \le n + 1) \to \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{Graph}.\operatorname{PathCHS}.\operatorname{PathCHSNormClosedForm}.\operatorname{chs}\left(n, d\right) = \frac{(n:\mathbb{R})^{2} + (n:\mathbb{R}) - (d:\mathbb{R})}{\left((n:\mathbb{R}) + (d:\mathbb{R})\right) \cdot \left((n:\mathbb{R}) + (d:\mathbb{R}) + 1\right)} \cdot (\operatorname{Nat}.\operatorname{choose}\left(n + d + 1, \operatorname{Nat}.\operatorname{div}\left(d, 2\right)\right):\mathbb{R}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormBCSRemark43ClosedRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/bouthat-chavez-sheng-2026-path-chs-remark43-closed-refutation` (refuted) by `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormBCSRemark43ClosedRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bouthat-chavez-sheng-2026-path-chs-remark43-closed-refutation","declaration_gid":"D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormBCSRemark43ClosedRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Ludovick Bouthat, Ángel Chávez and Sam Sheng (2026). *A general framework for inequalities on simple graphs*. DOI: [10.48550/arXiv.2606.17356](https://doi.org/10.48550/arXiv.2606.17356). URL: <https://arxiv.org/abs/2606.17356v1>.

*Commentary.*

For n=2 and d=6 the complete homogeneous symmetric value is one, while the proposed expression is zero.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormBCSRemark43ClosedRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormBCSRemark43ClosedRefutation.result`
- Dependency: [D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormClosedForm](PathCHSNormClosedForm.md)
