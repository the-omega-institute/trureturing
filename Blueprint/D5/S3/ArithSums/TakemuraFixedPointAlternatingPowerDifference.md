# Takemura's fixed-point alternating power difference

## Abstract

Takemura's fixed-point alternating power difference has first degree n - 1 and value n!.

**Definition 1.1 (The alternating power difference).**

$$\forall n \in \mathbb{N}, f \in Equiv.Perm\left(\operatorname{Fin}\left(n\right)\right) \to \mathbb{Z}, m \in \mathbb{N},\; \operatorname{apd}\left(n, f, m\right) = \sum_{sigma: Equiv.Perm\left(\operatorname{Fin}\left(n\right)\right)} (Equiv.Perm.sign\left(sigma\right): \mathbb{Z}) \cdot f\left(sigma\right)^{m}$$

*Formalization.* `D5/S3/ArithSums/TakemuraFixedPointAlternatingPowerDifference.apd` (`✓ std3`).

*Citation.* Kenichi Takemura (2025). *Alternating Power Difference and Matrix Symmetry: Closed-Form Formulas for the First Appearance Degree m_1*. DOI: [10.48550/arXiv.2512.18169](https://doi.org/10.48550/arXiv.2512.18169). URL: <https://arxiv.org/abs/2512.18169v1>.

*Commentary.*

Definition 1 (Alternating Power Difference). For an integer-valued function f : Sₙ → ℤ and m ≥ 1, we define: APDₘ(f) := Σ_{σ∈Sₙ} sgn(σ)f(σ)^m. (arXiv:2512.18169v1, printed p. 1.) The formal sum ranges over Equiv.Perm (Fin n), and the sign is cast to integers.

**Definition 1.2 (The fixed-point function).**

$$\forall n \in \mathbb{N}, sigma \in Equiv.Perm\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{fix}\left(sigma\right) = (\operatorname{card}\left(Finset.univ.filter\left((\lambda i \mapsto sigma\left(i\right) = i)\right)\right): \mathbb{Z})$$

*Formalization.* `D5/S3/ArithSums/TakemuraFixedPointAlternatingPowerDifference.fix` (`✓ std3`).

*Citation.* Kenichi Takemura (2025). *Alternating Power Difference and Matrix Symmetry: Closed-Form Formulas for the First Appearance Degree m_1*. DOI: [10.48550/arXiv.2512.18169](https://doi.org/10.48550/arXiv.2512.18169). URL: <https://arxiv.org/abs/2512.18169v1>.

*Commentary.*

For a permutation σ ∈ Sₙ, let P_σ be the permutation matrix corresponding to σ. We define the function f_A : Sₙ → ℤ corresponding to matrix A as the trace of the product of matrix A and the permutation matrix P_σ. f_A(σ) := tr(AP_σ) = Σ_{i=1}^{n} A_{i,σ(i)}. (arXiv:2512.18169v1, printed p. 2.) Therefore, the value of this function is exactly equal to the total number of fixed points in the permutation σ. We define this function as the Fixed Point Function fix (or Fix point function). fix(σ) := f_{Iₙ}(σ). (arXiv:2512.18169v1, printed p. 3.) The formal expression is the filtered cardinality of the fixed indices.

**Definition 1.3 (The first appearance degree).**

$$\forall n \in \mathbb{N}, f \in Equiv.Perm\left(\operatorname{Fin}\left(n\right)\right) \to \mathbb{Z},\; \operatorname{firstAppearanceDegree}\left(n, f\right) = \operatorname{sInf}\left(\{m: \mathbb{N} \mid (1 \le m \land \operatorname{apd}\left(n, f, m\right) \ne 0)\}\right)$$

*Formalization.* `D5/S3/ArithSums/TakemuraFixedPointAlternatingPowerDifference.firstAppearanceDegree` (`✓ std3`).

*Citation.* Kenichi Takemura (2025). *Alternating Power Difference and Matrix Symmetry: Closed-Form Formulas for the First Appearance Degree m_1*. DOI: [10.48550/arXiv.2512.18169](https://doi.org/10.48550/arXiv.2512.18169). URL: <https://arxiv.org/abs/2512.18169v1>.

*Commentary.*

Definition 2 (First Appearance Degree). For a function f : Sₙ → ℤ, the smallest m ≥ 1 such that APDₘ(f) ≠ 0 is called the First Appearance Degree (or APD Index) of f, denoted by m₁(f). If APDₘ(f) = 0 for all m ≥ 1, we define m₁(f) = ∞. (arXiv:2512.18169v1, printed p. 1.) The formal natural number is the sInf of exactly the defining set of positive indices with nonzero alternating power difference.

**Theorem 1.4 (Conjecture 1: first appearance degree).**

$$\forall n \in \mathbb{N},\; (2 \le n) \Rightarrow (\operatorname{firstAppearanceDegree}\left(n, fix\right) = n - 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/TakemuraFixedPointAlternatingPowerDifference.resultDegree` (`✓ std3`). ∎

*Resolves.* `Problems/takemura-fixed-point-apd-conjecture-1` (proved) by `D5/S3/ArithSums/TakemuraFixedPointAlternatingPowerDifference.resultDegree`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"takemura-fixed-point-apd-conjecture-1","declaration_gid":"D5/S3/ArithSums/TakemuraFixedPointAlternatingPowerDifference.resultDegree","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Kenichi Takemura (2025). *Alternating Power Difference and Matrix Symmetry: Closed-Form Formulas for the First Appearance Degree m_1*. DOI: [10.48550/arXiv.2512.18169](https://doi.org/10.48550/arXiv.2512.18169). URL: <https://arxiv.org/abs/2512.18169v1>.

*Commentary.*

Conjecture 1 (First Appearance Degree of Identity Matrix). For n ≥ 2, the first appearance degree m₁(Iₙ) of the fixed point function fix corresponding to the n-th order identity matrix Iₙ is given by the following closed form: m₁(Iₙ) = n − 1. This relationship has been verified for n ≤ 10. (arXiv:2512.18169v1, printed p. 4.) The statement is the source's conjecture, which it verifies numerically for n ≤ 10 and leaves unproved; the proof is repository-derived. The proof expands fix(sigma)^m over tuples of indices, exchanges the finite sums, evaluates the signed sum over permutations fixing the tuple image pointwise, and uses the resulting vanishing range together with the first nonzero injection count to identify the least degree.

**Theorem 1.5 (Conjecture 2: first appearance value).**

$$\forall n \in \mathbb{N},\; (2 \le n) \Rightarrow (\operatorname{apd}\left(n, fix, n - 1\right) = (\operatorname{factorial}\left(n\right): \mathbb{Z}))$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/TakemuraFixedPointAlternatingPowerDifference.resultValue` (`✓ std3`). ∎

*Resolves.* `Problems/takemura-fixed-point-apd-conjecture-2` (proved) by `D5/S3/ArithSums/TakemuraFixedPointAlternatingPowerDifference.resultValue`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"takemura-fixed-point-apd-conjecture-2","declaration_gid":"D5/S3/ArithSums/TakemuraFixedPointAlternatingPowerDifference.resultValue","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Kenichi Takemura (2025). *Alternating Power Difference and Matrix Symmetry: Closed-Form Formulas for the First Appearance Degree m_1*. DOI: [10.48550/arXiv.2512.18169](https://doi.org/10.48550/arXiv.2512.18169). URL: <https://arxiv.org/abs/2512.18169v1>.

*Commentary.*

Conjecture 2 (Formula for First Appearance Value of Identity Matrix). For n ≥ 2, the first appearance value APDₙ₋₁(Iₙ) of the fixed point function fix corresponding to the n-th order identity matrix Iₙ is given by the following closed form: APDₙ₋₁(Iₙ) = n!. This relationship has been verified for n ≤ 10. (arXiv:2512.18169v1, printed p. 4.) The statement is the source's conjecture, which it verifies numerically for n ≤ 10 and leaves unproved; the proof is repository-derived. The proof leaves exactly the injective maps from Fin(n-1) to Fin(n) after the pointwise-fixing sign sum, counts those embeddings, and simplifies the descending factorial to n!.

## References

- Truth anchor: `D5/S3/ArithSums/TakemuraFixedPointAlternatingPowerDifference.apd`
- Truth anchor: `D5/S3/ArithSums/TakemuraFixedPointAlternatingPowerDifference.firstAppearanceDegree`
- Truth anchor: `D5/S3/ArithSums/TakemuraFixedPointAlternatingPowerDifference.fix`
- Truth anchor: `D5/S3/ArithSums/TakemuraFixedPointAlternatingPowerDifference.resultDegree`
- Truth anchor: `D5/S3/ArithSums/TakemuraFixedPointAlternatingPowerDifference.resultValue`
