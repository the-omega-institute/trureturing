# A repeated value among the wreath eigenvalues

## Abstract

The wreath eigenvalues indexed by three and five coincide at fourteen and five.

Petr and Turek's Theorem 1.5 identifies explicit formulas with the eigenvalues of the wreath matrix. The rational formulas below retain the paper's indices. Their equality at n = 14 and k = 5 answers Question 5.5 negatively. The identification with the matrix spectrum is a result of the cited paper; the Lean proof establishes the arithmetic refutation of distinctness.

**Definition 1.1 (The first eigenvalue formula).**

$$\forall n \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \operatorname{lambdaOne}\left(n, k\right) = \operatorname{ite}\left(k \mid n, \frac{(n : \mathrm{Rat})^{2} \cdot (\operatorname{Nat}.\operatorname{factorial}\left(n - k\right) : \mathrm{Rat})}{(k : \mathrm{Rat})^{2} \cdot (\operatorname{Nat}.\operatorname{factorial}\left(k\right) : \mathrm{Rat})^{\operatorname{Nat}.\operatorname{div}\left(n, k\right) - 1} \cdot (\operatorname{Nat}.\operatorname{factorial}\left(\operatorname{Nat}.\operatorname{div}\left(n, k\right)\right) : \mathrm{Rat})}, \frac{(n : \mathrm{Rat}) \cdot (\operatorname{Nat}.\operatorname{factorial}\left(n - k\right) : \mathrm{Rat}) \cdot (\operatorname{Nat}.\operatorname{factorial}\left(k\right) : \mathrm{Rat})}{2 \cdot (\operatorname{Nat}.\operatorname{gcd}\left(n, k\right) : \mathrm{Rat}) \cdot (\operatorname{Nat}.\operatorname{factorial}\left(\operatorname{Nat}.\operatorname{gcd}\left(n, k\right)\right) : \mathrm{Rat})^{\operatorname{Nat}.\operatorname{div}\left(n, \operatorname{Nat}.\operatorname{gcd}\left(n, k\right)\right)}}\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/PetrTurekWreathEigenvaluesRefutation.lambdaOne` (`✓ std3`).

*Citation.* Jan Petr; Pavel Turek (2025). *The wreath matrix*. DOI: [10.48550/arXiv.2501.07269](https://doi.org/10.48550/arXiv.2501.07269). URL: <https://arxiv.org/abs/2501.07269v2>.

*Commentary.*

Theorem 1.5, page 3, states: “The value of λ₁ is n(n−k)!k!/(2g(g!)ⁿ⁄ᵍ) if k ∤ n and n²(n−k)!/(k²(k!)ⁿ⁄ᵏ⁻¹(n/k)!) if k ∣ n.” Here g = gcd(n,k). The arguments n and k are natural numbers and the values are rational. Nat.div denotes natural-number division, and subtraction within a natural-number argument is truncated subtraction. Every conversion from Nat to Rat is displayed by a type annotation.

**Definition 1.2 (The indexed eigenvalue formula).**

$$\forall n \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \forall l \in \mathrm{Nat},\; \operatorname{lam}\left(n, k, l\right) = \operatorname{ite}\left(l = 1, \operatorname{lambdaOne}\left(n, k\right), \left(-1\right)^{l} \cdot \frac{1}{2} \cdot (\operatorname{Nat}.\operatorname{factorial}\left(l\right) : \mathrm{Rat}) \cdot (\operatorname{Nat}.\operatorname{factorial}\left(k\right) : \mathrm{Rat}) \cdot (\operatorname{Nat}.\operatorname{factorial}\left(n - k - l\right) : \mathrm{Rat}) \cdot \left((n : \mathrm{Rat}) - 2 \cdot (k : \mathrm{Rat}) - 1\right) \cdot (\operatorname{Nat}.\operatorname{choose}\left(k, l\right) : \mathrm{Rat}) - \frac{1}{2} \cdot (\operatorname{Nat}.\operatorname{factorial}\left(k\right) : \mathrm{Rat}) \cdot (\operatorname{Nat}.\operatorname{factorial}\left(n - k\right) : \mathrm{Rat}) + (\operatorname{Nat}.\operatorname{factorial}\left(l\right) : \mathrm{Rat}) \cdot (\operatorname{Nat}.\operatorname{choose}\left(k + 1, l + 1\right) : \mathrm{Rat}) \cdot \sum_{j \in \operatorname{Finset}.\operatorname{range}\left(l + 1\right)} (\left(-1\right)^{l - j} \cdot (\operatorname{Nat}.\operatorname{factorial}\left(k - j\right) : \mathrm{Rat}) \cdot (\operatorname{Nat}.\operatorname{factorial}\left(n - k - l + j\right) : \mathrm{Rat}))\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/PetrTurekWreathEigenvaluesRefutation.lam` (`✓ std3`).

*Citation.* Jan Petr; Pavel Turek (2025). *The wreath matrix*. DOI: [10.48550/arXiv.2501.07269](https://doi.org/10.48550/arXiv.2501.07269). URL: <https://arxiv.org/abs/2501.07269v2>.

*Commentary.*

Theorem 1.5, page 3, states: “If g = 1, for 2 ≤ l ≤ k we moreover have” λₗ = (−1)ˡ ½ l! k! (n−k−l)! (n−2k−1) C(k,l) − ½ k! (n−k)! + l! C(k+1,l+1) ∑ⱼ₌₀ˡ (−1)ˡ⁻ʲ (k−j)! (n−k−l+j)!. The value at l = 1 is lambdaOne n k. The sum over Finset.range (l+1) contains j = 0 through l once each. The factor n−2k−1 is evaluated in Rat; factorial arguments and the exponent l−j are evaluated in Nat. Outside the positive coprime range 2k < n and 1 ≤ l ≤ k, these total formulas assert no spectral interpretation.

**Definition 1.3 (Distinctness in the coprime range).**

$$\operatorname{claim} = (\forall n \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; 0 < k \Rightarrow (2 \cdot k < n \Rightarrow (\operatorname{Nat}.\operatorname{Coprime}\left(n, k\right) \Rightarrow (\forall l \in \mathrm{Nat},\; l \in \operatorname{Finset}.\operatorname{Icc}\left(1, k\right) \Rightarrow (\forall lprime \in \mathrm{Nat},\; lprime \in \operatorname{Finset}.\operatorname{Icc}\left(1, k\right) \Rightarrow (l \ne lprime \Rightarrow (\operatorname{lam}\left(n, k, l\right) \ne \operatorname{lam}\left(n, k, lprime\right))))))))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/PetrTurekWreathEigenvaluesRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jan Petr; Pavel Turek (2025). *The wreath matrix*. DOI: [10.48550/arXiv.2501.07269](https://doi.org/10.48550/arXiv.2501.07269). URL: <https://arxiv.org/abs/2501.07269v2>.

*Commentary.*

Question 5.5, page 16, asks verbatim: “Are the eigenvalues λ₁, λ₂, …, λₖ from Theorem 1.5 all distinct?” The proposition expresses an affirmative answer restricted to coprime positive parameters with 2k < n. The indices l and lprime (Lean's l') range over Finset.Icc 1 k. An affirmative answer to the source question implies this restricted proposition.

**Theorem 1.4 (Refutation by two coincident formula values).**

$$\neg (\forall n \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; 0 < k \Rightarrow (2 \cdot k < n \Rightarrow (\operatorname{Nat}.\operatorname{Coprime}\left(n, k\right) \Rightarrow (\forall l \in \mathrm{Nat},\; l \in \operatorname{Finset}.\operatorname{Icc}\left(1, k\right) \Rightarrow (\forall lprime \in \mathrm{Nat},\; lprime \in \operatorname{Finset}.\operatorname{Icc}\left(1, k\right) \Rightarrow (l \ne lprime \Rightarrow (\operatorname{lam}\left(n, k, l\right) \ne \operatorname{lam}\left(n, k, lprime\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/PetrTurekWreathEigenvaluesRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/petr-turek-2025-wreath-eigenvalue-coincidence` (refuted) by `D5/S3/Combinatorics/SpectralGraph/PetrTurekWreathEigenvaluesRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"petr-turek-2025-wreath-eigenvalue-coincidence","declaration_gid":"D5/S3/Combinatorics/SpectralGraph/PetrTurekWreathEigenvaluesRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jan Petr; Pavel Turek (2025). *The wreath matrix*. DOI: [10.48550/arXiv.2501.07269](https://doi.org/10.48550/arXiv.2501.07269). URL: <https://arxiv.org/abs/2501.07269v2>.

*Commentary.*

At n = 14 and k = 5, the indices 3 and 5 are distinct and both lie in Finset.Icc 1 5. The parameters satisfy 0 < 5, 2·5 < 14 and Nat.Coprime 14 5. Normalizing the two rational expressions gives lam 14 5 3 = 17107200 and lam 14 5 5 = 17107200, contradicting the displayed distinctness proposition. Theorem 1.5 expressly permits repeated values and adds their multiplicities, so its statement remains intact.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/PetrTurekWreathEigenvaluesRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/PetrTurekWreathEigenvaluesRefutation.lam`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/PetrTurekWreathEigenvaluesRefutation.lambdaOne`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/PetrTurekWreathEigenvaluesRefutation.result`
