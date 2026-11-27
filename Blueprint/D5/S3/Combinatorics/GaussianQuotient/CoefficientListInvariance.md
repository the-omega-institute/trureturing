# Invariance of the nonzero-coefficient list

## Abstract

Multiplying a polynomial by q^s or substituting q -> q^k with k at least one preserves its ordered list of nonzero coefficients, and hence almost palindromicity.

**Definition 1.1 (The ordered nonzero-coefficient list).**

$$\operatorname{supportCoeffList}\left(f\right) = \operatorname{map}\left(\operatorname{coeff}\left(f\right), \operatorname{sort}\left(\operatorname{support}\left(f\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/GaussianQuotient/CoefficientListInvariance.supportCoeffList` (`✓ std3`).

*Citation.* Okada, So (2020). *Merged-log-concavity of rational functions, almost strictly unimodal sequences, and phase transitions of ideal boson-fermion gases*. DOI: [10.48550/arXiv.2003.02112](https://doi.org/10.48550/arXiv.2003.02112). URL: <https://arxiv.org/abs/2003.02112v2>.

*Commentary.*

supportCoeffList f is the list of the coefficients of f at its support, read in increasing order of exponent; for f in Z[q] these are the f_(lambda_1),...,f_(lambda_kappa) of Definition 9.52, and OkadaPreMergedNonPalindromic.IsAlmostPalindromic f says that this list is a palindrome. In the result, RPoly is R[q] for a semiring R (a commutative semiring for the substitution) and ZPoly is Z[q].

**Theorem 1.2 (Shifts and substitutions keep the list).**

$$(\forall f \in \mathrm{RPoly},\; \forall s \in \mathrm{Nat},\; \operatorname{supportCoeffList}\left(q^{s} \cdot f\right) = \operatorname{supportCoeffList}\left(f\right)) \land ((\forall f \in \mathrm{RPoly},\; \forall k \in \mathrm{Nat},\; (1 \le k) \Rightarrow (\operatorname{supportCoeffList}\left(\operatorname{expand}\left(k, f\right)\right) = \operatorname{supportCoeffList}\left(f\right))) \land (\forall f \in \mathrm{ZPoly},\; \forall s \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; (1 \le k) \Rightarrow (((\operatorname{IsAlmostPalindromic}\left(q^{s} \cdot f\right)) \Leftrightarrow (\operatorname{IsAlmostPalindromic}\left(f\right))) \land ((\operatorname{IsAlmostPalindromic}\left(\operatorname{expand}\left(k, f\right)\right)) \Leftrightarrow (\operatorname{IsAlmostPalindromic}\left(f\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GaussianQuotient/CoefficientListInvariance.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Okada, So (2020). *Merged-log-concavity of rational functions, almost strictly unimodal sequences, and phase transitions of ideal boson-fermion gases*. DOI: [10.48550/arXiv.2003.02112](https://doi.org/10.48550/arXiv.2003.02112). URL: <https://arxiv.org/abs/2003.02112v2>.

*Commentary.*

For every polynomial f over a semiring and every s, the support of q^s f is the support of f shifted by s, and the coefficient of q^s f at n+s is that of f at n; since n -> n+s is strictly increasing it commutes with sorting, so supportCoeffList(q^s f)=supportCoeffList f. Over a commutative semiring and for k at least one, the support of f(q^k) is k times the support of f and the coefficient of f(q^k) at kn is that of f at n, so likewise supportCoeffList(f(q^k))=supportCoeffList f. No hypothesis f nonzero is needed: the zero polynomial has the empty list. Over Z these identities give that q^s f and f(q^k) are almost palindromic exactly when f is. Okada, arXiv:2003.02112v2, Definition 9.52(1), page 94, defines almost palindromic polynomials; the paper does not state this invariance, and the statement and proof are repo-derived. The support identity for q^s f is transported from Mathlib's AddMonoidAlgebra.support_coeff_single_mul.

## References

- Truth anchor: `D5/S3/Combinatorics/GaussianQuotient/CoefficientListInvariance.result`
- Truth anchor: `D5/S3/Combinatorics/GaussianQuotient/CoefficientListInvariance.supportCoeffList`
- Dependency: [D5/S3/Combinatorics/GaussianQuotient/OkadaPreMergedNonPalindromic](OkadaPreMergedNonPalindromic.md)
