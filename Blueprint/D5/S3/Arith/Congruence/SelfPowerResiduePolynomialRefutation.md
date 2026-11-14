# The full polynomial-existence assertion is false

## Abstract

The original domain of Englander XVII includes three even inputs incompatible with any affine complex polynomial.

**Definition 1.1 (One fixed polynomial for every residue class).**

$$(\operatorname{claim}\left(\right)) \Leftrightarrow (\forall k \in \mathbb{N},\; (0 < k) \Rightarrow (\exists P \in \mathbb{N} \to \mathbb{C}[X],\; (\forall r \in \mathbb{N},\; (r < 2*k) \Rightarrow (\operatorname{natDegree}\left(\operatorname{P}\left(r\right)\right) = k)) \land (\forall n \in \mathbb{N},\; (k < n) \Rightarrow (\operatorname{eval}\left(\operatorname{P}\left(\operatorname{mod}\left(n, 2*k\right)\right), (n: \mathbb{C})\right) = (\operatorname{emod}\left(\operatorname{a}\left(n\right), ((n: \mathbb{Z}))^{k}+(-1)^{k}\right): \mathbb{C})))))$$

*Formalization.* `D5/S3/Arith/Congruence/SelfPowerResiduePolynomialRefutation.claim` (`✓ std3`).

*Citation.* Mathew Englander (2020). *Comments on OEIS A081215*. URL: <https://oeis.org/A081215/a081215.pdf>.

*Commentary.*

For every positive natural k there is one family P, whose first 2k entries have degree exactly k. The same family must work simultaneously for every natural n greater than k. The coefficient field is C, so real and rational coefficients are included. Entries beyond the first 2k are immaterial. The exact integer sequence a and Euclidean remainder are shared with the cubic theorem.

**Theorem 1.2 (The literal closed claim is refuted).**

$$\neg (\operatorname{claim}\left(\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/SelfPowerResiduePolynomialRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/englander-a081215-xvii-polynomial-refutation` (refuted) by `D5/S3/Arith/Congruence/SelfPowerResiduePolynomialRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"englander-a081215-xvii-polynomial-refutation","declaration_gid":"D5/S3/Arith/Congruence/SelfPowerResiduePolynomialRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Mathew Englander (2020). *Comments on OEIS A081215*. URL: <https://oeis.org/A081215/a081215.pdf>.

*Commentary.*

At k=1, inputs 2, 4 and 6 are all even and all satisfy n>k. Their exact quotient values are 1, 41 and 5713, so the remainders modulo n-1 are 0, 2 and 3. Mathlib eq_X_add_C_of_natDegree_le_one expresses the even-class polynomial as an affine polynomial. Its three values must have zero second difference, while these values have second difference -1. The contradiction holds over C, and therefore excludes unrestricted real coefficients as well. The result concerns the full existence claim; the separate printed zero-class formula error is not counted as another problem. No statement about eventual polynomiality or the revised domain k>=2 is asserted.

## References

- Truth anchor: `D5/S3/Arith/Congruence/SelfPowerResiduePolynomialRefutation.claim`
- Truth anchor: `D5/S3/Arith/Congruence/SelfPowerResiduePolynomialRefutation.result`
- Dependency: [D5/S3/Arith/Congruence/SelfPowerQuotient](SelfPowerQuotient.md)
