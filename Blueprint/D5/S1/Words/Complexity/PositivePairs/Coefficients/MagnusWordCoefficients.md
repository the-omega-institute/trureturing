# MagnusWordCoefficients

## Abstract

Actual Magnus coefficients equal scattered-subword multiplicities.

Magnus expansions and shuffle or infiltration identities are classical context, but the complete recursively indexed positive-pair construction below is a repository route. Indices are retained even when two evaluated pairs coincide.

**Definition 1.1 (Actual positive-word Magnus polynomial).**

$$magnusPolynomial$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairs/Coefficients/MagnusWordCoefficients.magnusPolynomial` (`✓ std3`).

*Citation.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

magnusPolynomial []=1 and magnusPolynomial (a::w)=(1+X_a)*magnusPolynomial w, preserving source order.

**Theorem 1.2 (Magnus is multiplicative on concatenation).**

$$magnusPolynomialappend$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/PositivePairs/Coefficients/MagnusWordCoefficients.magnusPolynomial_append` (`✓ std3`). ∎

*Citation.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For all finite words left,right, the Magnus polynomial of left++right is the product of their Magnus polynomials.

**Theorem 1.3 (Magnus coefficients are scattered counts).**

$$magnusPolynomialcoeffscatteredCount$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/PositivePairs/Coefficients/MagnusWordCoefficients.magnusPolynomial_coeff_scatteredCount` (`✓ std3`). ∎

*Citation.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

With decidable equality on A, the coefficient at pattern in magnusPolynomial source is exactly the natural scatteredCount pattern source, cast to Z.

**Definition 1.4 (Degree-one letter sum).**

$$wordAbelianization$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairs/Coefficients/MagnusWordCoefficients.wordAbelianization` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

wordAbelianization recursively sums the singleton wordMonomial for each source letter and maps the empty word to zero.

**Theorem 1.5 (Abelianization is additive).**

$$wordAbelianizationappend$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/PositivePairs/Coefficients/MagnusWordCoefficients.wordAbelianization_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

wordAbelianization (left++right) is the sum of the two word abelianizations.

**Theorem 1.6 (Singleton coefficients count letters).**

$$wordAbelianizationcoeffsingleton$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/PositivePairs/Coefficients/MagnusWordCoefficients.wordAbelianization_coeff_singleton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

With decidable equality, the coefficient of [b] in wordAbelianization source is scatteredCount [b] source, cast to Z.

**Theorem 1.7 (No empty coefficient).**

$$wordAbelianizationcoeffempty$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/PositivePairs/Coefficients/MagnusWordCoefficients.wordAbelianization_coeff_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For every source, wordAbelianization source has coefficient zero at the empty free word.

## References

- Truth anchor: `D5/S1/Words/Complexity/PositivePairs/Coefficients/MagnusWordCoefficients.magnusPolynomial`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairs/Coefficients/MagnusWordCoefficients.magnusPolynomial_append`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairs/Coefficients/MagnusWordCoefficients.magnusPolynomial_coeff_scatteredCount`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairs/Coefficients/MagnusWordCoefficients.wordAbelianization`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairs/Coefficients/MagnusWordCoefficients.wordAbelianization_append`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairs/Coefficients/MagnusWordCoefficients.wordAbelianization_coeff_empty`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairs/Coefficients/MagnusWordCoefficients.wordAbelianization_coeff_singleton`
- Dependency: [D5/S1/Words/Complexity/PositivePairs/Coefficients/CutoffCoefficientAlgebra](CutoffCoefficientAlgebra.md)
