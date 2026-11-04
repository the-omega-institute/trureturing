# QuadraticSignProducts

## Abstract

A finite family of integer signs has sum congruent modulo4 to cardinality minus one plus its product. Separating factorials into odd and even factors evaluates the common paired product without rational denominators. A triangular finite-product interchange counts every multiplicity and supplies the genuine nested Legendre product.

A finite family of integer signs has sum congruent modulo4 to cardinality minus one plus its product. Separating factorials into odd and even factors evaluates the common paired product without rational denominators. A triangular finite-product interchange counts every multiplicity and supplies the genuine nested Legendre product.

Four-slot escape registrations are unfinished, tracked at https://github.com/the-omega-institute/trureturing/issues/26321. No declared_validated status is claimed. This registration debt is separate from the native mathematical proof.

**Theorem 1.1 (sign_sum_mod_four).**

Lean statement: `D5/S3/Arith/CharacterSums/QuadraticSignProducts.sign_sum_mod_four`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/QuadraticSignProducts.sign_sum_mod_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

This integral form of the sign-product parity rule avoids assigning a natural exponent to a possibly negative half sum. Repeated signs may be indexed separately.

**Definition 1.2 (oddProduct).**

Lean statement: `D5/S3/Arith/CharacterSums/QuadraticSignProducts.oddProduct`

*Formalization.* `D5/S3/Arith/CharacterSums/QuadraticSignProducts.oddProduct` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

The odd factors below twice the endpoint.

**Theorem 1.3 (oddProduct_succ).**

Lean statement: `D5/S3/Arith/CharacterSums/QuadraticSignProducts.oddProduct_succ`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/QuadraticSignProducts.oddProduct_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

The exact Lean declaration D5.S3.Arith.CharacterSums.QuadraticSignProducts.oddProduct_succ supplies this step in the proof chain described above; its complete Lean statement is retained in the scoped report. The pinned projection corpus has no formula for this new declaration.

**Theorem 1.4 (factorial_even_split).**

Lean statement: `D5/S3/Arith/CharacterSums/QuadraticSignProducts.factorial_even_split`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/QuadraticSignProducts.factorial_even_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

Separating the even and odd factors of a factorial, with no quotient in N.

**Definition 1.5 (oddPairProduct).**

Lean statement: `D5/S3/Arith/CharacterSums/QuadraticSignProducts.oddPairProduct`

*Formalization.* `D5/S3/Arith/CharacterSums/QuadraticSignProducts.oddPairProduct` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

Pairing an odd lower-half index j with 2m+1-j gives this integer product.

**Theorem 1.6 (oddPairProduct_eq).**

Lean statement: `D5/S3/Arith/CharacterSums/QuadraticSignProducts.oddPairProduct_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/QuadraticSignProducts.oddPairProduct_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

The exact Lean declaration D5.S3.Arith.CharacterSums.QuadraticSignProducts.oddPairProduct_eq supplies this step in the proof chain described above; its complete Lean statement is retained in the scoped report. The pinned projection corpus has no formula for this new declaration.

**Theorem 1.7 (oddPairProduct_even).**

Lean statement: `D5/S3/Arith/CharacterSums/QuadraticSignProducts.oddPairProduct_even`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/QuadraticSignProducts.oddPairProduct_even` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

The even m factorial-product identity used in the odd-prime-family parity proof. Multiplying through by the square denominator keeps the statement integral.

**Theorem 1.8 (oddPairProduct_odd).**

Lean statement: `D5/S3/Arith/CharacterSums/QuadraticSignProducts.oddPairProduct_odd`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/QuadraticSignProducts.oddPairProduct_odd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

For odd m the corresponding product is twice a square; the supplement at two will show that this extra factor has quadratic character one.

**Theorem 1.9 (factorial_character_square).**

Lean statement: `D5/S3/Arith/CharacterSums/QuadraticSignProducts.factorial_character_square`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/QuadraticSignProducts.factorial_character_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

The denominator factorials in the product identities are genuinely nonzero modulo p. This discharges the cancellation rather than treating a quotient formally.

**Theorem 1.10 (oddPairProduct_character).**

Lean statement: `D5/S3/Arith/CharacterSums/QuadraticSignProducts.oddPairProduct_character`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/QuadraticSignProducts.oddPairProduct_character` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

The common factorial product has character one or character two according to the parity of m. This lemma applies to both prime families in Chen-Sun.

**Definition 1.11 (intervalProduct).**

Lean statement: `D5/S3/Arith/CharacterSums/QuadraticSignProducts.intervalProduct`

*Formalization.* `D5/S3/Arith/CharacterSums/QuadraticSignProducts.intervalProduct` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

A central interval of even length, before evaluating the sign family.

**Theorem 1.12 (intervalProduct_pair).**

Lean statement: `D5/S3/Arith/CharacterSums/QuadraticSignProducts.intervalProduct_pair`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/QuadraticSignProducts.intervalProduct_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

Reflection of the upper half pairs j with 2m+1-j.

**Theorem 1.13 (intervalProduct_triangle).**

Lean statement: `D5/S3/Arith/CharacterSums/QuadraticSignProducts.intervalProduct_triangle`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/QuadraticSignProducts.intervalProduct_triangle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

The actual nested interval product is a weighted triangular product. The finite diagonal-flip supplier accounts for the multiplicities, rather than assuming them.

**Theorem 1.14 (weighted_sign_product_even).**

Lean statement: `D5/S3/Arith/CharacterSums/QuadraticSignProducts.weighted_sign_product_even`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/QuadraticSignProducts.weighted_sign_product_even` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

Square-one factors at even weights disappear from the triangular product.

**Theorem 1.15 (weighted_sign_product_odd).**

Lean statement: `D5/S3/Arith/CharacterSums/QuadraticSignProducts.weighted_sign_product_odd`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/QuadraticSignProducts.weighted_sign_product_odd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

The unpaired last odd weight contributes its sign.

**Theorem 1.16 (intervalProduct_character).**

Lean statement: `D5/S3/Arith/CharacterSums/QuadraticSignProducts.intervalProduct_character`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/QuadraticSignProducts.intervalProduct_character` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

The full nested product of the genuine Legendre signs is evaluated by the factorial identities above. The bound ensures every paired factor is nonzero.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/QuadraticSignProducts.factorial_character_square`
- Truth anchor: `D5/S3/Arith/CharacterSums/QuadraticSignProducts.factorial_even_split`
- Truth anchor: `D5/S3/Arith/CharacterSums/QuadraticSignProducts.intervalProduct`
- Truth anchor: `D5/S3/Arith/CharacterSums/QuadraticSignProducts.intervalProduct_character`
- Truth anchor: `D5/S3/Arith/CharacterSums/QuadraticSignProducts.intervalProduct_pair`
- Truth anchor: `D5/S3/Arith/CharacterSums/QuadraticSignProducts.intervalProduct_triangle`
- Truth anchor: `D5/S3/Arith/CharacterSums/QuadraticSignProducts.oddPairProduct`
- Truth anchor: `D5/S3/Arith/CharacterSums/QuadraticSignProducts.oddPairProduct_character`
- Truth anchor: `D5/S3/Arith/CharacterSums/QuadraticSignProducts.oddPairProduct_eq`
- Truth anchor: `D5/S3/Arith/CharacterSums/QuadraticSignProducts.oddPairProduct_even`
- Truth anchor: `D5/S3/Arith/CharacterSums/QuadraticSignProducts.oddPairProduct_odd`
- Truth anchor: `D5/S3/Arith/CharacterSums/QuadraticSignProducts.oddProduct`
- Truth anchor: `D5/S3/Arith/CharacterSums/QuadraticSignProducts.oddProduct_succ`
- Truth anchor: `D5/S3/Arith/CharacterSums/QuadraticSignProducts.sign_sum_mod_four`
- Truth anchor: `D5/S3/Arith/CharacterSums/QuadraticSignProducts.weighted_sign_product_even`
- Truth anchor: `D5/S3/Arith/CharacterSums/QuadraticSignProducts.weighted_sign_product_odd`
