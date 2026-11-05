# QuadraticClassNumberSquare

## Abstract

Comparing the actual Dedekind-zeta residue and the proved quadratic factorization identifies L(1). The squared functional equation gives L(0)^2=h^2 for the genuine maximal-order ideal class number. The finite doubling identity gives c^2=(2-chi(2))^2*h^2. Finite sign parity then proves h odd; positivity is the standard cardinality theorem. No class-number formula is an assumed premise.

Comparing the actual Dedekind-zeta residue and the proved quadratic factorization identifies L(1). The squared functional equation gives L(0)^2=h^2 for the genuine maximal-order ideal class number. The finite doubling identity gives c^2=(2-chi(2))^2*h^2. Finite sign parity then proves h odd; positivity is the standard cardinality theorem. No class-number formula is an assumed premise.

Four-slot escape registrations are unfinished, tracked at https://github.com/the-omega-institute/trureturing/issues/26321. No declared_validated status is claimed. This registration debt is separate from the native mathematical proof.

**Theorem 1.1 (LFunction_one_eq_classNumber).**

Lean statement: `D5/S3/Analytic/Zeta/QuadraticClassNumberSquare.LFunction_one_eq_classNumber`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Zeta/QuadraticClassNumberSquare.LFunction_one_eq_classNumber` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

The value at one is obtained from the genuine number-field residue and the quadratic Euler factorization. No finite character-sum formula is assumed.

**Theorem 1.2 (LFunction_zero_sq_classNumber).**

Lean statement: `D5/S3/Analytic/Zeta/QuadraticClassNumberSquare.LFunction_zero_sq_classNumber`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Zeta/QuadraticClassNumberSquare.LFunction_zero_sq_classNumber` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

The squared functional equation suffices: its sign need not be computed to identify the square of L(0) with the square of the actual ideal class number.

**Definition 1.3 (quadraticExcess).**

Lean statement: `D5/S3/Analytic/Zeta/QuadraticClassNumberSquare.quadraticExcess`

*Formalization.* `D5/S3/Analytic/Zeta/QuadraticClassNumberSquare.quadraticExcess` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

An integer-valued half-interval character sum, including its zero term. The value is independent of the class-number definition.

**Theorem 1.4 (quadraticExcess_sq_classNumber).**

Lean statement: `D5/S3/Analytic/Zeta/QuadraticClassNumberSquare.quadraticExcess_sq_classNumber`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Zeta/QuadraticClassNumberSquare.quadraticExcess_sq_classNumber` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

Sufficient actual-class-number bridge for congruences depending on h squared. In particular, this does not redefine h as a character sum.

**Theorem 1.5 (quadraticExcess_eq_range).**

Lean statement: `D5/S3/Analytic/Zeta/QuadraticClassNumberSquare.quadraticExcess_eq_range`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Zeta/QuadraticClassNumberSquare.quadraticExcess_eq_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

Least representatives identify the excess with its literal finite positive interval; the additional index zero contributes zero.

**Theorem 1.6 (quadraticExcess_mod_two).**

Lean statement: `D5/S3/Analytic/Zeta/QuadraticClassNumberSquare.quadraticExcess_mod_two`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Zeta/QuadraticClassNumberSquare.quadraticExcess_mod_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

Every nonzero lower-half character value is odd, so the excess has the parity of the interval length. In this prime family that length is odd.

**Theorem 1.7 (classNumber_odd).**

Lean statement: `D5/S3/Analytic/Zeta/QuadraticClassNumberSquare.classNumber_odd`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Zeta/QuadraticClassNumberSquare.classNumber_odd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

Oddness of the genuine maximal-order class number follows from the proved squared bridge and the parity of the finite interval.

## References

- Truth anchor: `D5/S3/Analytic/Zeta/QuadraticClassNumberSquare.LFunction_one_eq_classNumber`
- Truth anchor: `D5/S3/Analytic/Zeta/QuadraticClassNumberSquare.LFunction_zero_sq_classNumber`
- Truth anchor: `D5/S3/Analytic/Zeta/QuadraticClassNumberSquare.classNumber_odd`
- Truth anchor: `D5/S3/Analytic/Zeta/QuadraticClassNumberSquare.quadraticExcess`
- Truth anchor: `D5/S3/Analytic/Zeta/QuadraticClassNumberSquare.quadraticExcess_eq_range`
- Truth anchor: `D5/S3/Analytic/Zeta/QuadraticClassNumberSquare.quadraticExcess_mod_two`
- Truth anchor: `D5/S3/Analytic/Zeta/QuadraticClassNumberSquare.quadraticExcess_sq_classNumber`
- Dependency: [D5/S3/Analytic/Zeta/QuadraticZetaFactorization](QuadraticZetaFactorization.md)
- Dependency: [D5/S3/Arith/QuadraticFields/QuadraticImaginaryInvariants](../../Arith/QuadraticFields/QuadraticImaginaryInvariants.md)
