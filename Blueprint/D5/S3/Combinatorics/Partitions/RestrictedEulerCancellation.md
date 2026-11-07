# RestrictedEulerCancellation

## Abstract

Exact restricted-partition Euler cancellation with finite and injectively indexed removed weights.

The base product supplier is Mathlib Nat.Partition.hasProd_powerSeriesMk_card_restricted, by Weiyi Wang under Apache 2.0. These proofs use actual restricted counting series, distinct allowed factors and exact stabilization at each arbitrary coefficient. The nine-block comparisons and positive decompositions implement the corresponding portion of the proposed ordinary source 'An all-index algebraic route to the denominator-ten eta signs', 3 November 2026, SHA256 f9c81115730bc353681e172d5b2ad17d199d66bd4602b56a5da7dfe8e185852b. The source is fallible mathematical input, not an acceptance certificate.

**Definition 1.1 (restrictedSeries).**

Lean statement: `D5/S3/Combinatorics/Partitions/RestrictedEulerCancellation.restrictedSeries`

*Formalization.* `D5/S3/Combinatorics/Partitions/RestrictedEulerCancellation.restrictedSeries` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

The actual counting series for partitions with a specified allowed-part predicate.

**Theorem 1.2 (coeff_restricted_nonnegative).**

Lean statement: `D5/S3/Combinatorics/Partitions/RestrictedEulerCancellation.coeff_restricted_nonnegative`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/RestrictedEulerCancellation.coeff_restricted_nonnegative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

Every restricted counting coefficient is nonnegative.

**Theorem 1.3 (restricted_constant_one).**

Lean statement: `D5/S3/Combinatorics/Partitions/RestrictedEulerCancellation.restricted_constant_one`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/RestrictedEulerCancellation.restricted_constant_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

The empty partition gives constant coefficient one for every predicate.

**Theorem 1.4 (coeff_restricted_ge_one_of_parts).**

Lean statement: `D5/S3/Combinatorics/Partitions/RestrictedEulerCancellation.coeff_restricted_ge_one_of_parts`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/RestrictedEulerCancellation.coeff_restricted_ge_one_of_parts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

An explicit positive allowed multiset of total degree n supplies a coefficient lower bound of one.

**Theorem 1.5 (coeff_restricted_ge_one_of_two_three).**

Lean statement: `D5/S3/Combinatorics/Partitions/RestrictedEulerCancellation.coeff_restricted_ge_one_of_two_three`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/RestrictedEulerCancellation.coeff_restricted_ge_one_of_two_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

Allowed parts two and three give a coefficient at least one in every degree zero or at least two.

**Theorem 1.6 (coeff_restricted_congr).**

Lean statement: `D5/S3/Combinatorics/Partitions/RestrictedEulerCancellation.coeff_restricted_congr`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/RestrictedEulerCancellation.coeff_restricted_congr` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

Allowed-part predicates agreeing on positive parts up to n have the same degree-n coefficient.

**Theorem 1.7 (restricted_mul_one_sub).**

Lean statement: `D5/S3/Combinatorics/Partitions/RestrictedEulerCancellation.restricted_mul_one_sub`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/RestrictedEulerCancellation.restricted_mul_one_sub` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

Cancelling one allowed positive Euler factor gives exactly the restricted series with that part removed.

**Theorem 1.8 (restricted_mul_euler_finset).**

Lean statement: `D5/S3/Combinatorics/Partitions/RestrictedEulerCancellation.restricted_mul_euler_finset`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/RestrictedEulerCancellation.restricted_mul_euler_finset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

Cancelling a finite set of distinct positive allowed parts gives exactly its complementary restricted product.

**Theorem 1.9 (coeff_cancelled_product_nonnegative).**

Lean statement: `D5/S3/Combinatorics/Partitions/RestrictedEulerCancellation.coeff_cancelled_product_nonnegative`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/RestrictedEulerCancellation.coeff_cancelled_product_nonnegative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

Finite cancellation preserves nonnegativity because the result is an actual counting series.

**Theorem 1.10 (restricted_mul_indexed_euler).**

Lean statement: `D5/S3/Combinatorics/Partitions/RestrictedEulerCancellation.restricted_mul_indexed_euler`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/RestrictedEulerCancellation.restricted_mul_indexed_euler` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

The exact finite cancellation identity is invariant under any injective indexing of the allowed weights.

**Theorem 1.11 (coeff_cancelled_indexed_product_nonnegative).**

Lean statement: `D5/S3/Combinatorics/Partitions/RestrictedEulerCancellation.coeff_cancelled_indexed_product_nonnegative`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/RestrictedEulerCancellation.coeff_cancelled_indexed_product_nonnegative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

An injective finite family of allowed weights cancels to a nonnegative counting product.

These cancellation and comparison results have present mathematical consumers: EulerNineDissection identifies the actual quotient, EulerNineSquareDissection derives the cubic relation and squared coefficient bounds, and EtaSignK10 proves the complete source-defined denominator-ten endpoint. The separate ordinary manuscript is fallible input; independent formal review, original-problem acceptance, literature priority, unique status, CI and publication are not certified here.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/RestrictedEulerCancellation.coeff_cancelled_indexed_product_nonnegative`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RestrictedEulerCancellation.coeff_cancelled_product_nonnegative`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RestrictedEulerCancellation.coeff_restricted_congr`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RestrictedEulerCancellation.coeff_restricted_ge_one_of_parts`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RestrictedEulerCancellation.coeff_restricted_ge_one_of_two_three`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RestrictedEulerCancellation.coeff_restricted_nonnegative`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RestrictedEulerCancellation.restrictedSeries`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RestrictedEulerCancellation.restricted_constant_one`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RestrictedEulerCancellation.restricted_mul_euler_finset`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RestrictedEulerCancellation.restricted_mul_indexed_euler`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RestrictedEulerCancellation.restricted_mul_one_sub`
- Dependency: [D5/S3/Combinatorics/Partitions/OrdinaryEulerProduct](OrdinaryEulerProduct.md)
