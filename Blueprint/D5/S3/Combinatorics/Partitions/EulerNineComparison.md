# EulerNineComparison

## Abstract

All-index restricted nine-residue partition comparisons and positive products for the algebraic k10 route.

The base product supplier is Mathlib Nat.Partition.hasProd_powerSeriesMk_card_restricted, by Weiyi Wang under Apache 2.0. These proofs use actual restricted counting series, distinct allowed factors and exact stabilization at each arbitrary coefficient. The nine-block comparisons and positive decompositions implement the corresponding portion of the proposed ordinary source 'An all-index algebraic route to the denominator-ten eta signs', 3 November 2026, SHA256 f9c81115730bc353681e172d5b2ad17d199d66bd4602b56a5da7dfe8e185852b. The source is fallible mathematical input, not an acceptance certificate.

**Definition 1.1 (S).**

Lean statement: `D5/S3/Combinatorics/Partitions/EulerNineComparison.S`

*Formalization.* `D5/S3/Combinatorics/Partitions/EulerNineComparison.S` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

The actual restricted partition series allowing all positive parts not divisible by nine.

**Definition 1.2 (block).**

Lean statement: `D5/S3/Combinatorics/Partitions/EulerNineComparison.block`

*Formalization.* `D5/S3/Combinatorics/Partitions/EulerNineComparison.block` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

A pair of Euler factors with weights 9i+r and 9i+9-r.

**Definition 1.3 (pairWeight).**

Lean statement: `D5/S3/Combinatorics/Partitions/EulerNineComparison.pairWeight`

*Formalization.* `D5/S3/Combinatorics/Partitions/EulerNineComparison.pairWeight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

The two weights of a block, indexed by a Boolean colour.

**Theorem 1.4 (coeff_cancel_blocks).**

Lean statement: `D5/S3/Combinatorics/Partitions/EulerNineComparison.coeff_cancel_blocks`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/EulerNineComparison.coeff_cancel_blocks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

Distinct nine-block weights and two absent small weights cancel distinct reciprocals; every coefficient of the remaining product is nonnegative.

**Definition 1.5 (mixed).**

Lean statement: `D5/S3/Combinatorics/Partitions/EulerNineComparison.mixed`

*Formalization.* `D5/S3/Combinatorics/Partitions/EulerNineComparison.mixed` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

The finite product using one block type before a moving cut and another after it.

**Theorem 1.6 (coeff_finite_comparison).**

Lean statement: `D5/S3/Combinatorics/Partitions/EulerNineComparison.coeff_finite_comparison`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/EulerNineComparison.coeff_finite_comparison` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

A paid block difference and multiplicity-free cancellation prove the coefficientwise finite product comparison by telescoping.

**Theorem 1.7 (coeff_finite_42).**

Lean statement: `D5/S3/Combinatorics/Partitions/EulerNineComparison.coeff_finite_42`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/EulerNineComparison.coeff_finite_42` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

Every coefficient of the finite type-four cancellation product bounds that of the type-two product.

**Theorem 1.8 (coeff_finite_21).**

Lean statement: `D5/S3/Combinatorics/Partitions/EulerNineComparison.coeff_finite_21`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/EulerNineComparison.coeff_finite_21` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

Every coefficient of the finite type-two cancellation product bounds that of the type-one product.

**Definition 1.9 (Q).**

Lean statement: `D5/S3/Combinatorics/Partitions/EulerNineComparison.Q`

*Formalization.* `D5/S3/Combinatorics/Partitions/EulerNineComparison.Q` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

The actual restricted counting series excluding residues zero, r and nine minus r modulo nine. Source A=Q4, B=Q2 and C=Q1.

**Theorem 1.10 (coeff_Q_finite).**

Lean statement: `D5/S3/Combinatorics/Partitions/EulerNineComparison.coeff_Q_finite`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/EulerNineComparison.coeff_Q_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

For every n and N with n<9N, the degree-n coefficient of the infinite restricted series equals its finite cancelled product coefficient.

**Theorem 1.11 (coefficient_order).**

Lean statement: `D5/S3/Combinatorics/Partitions/EulerNineComparison.coefficient_order`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/EulerNineComparison.coefficient_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

For every natural n, including zero, the actual restricted products satisfy C[n] <= B[n] <= A[n].

**Definition 1.12 (D).**

Lean statement: `D5/S3/Combinatorics/Partitions/EulerNineComparison.D`

*Formalization.* `D5/S3/Combinatorics/Partitions/EulerNineComparison.D` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

The actual coloured partition product with one colour at residues three and six and two colours at residues four and five.

**Theorem 1.13 (multiplicity_relation).**

Lean statement: `D5/S3/Combinatorics/Partitions/EulerNineComparison.multiplicity_relation`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/EulerNineComparison.multiplicity_relation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

Actual reciprocal multiplicities prove AD=BC, without dividing any coefficient inequality.

**Theorem 1.14 (coeff_delta_nonnegative).**

Lean statement: `D5/S3/Combinatorics/Partitions/EulerNineComparison.coeff_delta_nonnegative`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/EulerNineComparison.coeff_delta_nonnegative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

For every n, the coefficient of AC-CD is nonnegative, by C(A-B)+D(A-C) and AD=BC.

**Definition 1.15 (lowerProduct).**

Lean statement: `D5/S3/Combinatorics/Partitions/EulerNineComparison.lowerProduct`

*Formalization.* `D5/S3/Combinatorics/Partitions/EulerNineComparison.lowerProduct` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

The actual lower product (1-X)AC appearing in the proposed W decomposition.

**Theorem 1.16 (coeff_lowerProduct_nonnegative).**

Lean statement: `D5/S3/Combinatorics/Partitions/EulerNineComparison.coeff_lowerProduct_nonnegative`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/EulerNineComparison.coeff_lowerProduct_nonnegative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

Every coefficient of (1-X)AC is nonnegative after exact cancellation of its sole part-one factor.

**Theorem 1.17 (coeff_lowerProduct_ge_one).**

Lean statement: `D5/S3/Combinatorics/Partitions/EulerNineComparison.coeff_lowerProduct_ge_one`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/EulerNineComparison.coeff_lowerProduct_ge_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

The coefficient of (1-X)AC is at least one at degree zero and every degree at least two.

**Theorem 1.18 (lowerProduct_initial).**

Lean statement: `D5/S3/Combinatorics/Partitions/EulerNineComparison.lowerProduct_initial`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/EulerNineComparison.lowerProduct_initial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kathrin Bringmann, Guoniu Han, Bernhard Heim and Ben Kane (2024). *Periodic sign changes for weakly holomorphic eta-quotients*. DOI: [10.48550/arXiv.2409.07164](https://doi.org/10.48550/arXiv.2409.07164). URL: <https://arxiv.org/abs/2409.07164v1>.

*Commentary.*

The exact lower product has constant coefficient one and degree-one coefficient zero.

These cancellation and comparison results have present mathematical consumers: EulerNineDissection identifies the actual quotient, EulerNineSquareDissection derives the cubic relation and squared coefficient bounds, and EtaSignK10 proves the complete source-defined denominator-ten endpoint. The separate ordinary manuscript is fallible input; independent formal review, original-problem acceptance, literature priority, unique status, CI and publication are not certified here.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/EulerNineComparison.D`
- Truth anchor: `D5/S3/Combinatorics/Partitions/EulerNineComparison.Q`
- Truth anchor: `D5/S3/Combinatorics/Partitions/EulerNineComparison.S`
- Truth anchor: `D5/S3/Combinatorics/Partitions/EulerNineComparison.block`
- Truth anchor: `D5/S3/Combinatorics/Partitions/EulerNineComparison.coeff_Q_finite`
- Truth anchor: `D5/S3/Combinatorics/Partitions/EulerNineComparison.coeff_cancel_blocks`
- Truth anchor: `D5/S3/Combinatorics/Partitions/EulerNineComparison.coeff_delta_nonnegative`
- Truth anchor: `D5/S3/Combinatorics/Partitions/EulerNineComparison.coeff_finite_21`
- Truth anchor: `D5/S3/Combinatorics/Partitions/EulerNineComparison.coeff_finite_42`
- Truth anchor: `D5/S3/Combinatorics/Partitions/EulerNineComparison.coeff_finite_comparison`
- Truth anchor: `D5/S3/Combinatorics/Partitions/EulerNineComparison.coeff_lowerProduct_ge_one`
- Truth anchor: `D5/S3/Combinatorics/Partitions/EulerNineComparison.coeff_lowerProduct_nonnegative`
- Truth anchor: `D5/S3/Combinatorics/Partitions/EulerNineComparison.coefficient_order`
- Truth anchor: `D5/S3/Combinatorics/Partitions/EulerNineComparison.lowerProduct`
- Truth anchor: `D5/S3/Combinatorics/Partitions/EulerNineComparison.lowerProduct_initial`
- Truth anchor: `D5/S3/Combinatorics/Partitions/EulerNineComparison.mixed`
- Truth anchor: `D5/S3/Combinatorics/Partitions/EulerNineComparison.multiplicity_relation`
- Truth anchor: `D5/S3/Combinatorics/Partitions/EulerNineComparison.pairWeight`
- Dependency: [D5/S3/Combinatorics/Partitions/RestrictedEulerCancellation](RestrictedEulerCancellation.md)
