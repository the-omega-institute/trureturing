---
bibkey: uhlmann2023spectralmajorization
authors: Jeffrey Uhlmann
year: 2023
title: "Partial Proof of a Conjecture with Implications for Spectral Majorization"
doi: 10.46571/JCI.2023.2.4
url: https://arxiv.org/abs/2309.01302v1
claim: "Section 4 considers whether the diagonal-spectrum majorization property extends to unrestricted positive definite similarities; a real symmetric positive definite matrix in dimension seven refutes that extension."
strata_touched:
  - D5/S3/Quantum/Matrix/UhlmannDiagonalMajorizationRefutation
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.46571/JCI.2023.2.4

Source: https://arxiv.org/abs/2309.01302v1

The arXiv v1 text, Section 3, page 5, defines majorization by:

> An alternative definition is that x ≺ y if and only if

> x = Sy , (3.2)

> where S is a doubly-stochastic matrix, i.e., nonnegative with every row and column sum equal to unity.

Section 3, page 5, states:

> Definition (Special PD-Diagonalizable): A given n × n matrix M = PDP⁻¹, n ≤ k, is defined to be special PD-diagonalizable if matrix D is diagonal and positive-definite matrix P is real symmetric.

> Majorization Theorem: The spectrum of a special PD-diagonalizable matrix is majorized by its diagonal.

Section 4, page 7, considers the unrestricted extension:

> However, the fact that such a construction does not generally exist for n > 6 does not necessarily imply that the diagonal-spectrum majorization relationship does not hold in general.

> Empirical investigation may be able to provide sufficient evidence to justify a conjecture or, alternatively, empirical and/or analytical efforts may identify counterexamples that constrain such generalizations

The unrestricted assertion quantifies over all natural dimensions, real symmetric positive definite P and real diagonal D. The Lean predicate uses the source's doubly-stochastic definition: Majorizes y x means there exists S in doublyStochastic with x = Matrix.mulVec S y. Its refutation uses P with block rows (10,1,2eᵀ), (1,10,2eᵀ), (2e,2e,10I₅), and D = diag(1,20,2,2,2,2,2). The resulting diagonal has minimum 64/63, greater than the least spectral entry 1. The dimensional restriction in the source's theorem is retained; the unrestricted assertion is the proposition refuted.

The exact experiment is in the private repository the-omega-institute/trureturing-experiments, directory docs/reports/uhlmann-2023-pd-diagonalizable-majorization, commit 65de77d642c949fc7345e8925672d34307a37483. The source check.py has SHA-256 7e2bce3c0890339462b9868b892f54fc5ae6b6eccf29c54941f1fa5e7bb75cef; preregistration #18572 records exit 0 and RESULT PASS. The Lean proof independently checks the positive definite certificate, inverse, diagonal and stochastic obstruction.

Literature completeness is ASSUMED-UNVERIFIED. The journal-revision and related-paper readings recorded in #18572 are source-reported; they do not replace the kernel proof of the refutation.
