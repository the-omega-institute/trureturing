---
bibkey: axler2024innerproduct
authors: Sheldon Axler
year: 2024
title: Linear Algebra Done Right, fourth edition
doi: null
url: https://linear.axler.net/
claim: Cauchy-Schwarz for inner product spaces yields the covariance entry bound; uniform variances and a finite row-support bound then give the sparse covariance sum by direct summation.
strata_touched:
  - D5/S3/Quantum/Information/CovarianceSumBound
license: citation-only
triage: anchor
---

# Cauchy-Schwarz and the finite support sum

## Verified locator

The exact upstream locator is:
https://linear.axler.net/

The author's book page was retrieved successfully. It identifies Sheldon Axler,
the title above, the fourth edition, its open-access availability, and a 2024
English Kindle edition. It also links a later updated English PDF.

The round-17 seat locates the inner-product Cauchy-Schwarz inequality in section
6A of the fourth edition. This interior location was not checked in the book
here; no page or theorem number is added.

## Scope of the dependency

For Hermitian observables center A and B by their density-state means. The
weighted matrix pairing has real part Cov_D(A,B) and squared lengths Var_D(A)
and Var_D(B). For singular D this is a positive semidefinite pairing: one may
quotient by its null space, or map X to X sqrt(D) in the Hilbert-Schmidt space,
and apply ordinary Cauchy-Schwarz there. Thus

    |Cov_D(A,B)| ≤ sqrt(Var_D(A) Var_D(B)).

This is the same standard input formalized by the repository's existing
`abs_covariance_le`, whose Mathlib citation is retained. It is not a claim that
Axler defines this repository's density-state API.

For `covariance_sum_le_of_variance`, write v_x = Var_D(R_x) and assume
0 ≤ v_x ≤ Δ². The inequality gives |Cov_D(R_x,R_y)| ≤ Δ², since
v_x v_y ≤ Δ⁴. Let S_x = {y ∈ Q | Cov_D(R_x,R_y) ≠ 0}. Zero terms may be
removed, and each of the at most b remaining terms is bounded by Δ²:

    Σ_{y∈Q} |Cov_D(R_x,R_y)| = Σ_{y∈S_x} |Cov_D(R_x,R_y)|
      ≤ |S_x| Δ² ≤ b Δ².
    Σ_{x∈Q} Σ_{y∈Q} |Cov_D(R_x,R_y)| ≤ |Q| b Δ².

The sign of Δ is immaterial in this variance-assumption version. Empty Q also
satisfies the bound. This finite support summation is a standard direct
corollary written out here, not a separately named theorem attributed to the
book. The support size is a hypothesis; no locality or preparation-time law is
derived. The spectral version adds the input recorded in
`D5/L/Quantum/sharma2010variance`.

## What this note does and does not attest

Attested by this repository's own retrieval: the author's book-page title,
author, fourth-edition designation and the explicitly dated 2024 Kindle link.

Not attested here: section 6A or any book-interior page or theorem numbering.
Section 6A is the round-17 seat's report, relayed in the implementation brief
and issue #6298, and remains `ASSUMED-UNVERIFIED` as an interior locator.
The transport to a possibly degenerate density pairing and the finite support
sum are explicit standard derivations above, not claims of verbatim appearance
in the textbook. No priority or earliest-appearance claim is made.
