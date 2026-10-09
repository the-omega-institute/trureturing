---
bibkey: wangzhouchenfei2026conical
authors: H.-F. Wang; W. Zhou; L. Chen; S.-M. Fei
year: 2026
title: Estimating the concurrence for quantum states via symmetric measurements
doi: null
url: https://arxiv.org/abs/2606.31010v2
claim: "The lower bounds of concurrence induced by arbitrary two distinct conical 2-designs are comparable."
strata_touched:
  - D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability
license: citation-only
triage: anchor
---

## Verified locator

Source: https://arxiv.org/abs/2606.31010v2

Section IV, Theorem 2 and the conjecture immediately following it, PDF p. 8.
The two-constant definition of the bound is the source's reference [LBGEM],
Siudzińska, J. Phys. A 58 (2025) 375302, Section 7, Theorem 6.
The Crossref title query found no exact journal record for this title; no journal
DOI is asserted.

# Comparability of conical-design concurrence bounds

The source conjecture reads:

> The lower bounds of concurrence induced by arbitrary two distinct conical 2-designs are comparable.

A finite positive semidefinite family on the d-dimensional complex Hilbert space
satisfies $\sum_i E_i\otimes E_i=\alpha I+\beta F$ with $\alpha\geq\beta>0$,
where $F$ swaps the tensor factors. Its measurement correlation matrix has
entries $P_E(\rho)_{ij}=\operatorname{tr}[\rho(E_i\otimes E_j)]$.
Reference [LBGEM] gives the bound
$B_E(\rho)=\sqrt{2/[d(d-1)]}(\|P_E(\rho)\|_1-\alpha-\beta)/\beta$.
The trace norm is the sum of singular values, equivalently
$\operatorname{tr}\sqrt{P_E(\rho)^*P_E(\rho)}$.

Comparability means one uniform pointwise ordering over all positive
semidefinite trace-one bipartite states. The same family is used on both
subsystems. The claim includes equal designs and equal ratios; the source's
distinct-design assertion is contained in that statement. This comparison
does not assert that the bound is nonnegative, equals concurrence, detects
all PPT entanglement, or has a maximizing finite design.
