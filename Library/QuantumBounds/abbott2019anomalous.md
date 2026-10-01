---
bibkey: abbott2019anomalous
authors: Alastair A. Abbott; Ralph Silva; Julian Wechs; Nicolas Brunner; Cyril Branciard
year: 2019
title: "Anomalous Weak Values Without Post-Selection"
doi: 10.22331/q-2019-10-14-194
url: https://arxiv.org/abs/1805.09364v3
claim: "Without post-selection the mean product of the pointer positions of n sequential weak measurements of A_1, ..., A_n on rho is 2^(-(n-1)) Tr[{A_1, {A_2, ..., {A_(n-1), A_n}...}} rho]; for two projection observables (eigenvalues 0 and 1) it is at least -1/8, and the authors conjecture the bound -1/8 for every number n of projection observables."
strata_touched:
  - D5/S3/Quantum/Measurement/SequentialWeakPointerRefutation
license: citation-only
triage: anchor
---

# Anomalous Weak Values Without Post-Selection

A. A. Abbott, R. Silva, J. Wechs, N. Brunner and C. Branciard, arXiv:1805.09364
(v1 2018-05-23, v3 2019-09-12); Quantum 3, 194 (2019). Subject: quant-ph.

The paper shows that sequential weak measurements without post-selection can
produce anomalous weak values. For two sequential weak measurements of `A`
then `B` on `ψ`, the mean product of the pointer positions is the real part of
the sequential weak value `(BA)_ψ = ⟨ψ|BA|ψ⟩`. For two projection observables
(eigenvalues 0 and 1) the Appendix proves `Re[(BA)_ψ] ≥ −1/8` for every pure or
mixed state. For `n` measurements the Appendix expresses the mean product of
the pointer positions as the nested anticommutator
`2^{−(n−1)} Tr[{A_1, {A_2, …, {A_{n−1}, A_n}…}} ρ]`, and the section on more
measurements states:

> Interestingly, by numerically minimising the mean product of the pointer
> positions for sequences of up to 5 projection observables, we were unable to
> obtain a value smaller than −1/8, and we conjecture that this is in fact the
> case for all n.

## Verified locator

- DOI: https://doi.org/10.22331/q-2019-10-14-194 (the journal page was not
  read).
- URL: https://arxiv.org/abs/1805.09364v3 (source retrieved 2026-09-30):
  `anomalous_wv_no_postselection_final.tex`, section "More measurements" (the
  conjecture), Appendix "Proof that Re[(BA)_ψ] ≥ −1/8 for two projection
  observables" and subsection "Generalisation to n sequential weak
  measurements" (the nested anticommutator).
