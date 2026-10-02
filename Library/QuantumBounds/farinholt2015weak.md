---
bibkey: farinholt2015weak
authors: Jacob M. Farinholt; Alexander Ghazarians; James E. Troupe
year: 2015
title: "The Geometry of Qubit Weak Values"
doi: 10.48550/arXiv.1512.02113
url: https://arxiv.org/abs/1512.02113v2
claim: "For distinct, nonorthogonal pure states phi, psi the weak function is W_{phi,psi}(M) = <psi|M|phi>/<psi|phi> on Hermitian n x n matrices, restricted to the traceless subspace S. For orthonormal bases phi_0, ..., phi_(n-1) and psi_0, ..., psi_(n-1) of C^n with phi_0, psi_0 distinct and nonorthogonal, let R be the real span in S of the traceless projectors |phi_i><phi_i| - I/n and |psi_j><psi_j| - I/n. Every M in R has all weak values W_{phi_i,psi_j}(M) real; the paper conjectures that for M in S all these weak values are real if and only if M is in R."
strata_touched:
  - D5/S3/Quantum/Measurement/QunitRealWeakValueRefutation
license: citation-only
triage: anchor
---

# The Geometry of Qubit Weak Values

Jacob M. Farinholt, Alexander Ghazarians, James E. Troupe, arXiv:1512.02113v2
[quant-ph] (2015). Quotations are from the arXiv source.

The weak function (Section 2), for

> any ordered pair $(|\varphi\ra, |\psi\ra)$ of distinct, nonorthogonal pure states

is $W_{\varphi, \psi}(M) := \frac{\la\psi|M|\varphi\ra}{\la\psi|\varphi\ra}$, and
$\mathcal{W}_{\varphi, \psi}$ is its restriction to the trace-0 subspace
$\mathcal{S}$ of the Hermitian matrices.

The conclusions (Section 7) set up two orthonormal bases of $\mathbb{C}^n$
containing distinct, nonorthogonal $|\varphi_0\rangle$ and $|\psi_0\rangle$,
the traceless projectors
$|\varphi_i\rangle\langle\varphi_i| - \frac{1}{n}\mathbb{I}$ and
$|\psi_j\rangle\langle\psi_j| - \frac{1}{n}\mathbb{I}$, and their span
$\mathcal{R}_{\varphi, \psi}$ in $\mathcal{S}$, then state:

> Let $M \in \mc{R}_{\varphi, \psi}$. Then $\mc{W}_{\varphi_i, \psi_j}(M) \in \mbb{R}$, for any $i,j \in \{0, 1, \dots n-1\}$.

> Let $M \in \mc{S}$. Then for all $i,j \in \{0, 1, \dots n-1\}$, $\mc{W}_{\varphi_i, \psi_j}(M) \in \mbb{R}$ if and only if $M \in \mc{R}_{\varphi, \psi}$.

The first is a proposition and the second a conjecture.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.1512.02113 (arXiv-issued; v2 is the
  latest version and the record lists no journal reference).
- URL: https://arxiv.org/abs/1512.02113v2 (source `GeomWeakValues.tex`
  with LF line endings, md5 of the raw bytes
  `2a4d2ba941be85eff532d7e5745e392b`; the gzip tarball from
  https://arxiv.org/src/1512.02113v2 has md5
  `441fcb5d97b105a80c092d15c81d12b4`): the weak function (l. 113–116), its
  restriction to the trace-0 subspace (l. 119), the setting (l. 514), the
  proposition (l. 516–518) and the conjecture (l. 520–522).
