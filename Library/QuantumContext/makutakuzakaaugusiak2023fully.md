---
bibkey: makutakuzakaaugusiak2023fully
authors: Owidiusz Makuta; Błażej Kuzaka; Remigiusz Augusiak
year: 2023
title: "Fully non-positive-partial-transpose genuinely entangled subspaces"
doi: 10.22331/q-2023-02-09-915
url: https://arxiv.org/abs/2203.16902v2
claim: "The paper constructs genuinely entangled subspaces from qudit stabilizers, relates genuine entanglement of a stabilizer subspace to the span of the commutation vectors of its generators, proves the case of two generators, and conjectures (Conjecture 1) that for prime local dimension d a genuinely entangled stabilizer subspace has commutation-space dimension at least the ceiling of (N-1)/(d-1)."
strata_touched:
  - D5/S3/Quantum/Codes/StabilizerGenuineEntanglementCommutationRank
license: citation-only
triage: anchor
---

# Fully non-positive-partial-transpose genuinely entangled subspaces

O. Makuta, B. Kuzaka and R. Augusiak, arXiv:2203.16902v2; Quantum 7, 915 (2023). Quotations are from the v2 TeX source.

Genuine entanglement:

> We say that $\ket{\psi}$ is separable with respect the bipartition $Q|\overline{Q}$ if $\ket{\psi}= \ket{\psi}_{Q}\otimes \ket{\psi}_{\overline{Q}}$ for some $\ket{\psi}_{Q}\in \mathcal{H}'=\bigotimes_{i\in Q}\mathcal{H}_{i}$. Otherwise, we call it entangled with respect to the bipartition $Q|\overline{Q}$. Then, we call $\ket{\psi}$ genuinely multipartite entangled iff it is entangled with respect to any nontrivial bipartition of the set $I_N$.

The generalized Pauli matrices:

> $X=\sum_{i=0}^{d-1}\ket{i+1}\!\bra{i},\qquad Z=\sum_{i=0}^{d-1}\omega^{i}\ket{i}\!\bra{i},$ where $\omega=\operatorname{exp}(2\pi \mathbb{i}/d)$ is a primitive $d$th root of unity

Stabilizers and stabilizer subspaces:

> Consider then a subgroup $\mathbb{S}\subset\mathbbm{P}_{N,d}$. It is called a stabilizer if: all elements of $\mathbb{S}$ mutually commute, given $a\in\mathbb{C}$, we have $a\mathbb{1}\in\mathbb{S}$ if and only if $a=1$. [...] Then, a stabilizer subspace $V$ is a maximal subspace stabilized by a given stabilizer

Conjecture 1:

> Given a stabilizer $\mathbb{S}=\langle G_{1},\dots,G_{k}\rangle$, if the local dimension $d$ is a prime number and the corresponding stabilizer subspace $V$ is genuinely entangled, then $\dim K(\mathbb{S}) \geqslant \left\lceil \frac{N-1}{d-1} \right\rceil.$

> However, since we were not able to prove Conjecture 1, the actual value of $p(N,d)$ remains unknown.

## Verified locator

Source: https://arxiv.org/abs/2203.16902v2
- URL: https://arxiv.org/abs/2203.16902v2 (source `final_5.tex`, md5 `8b745e95a3a5cb115f40e13c86b1e06d`):
  - genuine entanglement, l. 120–133;
  - the generalized Pauli matrices, l. 190–196;
  - the generalized Pauli group, stabilizers and stabilizer subspaces, l. 215–231;
  - Conjecture 1, l. 457–466;
  - the unproved status, l. 538.
- DOI: 10.22331/q-2023-02-09-915 (https://doi.org/10.22331/q-2023-02-09-915).
