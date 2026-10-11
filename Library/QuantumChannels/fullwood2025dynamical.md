---
bibkey: fullwood2025dynamical
authors: James Fullwood and Arthur J. Parzygnat
year: 2025
title: "On Dynamical Measures of Quantum Information"
doi: 10.3390/e27040331
url: https://doi.org/10.3390/e27040331
claim: "Remark 1 conjectures that the entropy functional S(X) = -tr(X log|X|), restricted to quantum states over time (half the anticommutator of the input state tensor the identity with the Jamiołkowski matrix of a channel), is subadditive; Section 5 states the conjecture as non-negativity of the dynamical mutual information. Fullwood and Yang (arXiv:2608.28946) prove it for single-qubit inputs and state it open in general."
strata_touched:
  - D5/S3/Quantum/Information/FullwoodParzygnatSubadditivityRefutation
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.3390/e27040331

Source: https://doi.org/10.3390/e27040331 (Entropy 27(4), 331, 2025; arXiv:2306.01831).
The full text was read through Europe PMC (PMC12025998). Equation (15) and
Remark 1 are in Section 3; the dynamical mutual information is discussed in
Section 5.

Equation (15) and the definition of a quantum state over time read:

> $\varrho_{AB}$ is a quantum state over time if and only if there exists a
> completely positive trace-preserving map $\mathcal E:A\to B$ such that
> $\varrho_{AB}=\frac12\{\rho_A\otimes\mathbb 1,\mathscr J[\mathcal E]\}$.

Remark 1 ends:

> At present, we do not know of any examples of quantum states over time that
> violate subadditivity, which leads us to conjecture that the entropy
> functional S restricted to quantum states over time does in fact satisfy
> subadditivity.

Section 5 reads:

> From the perspective of dynamical measures of quantum information, such a
> conjecture is equivalent to the conjecture that the dynamical mutual
> information $I(\mathcal E,\rho)=S(\rho)+S(\mathcal E(\rho))-S(\mathcal E,\rho)$
> is non-negative for all processes $(\mathcal E,\rho)$.

J. Fullwood and B. Yang, *On the entropy of a pseudo-density matrix*,
https://arxiv.org/abs/2608.28946v1 (28 August 2026), fixes the conventions
used in the formal statement: Section 2 gives
$\varrho_{AB}=\frac12\{\rho_A\otimes\mathbb 1_B,\mathscr J[\mathcal E]\}$ with
$\mathscr J[\mathcal E]=\sum_{i,j}|i\rangle\langle j|\otimes\mathcal E(|j\rangle\langle i|)$,
"the Jamiołkowski matrix", which "is not to be confused with the Choi matrix";
Theorem 3.1 characterizes $S(X)=-\mathrm{tr}(X\log|X|)$ on unit-trace Hermitian
matrices; Theorem 4.1 proves subadditivity when the input is a single qubit
and the output dimension is arbitrary. Section 6 reads:

> it is presently unknown if PDM entropy is subadditive for 2-time
> pseudo-density matrices. Although we proved subadditivity for 2-time
> pseudo-density matrices whose initial state is that of a single qubit,
> numerically generated examples suggest that subadditivity may fail in
> higher dimensions. However, we still do not know of a simple, physically
> motivated example where subadditivity fails.
