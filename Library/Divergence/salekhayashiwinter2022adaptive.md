---
bibkey: salekhayashiwinter2022adaptive
authors: Farzin Salek; Masahito Hayashi; Andreas Winter
year: 2022
title: "Usefulness of adaptive strategies in asymptotic quantum channel discrimination"
doi: 10.1103/PhysRevA.105.022419
url: https://arxiv.org/abs/2011.06569v3
claim: "The paper compares adaptive and non-adaptive strategies for discriminating two channels asymptotically. For classical-quantum channels it shows that adaptive strategies give no advantage in the Chernoff, Hoeffding and Stein settings. For quantum channels it bounds the parallel Chernoff exponent through a positive-definiteness condition. For the Harrow et al. channel pair, which adaptive strategies discriminate perfectly with two uses, it proves the parallel exponent finite, at most 13.83, and conjectures that it equals 1."
strata_touched:
  - D5/S3/Quantum/QuantumChannels/HarrowParallelChernoffExponentRefutation
license: citation-only
triage: anchor
---

# Salek, Hayashi and Winter, adaptive strategies in asymptotic channel discrimination

F. Salek, M. Hayashi and A. Winter, arXiv:2011.06569v3 [quant-ph]; Phys. Rev. A 105, 022419 (2022). Quotations are from the v3 TeX source, with macros expanded.

Parallel discrimination of quantum channels: the error probability is

> $P_{e,\mathbb{P}}^{(n)} = \frac12 \left( 1-\frac12\left\| \mathcal{M}^{\otimes n}-\overline{\mathcal{M}}^{\otimes n} \right\|_\diamond \right)$

and the non-adaptive Chernoff exponent is $C^{\mathbb P}(\mathcal M,\overline{\mathcal M})=\lim_{n\to\infty}-\frac1n\log P_{e,\mathbb{P}}^{(n)}$, possibly $+\infty$.

Example 5, the Harrow et al. channels from two qubits $A\otimes C$ to one qubit:

> $\mathcal{M}(\rho^A\otimes\gamma^C) = |0\rangle\langle0| \langle0|\gamma|0\rangle + |0\rangle\langle0| \langle1|\gamma|1\rangle \langle0|\rho|0\rangle + \frac12 I \langle1|\gamma|1\rangle \langle1|\rho|1\rangle$,
>
> $\overline{\mathcal{M}}(\rho^A\otimes\gamma^C) = |+\rangle\langle+| \langle0|\gamma|0\rangle + |1\rangle\langle1| \langle1|\gamma|1\rangle \langle+|\rho|+\rangle + \frac12 I \langle1|\gamma|1\rangle \langle-|\rho|-\rangle$,

extended by linearity. After the upper bound $C^{\mathbb P}\le13.83$:

> Note that a lower bound is the Chernoff bound of the two pure output states $|0\rangle\langle0| = \mathcal{M}(|00\rangle\langle00|)$ and $|+\rangle\langle+| = \overline{\mathcal{M}}(|00\rangle\langle00|)$, which is $\log 2 = 1$, so $C^{\mathbb{P}}(\mathcal{M},\overline{\mathcal{M}}) \geq 1$. It seems reasonable to conjecture that this is optimal, but we do not have at present a proof of it.

## Verified locator

Source: https://arxiv.org/abs/2011.06569v3
- DOI: https://doi.org/10.1103/PhysRevA.105.022419 (Phys. Rev. A 105, 022419 (2022); author list, journal, volume, issue and article number from Crossref).
- URL: https://arxiv.org/abs/2011.06569v3. The e-print is a gzipped tar archive; its member `cq-channel-PRXQ-revised.14jan22mh+aw.tex` has 3699 lines and md5 `f950feede0e95a6a2aa6ab8f74ee23d0`. Locations:
  - the diamond-norm error probability and the Chernoff exponent, l. 1290–1313;
  - Example 5, l. 1399–1442;
  - the conjecture, l. 1511–1514.
- The arXiv version is from the arXiv metadata.
