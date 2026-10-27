---
bibkey: dzhenzhersakbaev2026slln
authors: Sviatoslav V. Dzhenzher; Vsevolod Zh. Sakbaev
year: 2026
title: "The Strong Law of Large Numbers for random semigroups on uniformly smooth Banach spaces"
doi: 10.1007/s43036-025-00481-7
url: https://arxiv.org/abs/2507.07658v3
claim: "The paper proves a strong law of large numbers for products of exponentials of i.i.d. bounded random operators: on a uniformly smooth Banach space the products exp(A_1 t/n)...exp(A_n t/n) converge almost surely in the strong operator topology to exp(t E A), uniformly for t in any segment; it proves the weak-operator version on every Banach space, deduces the strong version on l_1 by Schur's theorem, and conjectures the strong version on every Banach space."
strata_touched:
  - D5/S3/Analytic/Probability/RandomExponentialProductSLLN
license: citation-only
triage: anchor
---

# Dzhenzher and Sakbaev, the strong law of large numbers for random semigroups

S. V. Dzhenzher and V. Zh. Sakbaev, arXiv:2507.07658v3 (18 October 2025; v1 10 July 2025); Advances in Operator Theory 11 (2026), no. 1, article 4. Quotations are from the v3 TeX source, with macros expanded and theorem references replaced by bracketed descriptions.

Setting (Section 2): random elements of a Banach space are Bochner measurable maps on a complete probability space, random operators are random elements of the bounded operators $\mathcal L(\mathcal X)$ with the operator norm, and expectations are Bochner integrals.

Theorem 2.4 (SLLN in SOT):

> Let $\mathcal{X}$ be a uniformly smooth Banach space. Let $A\colon\Omega\to\mathcal L(\mathcal{X})$ be a generator of a semigroup $e^{At}$ such that $\|A\|$ is bounded. Let $A,A_1, A_2, \ldots$ be a sequence of i.i.d. random generators. Then $e^{A_1t/n} \ldots e^{A_nt/n}$ converges a.s. in SOT of $\|\cdot\|_\mathcal{X}$ to $e^{\mathbb E At}$ uniformly for $t>0$ in any segment

that is, for every $x$ and $T>0$, almost surely $\lim_n\sup_{t\in[0,T]}\|(e^{A_1t/n}\cdots e^{A_nt/n}-e^{\mathbb EAt})x\|=0$. The weak-operator version holds on every Banach space (Theorem 2.5), which gives the strong version on $\ell_1$, a space that is not uniformly smooth.

Conjecture 2.6:

> Let $\mathcal{X}$ be a Banach space. Then under the assumptions of [Theorem 2.4], $e^{A_1t/n} \ldots e^{A_nt/n}$ converges a.s. in SOT of $\|\cdot\|_\mathcal{X}$ to $e^{\mathbb E At}$ uniformly for $t>0$ in any segment.

## Verified locator

Source: https://arxiv.org/abs/2507.07658v3
- DOI: https://doi.org/10.1007/s43036-025-00481-7 (Advances in Operator Theory 11 (2026), no. 1, article 4; author list, journal, volume, issue and article number from Crossref).
- URL: https://arxiv.org/abs/2507.07658v3 (the e-print is a gzipped tar archive; the main text is the member `mains/slln_smooth.tex`, 603 lines, md5 `a977c94eb4adc6b7a26664cb45150780`, included by `main_arxiv.tex`):
  - random elements, random operators and expectations, l. 57–193;
  - Theorem 2.4, l. 195–204;
  - the conjecture, l. 224–229.
- The arXiv version dates are from the arXiv metadata.
