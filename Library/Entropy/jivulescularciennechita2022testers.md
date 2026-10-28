---
bibkey: jivulescularciennechita2022testers
authors: Maria Anastasia Jivulescu; Cécilia Lancien; Ion Nechita
year: 2022
title: "Multipartite Entanglement Detection Via Projective Tensor Norms"
doi: 10.1007/s00023-022-01187-9
url: https://arxiv.org/abs/2010.06365v1
claim: "The paper introduces entanglement testers, trace-norm-to-Euclidean contractions of operator norm 1 whose tensor products detect entanglement when the projective tensor norm of the image exceeds 1; it shows that the realignment and SIC POVM criteria are testers, that both detect the Werner states exactly for mu < 1/d, and asks whether the testers are complete without a permutation of indices: does every entangled state have testers whose image has projective norm greater than 1?"
strata_touched:
  - D5/S3/Quantum/Entanglement/Witness/WernerTesterIncompleteness
license: citation-only
triage: anchor
---

# Jivulescu, Lancien and Nechita, multipartite entanglement detection via projective tensor norms

M. A. Jivulescu, C. Lancien and I. Nechita, Annales Henri Poincaré 23 (2022), 3791–3838, DOI 10.1007/s00023-022-01187-9; arXiv:2010.06365v1 (13 October 2020). Quotations are from the arXiv v1 TeX source, with the macros `\Tr`, `\ket` written as $\operatorname{Tr}$, $|\cdot\rangle$ and cross-references omitted.

The projective norm:

> $\|x\|_\pi := \inf \left\{ \sum_{k=1}^r \|a_k^1\| \cdots \|a_k^m\| \, : \, r \in \mathbb N, \ a_k^i\in A_i,\ x = \sum_{k=1}^r a_k^1 \otimes \cdots \otimes a_k^m \right\}$

The trace norm, $\|X\|_1 = \operatorname{Tr}\sqrt{X^*X}$, with $S_1^{d} := (\mathcal M_d(\mathbb C), \|\cdot\|_1)$.

Testers: to $(E_1,\dots,E_n)\in\mathcal M_d(\mathbb C)^n$ the source associates $\mathcal E: X\mapsto \sum_{k=1}^n \operatorname{Tr}(E_k^*X) |k\rangle \in \mathbb C^n$, and

> A $\mathbb C$-linear map $\mathcal E$ as above is called a $\mathbb C$-tester if $\|\mathcal E\|_{S_1^{d} \to \ell_2^{n}} = 1$.

Werner states:

> $\sigma_{\mu} := \mu\frac{I+F}{d(d+1)} + (1-\mu)\frac{I-F}{d(d-1)} \, , \ 0\leq\mu\leq 1$

The source records that $\sigma_\mu$ is entangled iff $\mu<1/2$ and that the realignment and SIC POVM testers detect $\sigma_\mu$ iff $\mu<1/d$.

The question:

> The main question that remains unanswered at this point is whether our family of entanglement criteria is complete, without allowing for permutation of indices before applying the testers. Concretely, we would like to know if, for any entangled state $\rho$ on $\mathbb C^{d_1}\otimes\cdots\otimes\mathbb C^{d_m}$, there exist testers $\mathcal E_i:S_1^{d_i}\to\ell_2^{n_i}$, $1\leq i\leq m$, such that $\|\mathcal E_1\otimes\cdots\otimes\mathcal E_m(\rho)\|_{\ell_2^{n_1}\otimes_\pi\cdots\otimes_\pi\ell_2^{n_m}}>1$. Even for bipartite states we are only able to show a weaker version of this statement.

## Verified locator

DOI: https://doi.org/10.1007/s00023-022-01187-9 (Annales Henri Poincaré 23 (2022), 3791–3838; the journal text was not read).

Source: https://arxiv.org/abs/2010.06365v1
- URL: https://arxiv.org/abs/2010.06365v1 (the e-print is a gzipped tar archive; member `main.tex`, 1381 lines, md5 `9fdc54de5d2ae5f44ba87345810560e0`):
  - the projective norm, Definition, l. 234–238;
  - the trace norm and $S_1^d$, l. 288–290;
  - testers, l. 339–352;
  - Werner states, l. 946, and their detection, l. 985–1006;
  - the question, Section `sec:conclusions`, l. 1365.
- The author list, the journal reference and the DOI are from Crossref and the arXiv metadata.
