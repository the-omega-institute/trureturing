---
bibkey: alhejjiknill2024spinalignment
authors: Mohammad A. Alhejji; Emanuel Knill
year: 2024
title: "Towards a Resolution of the Spin Alignment Problem"
doi: 10.1007/s00220-024-04980-1
url: https://arxiv.org/abs/2307.06894v3
claim: "The paper generalizes spin alignment problems, proves alignment results for Schatten norms of integer order through an overlap lemma on traces of ordered products, and asks whether domination of all ordered-product traces implies the Schatten-norm inequality for every real order p in [1, ∞)."
strata_touched:
  - D5/S3/Quantum/Schatten/FractionalSchattenAlignmentRefutation
license: citation-only
triage: anchor
---

# Towards a Resolution of the Spin Alignment Problem

M. A. Alhejji and E. Knill, arXiv:2307.06894v3 (5 March 2024); Commun. Math. Phys. 405(5) (2024), 119. Quotations are from the v3 TeX source.

The spectrum (Section 1):

> For a self-adjoint operator \(S\), let $\lambda(S)$ denote the tuple whose entries are the eigenvalues of \(S\) (with multiplicity) ordered non-increasingly.

Schatten norms (Section 2):

> $|| R ||_{p} := \tr (|R|^{p})^{\frac{1}{p}},$ where $|R|$ denotes the absolute value $\sqrt{R^{*} R}$.

The question (Concluding remarks, item 1):

> (\textbf{Schatten norms of non-integer order}) We used Cor.~\ref{cor: ovelap of absolute value of trace} to resolve the spin alignment problem for Schatten norms of integer order. It is of interest to know if a similar approach can be used in cases where the order of the norm is not an integer. Suppose that $A_{0}, A_{1}, B_{0}, B_{1} \geq 0$ satisfy $\lambda(A_{0}) = \lambda(B_{0})$, $\lambda(A_{1}) = \lambda(B_{1})$. For a string $s \in \{0, 1\}^{*}$, define the ordered products $\Pi_s (A_{0}, A_{1}) := \Pi_{i \in [|s|]} A_{s(i)}$ and $\Pi_s(B_{0}, B_{1}) := \Pi_{i \in [|s|]} B_{s(i)}$. If for all strings $s$, $\tr(\Pi_s (A_{0}, A_{1})) \geq |\tr(\Pi_s (B_{0}, B_{1}))|$, does it hold that $|| A_{0} + A_{1} ||_{p} \geq || B_{0} + B_{1} ||_{p}$ for all $p \in [1,\infty)$? If so, then the overlap lemma may be used to prove the spin alignment conjecture for all Schatten norms, and by extension for the von Neumann entropy as well.

## Verified locator

Source: https://arxiv.org/abs/2307.06894v3
- URL: https://arxiv.org/abs/2307.06894v3 (the e-print is a tar archive; member `main.tex`, md5 `3eda922ce9b82255e4c4bcc30c3a2767`, 964 lines):
  - the spectrum $\lambda(S)$, l. 117;
  - Schatten norms, Eq. `eq: p-Schatten norm`, l. 274–278;
  - the question on Schatten norms of non-integer order, l. 759.
- DOI: 10.1007/s00220-024-04980-1 (https://doi.org/10.1007/s00220-024-04980-1; Crossref lists Communications in Mathematical Physics, volume 405, issue 5, article 119, published 29 April 2024).
