---
bibkey: divianszkymartonbenevertesi2023certification
authors: Péter Diviánszky; István Márton; Erika Bene; Tamás Vértesi
year: 2023
title: "Certification of qubits in the prepare-and-measure scenario with large input alphabet and connections with the Grothendieck constant"
doi: 10.1038/s41598-023-39529-0
url: https://arxiv.org/abs/2211.17185v2
claim: "The paper certifies qubits in prepare-and-measure scenarios through the matrix functions L_k(M), proves L_k(M) <= k L(M), notes that the bound is tight for k = 2 by the CHSH expression, and conjectures that it is not tight for k >= 3."
strata_touched:
  - D5/S3/Quantum/Optimization/PrepareMeasureLkBound
license: citation-only
triage: anchor
---

# Certification of qubits in the prepare-and-measure scenario with large input alphabet and connections with the Grothendieck constant

P. Diviánszky, I. Márton, E. Bene and T. Vértesi, arXiv:2211.17185v2 (2023-08-29); Sci. Rep. 13, 13200 (2023). Quotations are from the v2 TeX source.

Notation (Methods):

> it is convenient to define by $\W{n}{k} = \{\Id{k}_j \,|\, j = 1, 2, \dots, k\}^n \subset \Mat{n}{k}$ the set of matrices whose rows are all $0$s, but exactly one is $1$. Let $\Perm{n} \subset\Mat{n}{n}$ denote the set of permutation matrices. Let $\SM{M} = \sum_{i=1}^n \left\|M_i\right\|_1$ denote the Manhattan norm of the matrix $M \in \Mat{n}{m}$.

The definition of $L_k$:

> &L_k(M) = \max_{W \in \W{n}{k}} \SM{\transp{W}M}.

The definition of $L$:

> L(M) = \max_{v \in \{-1, +1\}^n} \Man{vM}.

Lemma III.4 and the question:

> L_k(M) \le kL(M)

> It is an open question whether Lemma~\ref{LkkL} is tight or not.

The conjecture:

> Note that in the particular case of $k=2$ the matrix $M^{(k)}$ is the CHSH expression~\cite{chsh69}, in which case $L(M^{(2)})=2$ and $L_2(M^{(2)})=4$. Hence, for $k=2$ the upper bound in Lemma~\ref{LkkL} is tight. We conjecture that the bound is not tight for greater values of $k$.

## Verified locator

Source: https://arxiv.org/abs/2211.17185v2
- URL: https://arxiv.org/abs/2211.17185v2 (source `certification_qubits_v2.tex`, md5 `728b314751930b8afc32fe1ad74cdc79`):
  - notation, l. 461–465;
  - the definition of $L_k$, l. 467–475;
  - the definition of $L$, l. 520;
  - Lemma III.4, l. 561–565;
  - the question, l. 584;
  - the conjecture, l. 608.
- DOI: 10.1038/s41598-023-39529-0 (https://doi.org/10.1038/s41598-023-39529-0).
