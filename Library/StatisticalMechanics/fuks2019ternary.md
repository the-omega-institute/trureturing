---
bibkey: fuks2019ternary
authors: Henryk Fukś; Roman Procyk
year: 2019
title: "Explorations of Ternary Cellular Automata and Ternary Density Classification Problems"
doi: 10.5506/APhysPolBSupp.12.75
url: https://arxiv.org/abs/2002.08924v1
claim: "Ternary nearest-neighbour cellular automata act on periodic configurations by (F(x))_i = f(x_{i-1}, x_i, x_{i+1}) with indices modulo L, and a rule is named by the Wolfram number with coefficients a_{9x_0+3x_1+x_2} = f(x_0,x_1,x_2). Conjecture 1 asserts that for F = 6478767664173 and G = 7580606234490, every finite configuration of length L containing at least one zero, with density rho = (1/2L) sum x_i, satisfies G^L F^L(x) = 0^L, 1^L or 2^L according as rho lies in [0, 2/3), (2/3, 3/4) or (3/4, 1)."
strata_touched:
  - D5/S3/StatisticalMechanics/CellularAutomata/TernaryDensityClassificationRefutation
license: citation-only
triage: anchor
---

# Explorations of Ternary Cellular Automata and Ternary Density Classification Problems

Henryk Fukś and Roman Procyk, arXiv:2002.08924v1 [nlin.CG] (2020); Acta
Physica Polonica B Proceedings Supplement 12(1) (2019) 75–89. Quotations
are from the arXiv source.

The setting (Section 2):

> We will impose periodic boundary conditions on configurations $\mathbf{x} \in S$, so that for $\mathbf{x}=(x_0, x_1, \ldots x_{L-1})$, the index $i$ in $x_i$ is to be always taken modulo $L$, i.e., $i\in \mathbb{Z}/L$.

> $(F(\mathbf{x}))_i=f(x_{i-1}, x_i, x_{i+1})$ for all $i\in \mathbb{Z}/L$.

The rule tables are indexed as $a_{9x_0+3x_1+x_2}=f(x_0,x_1,x_2)$, and a
rule is named by its Wolfram number $\sum_j a_j 3^j$.

Conjecture 1:

> Let $F$ be the ternary nearest-neighbour rule with Wolfram number 6478767664173, and $G$ be the rule with Wolfram number 7580606234490. For any finite ternary string $\mathbf{x}$ of length $L$, containing at least one zero, let $\displaystyle \rho=\frac{1}{2L}\sum_{i=0}^{L-1} x_i$. Then $G^LF^L(\mathbf{x})=0^L$ if $\rho(\mathbf{x}) \in [0, 2/3)$, $G^LF^L(\mathbf{x})=1^L$ if $\rho(\mathbf{x}) \in (2/3, 3/4)$, $G^LF^L(\mathbf{x})=2^L$ if $\rho(\mathbf{x}) \in (3/4, 1)$.

The authors then write:

> Configurations which do not satisfy this property can be misclassified - for example, $1^L$ has density $1/2$, thus should produce $0^L$ in the end, yet $1^L$ is a fixed point of both rules 6478767664173 and 7580606234490.

> We performed extensive numerical experiments to verify the above conjecture, and it appears to be valid.

and close the sketch of a proof with:

> Our statement about rules 6478767664173 and 7580606234490, therefore, must remain a conjecture for now.

The abstract of both versions states: "Finally we show an example of a pair
of rules which solve non-symmetric interval-wise DCP for initial
configurations containing at least one zero." In the arXiv text, the
paragraph after the sketch names the second rule $G$ with the number
6478767664173 of $F$; the conjecture and the binary projections of $G$
listed there (192, 232, 232) identify $G$ as 7580606234490.

## Verified locator

- DOI: https://doi.org/10.5506/APhysPolBSupp.12.75 (Conjecture 1 of the
  journal version; the published text was read by a scout subagent, and the
  Crossref record gives the title, authors, volume 12, issue 1 and first page
  75).
- URL: https://arxiv.org/abs/2002.08924v1 (source `hfrprevised.tex` retrieved
  2026-10-01): the periodic configurations and the global map (Section 2),
  the coefficient indexing of the rule tables, Conjecture 1, and the remarks
  and the sketch of a proof that follow it.
