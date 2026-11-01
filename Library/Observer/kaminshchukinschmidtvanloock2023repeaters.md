---
bibkey: kaminshchukinschmidtvanloock2023repeaters
authors: Lars Kamin; Evgeny Shchukin; Frank Schmidt; Peter van Loock
year: 2023
title: "Exact rate analysis for quantum repeaters with imperfect memories and entanglement swapping as soon as possible"
doi: 10.1103/PhysRevResearch.5.023086
url: "https://arxiv.org/abs/2203.10318v1"
claim: "The paper computes exact secret-key rates of linear quantum repeaters with up to eight segments, memory dephasing and parallel entanglement distribution, defines the dephasing of the scheme that always swaps an earliest pair of adjacent segments and of the globally optimal swapping order, verifies that they coincide for up to eight segments, and conjectures that they coincide for every number of segments."
strata_touched:
  - D5/S3/Quantum/Optimization/SwapEarliestDephasingOptimality
license: citation-only
triage: anchor
---

# Kamin, Shchukin, Schmidt and van Loock, Exact rate analysis for quantum repeaters with imperfect memories and entanglement swapping as soon as possible

L. Kamin, E. Shchukin, F. Schmidt and P. van Loock, Physical Review Research 5(2) (2023) 023086, DOI 10.1103/PhysRevResearch.5.023086; arXiv:2203.10318v1. Quotations are from the arXiv v1 TeX source.

Segment $i$ of an $n$-segment repeater is ready after $N_i$ time units; swapping adjacent segments $i,i+1$ adds dephasing $|N_i-N_{i+1}|$ and leaves a combined segment ready at $\max(N_i,N_{i+1})$. The scheme that always swaps an earliest pair (an adjacent pair minimizing $\max(N_i,N_{i+1})$, ties chosen arbitrarily) has dephasing $\tilde D_n$; the optimal swapping order has dephasing $D^\star_n$, the minimum over the first swap of its cost plus $D^\star_{n-1}$ of the shortened list, with $D^\star_2(N_1,N_2)=|N_1-N_2|$. After verifying $\tilde D_n=D^\star_n$ for $n\le8$ the paper states:

> Our conjecture is that the statement is valid for all $n\geqslant2$, but in this work we consider repeaters with up to eight segments only, and for such $n$ we have verified this statement directly.

## Verified locator

Source: https://arxiv.org/abs/2203.10318v1
- DOI: https://doi.org/10.1103/PhysRevResearch.5.023086 (journal version; title, authors, journal, volume, issue and article number from Crossref; the journal text was not read).
- URL: https://arxiv.org/abs/2203.10318v1. The e-print member `skr.tex` has 3889 lines and md5 `491326023d580d1ec0d0d5d5f42f267d`. Locations:
  - the greedy scheme $\tilde D_n$, l. 1033–1044;
  - the optimal scheme $D^\star_n$ and its base case, l. 1053–1064;
  - the verification for $n\le8$ and the conjecture, l. 1066–1083.
