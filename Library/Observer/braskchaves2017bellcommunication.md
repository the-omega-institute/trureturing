---
bibkey: braskchaves2017bellcommunication
authors: Jonatan Bohr Brask and Rafael Chaves
year: 2017
title: "Bell scenarios with communication"
doi: 10.1088/1751-8121/aa5840
url: "https://arxiv.org/abs/1607.08182v1"
claim: "In a bipartite Bell scenario where Alice's output may influence Bob's output (causal outcome-dependent models), the chained Bell inequality with Alice's outputs relabelled for every second input is valid for 3, 5, 7 and 9 inputs by vertex enumeration, is violated for even numbers of inputs up to 8, and is conjectured to hold for every odd number of inputs."
strata_touched:
  - D5/S3/Quantum/Contextuality/OutcomeCommunicationChainedInequality
license: citation-only
triage: anchor
---

# Brask and Chaves, Bell scenarios with communication

J. B. Brask and R. Chaves, J. Phys. A: Math. Theor. 50(9), 094001 (2017); arXiv:1607.08182v1. Quotations are from the v1 TeX source.

In a causal outcome-dependent (COD) model the output of one party directly influences the output of the other, so the behaviour has the form
$$p(a,b\mid x,y)=\sum_\lambda p(\lambda)\,p(a\mid x,\lambda)\,p(b\mid a,y,\lambda).$$
For the chained Bell inequality in the bracket notation $[a_x-b_y]=\sum_{j=0}^1j\,p(a-b=j \bmod 2\mid x,y)$, $a,b\in\{0,1\}$, $x,y\in\{1,\dots,n\}$, the paper enumerates the vertices of the COD polytope and reports:

> For even numbers of inputs (up to 8), we find that all symmetries can be violated. However, for 3,5,7, and 9 inputs, we find that the following inequality can be made valid for the COD model
> $$[a_1-b_1]+[b_1-a_2]+[a_2-b_2]+\cdots+[a_n-b_n]+[b_n-a_1-1]\geq 1 .$$
> [...] For the inequality to hold for the COD model, Alice's outputs must be relabelled for every second input. That is $a=0 \leftrightarrow a=1$ for even $x$. With this relabelling, we conjecture that (25) holds for any odd number of inputs.

## Verified locator

Source: https://arxiv.org/abs/1607.08182v1
- DOI: https://doi.org/10.1088/1751-8121/aa5840 (Journal of Physics A: Mathematical and Theoretical 50(9), 094001; title, authors, journal, volume, issue and article number from Crossref).
- URL: https://arxiv.org/abs/1607.08182v1. The e-print member `Bell_comm_arXiv_v1.tex` has 534 lines and md5 `e207a0023fa9c95a83583eef1d7d0158`. Locations:
  - the COD model, Eq. (7), l. 150–155;
  - the vertex enumeration, the inequality (25), the bracket notation, the relabelling and the conjecture, l. 317–325.
