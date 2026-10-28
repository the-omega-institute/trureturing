---
bibkey: chenetal2024bipartitewalkhamiltonians
authors: Qiuting Chen; Chris Godsil; Mariia Sobchuk; Hanmeng Zhan
year: 2024
title: "Hamiltonians of bipartite walks"
doi: 10.37236/12040
url: https://arxiv.org/abs/2207.01673v1
claim: "The paper studies bipartite discrete quantum walks with transition matrix U=(2P-I)(2Q-I) built from the two vertex-class partitions of the edges of a bipartite graph, and in its open questions displays the transition matrix of a seven-edge example with perfect state transfer from e1 to e6 at step 1 and states the suspicion that there is no perfect state transfer from e6 to e1."
strata_touched:
  - D5/S3/Quantum/Walks/BipartiteWalkReverseStateTransfer
license: citation-only
triage: anchor
---

# Hamiltonians of bipartite walks

Q. Chen, C. Godsil, M. Sobchuk and H. Zhan, arXiv:2207.01673v1; The Electronic Journal of Combinatorics 31(4) (2024), P4.10. Quotations are from the v1 TeX source.

The walk (Section 2):

> If the initial state is $z$, then after $k$ steps of the walk, the state is $U^kz$.

> Hence we can define a unitary operator $U$ by
> \[
> 	U := (2P-I)(2Q-I).
> \]
> This the transition matrix of the bipartite walk on $G$.

The open question (Section "Open questions"), after the displayed $7\times7$ transition matrix of the walk on the graph of Figure `not return pst graph`:

> State $e_i$ is the characteristic vector of $i$. It is easy to see that there is perfect state transfer from state $e_1$ to $e_6$ at step $k=1$. But up to $k=300000$ steps, there is no perfect state transfer observed from $e_6$ to $e_1$. We suspect that there is no perfect state transfer from $e_6$ to $e_1$.

The displayed matrix has entry $(3,5)$ equal to $\tfrac13$; the product $(2P-I)(2Q-I)$ formed from the displayed projections $P$ and $Q$ has $-\tfrac13$ there, and every other entry agrees.

## Verified locator

Source: https://arxiv.org/abs/2207.01673v1
- URL: https://arxiv.org/abs/2207.01673v1 (source `Hamiltonian_7.tex`, md5 `2e3f9a1a91cb695794df49b0123dfc37`, 1587 lines):
  - the walk and $U=(2P-I)(2Q-I)$, l. 135–163;
  - the graph of Figure `not return pst graph`, l. 237–294;
  - its projections $\hat P_0$, $\hat P_1$, $P$ and $Q$, l. 296–339, and its displayed transition matrix, l. 340–351;
  - the open question on reverse perfect state transfer, l. 1276–1290.
- DOI: 10.37236/12040 (https://doi.org/10.37236/12040; Crossref lists The Electronic Journal of Combinatorics, volume 31, issue 4, article P4.10, published 4 October 2024).
