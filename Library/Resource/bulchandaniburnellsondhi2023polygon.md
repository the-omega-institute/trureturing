---
bibkey: bulchandaniburnellsondhi2023polygon
authors: Vir B. Bulchandani, Fiona J. Burnell, S. L. Sondhi
year: 2023
title: "Playing nonlocal games with phases of quantum matter"
doi: 10.1103/PhysRevB.107.045412
url: https://arxiv.org/abs/2206.11252v2
claim: "The paper introduces the P-player polygon game, gives a perfect quantum strategy from the 2P-qubit cyclic cluster state, shows that odd P admits no perfect classical strategy, exhibits a classical strategy losing on F_{P-1} of the 2^P inputs, and conjectures that the resulting lower bound p_cl*(P) >= 1 - F_{P-1}/2^P on the classical winning probability is tight for odd P."
strata_touched:
  - D5/S3/QuantumBounds/PolygonGameClassicalValue
license: citation-only
triage: anchor
---

# Bulchandani–Burnell–Sondhi, playing nonlocal games with phases of quantum matter

## Verified locator

DOI: https://doi.org/10.1103/PhysRevB.107.045412 (Phys. Rev. B 107, 045412, published 12 January 2023).

Source: https://arxiv.org/abs/2206.11252v2

V. B. Bulchandani, F. J. Burnell and S. L. Sondhi, arXiv:2206.11252v2 (the latest version). Quotations are from the v2 TeX source, Section 4.1 ("The polygon games").

## Statement

Each of the $P$ players receives an input bit $x_i$ and outputs $(a_i,b_i,c_i)$ on input $0$ and $(d_i,b_i,e_i)$ on input $1$. The players win when each output triple has even parity, $\sum_i b_i$ is even, and, for every matching $M_r$ of the $P$-gon whose edges' endpoints are exactly the players with input $1$,
$$\sum_{(i,i+1)\in M_r} d_i+e_{i+1} + \sum_{(j-1,j),(j,j+1) \notin M_r} a_j \equiv r \pmod 2$$
(the cases $r=0,1,2$ are the source's Conditions 3–5). For even $P$ the classical value is $1$. For odd $P$ the source shows $p^*_{\mathrm{cl}}(P)\le 1-2^{-P}$, recalls $p^*_{\mathrm{cl}}(3)=7/8$, finds $p^*_{\mathrm{cl}}(5)=29/32$ by exhausting all $2^{20}$ deterministic strategies, gives a strategy that loses on $F_{P-1}$ inputs (the conditions of the matchings containing the edge $(P,1)$), and states:

> $p_{\mathrm{cl}}^*(P) \geq \frac{2^P - F_{P-1}}{2^P} = 1 - \frac{F_{P-1}}{2^P}, \quad P \,\mathrm{odd}.$ We conjecture that this bound is tight.

with Fibonacci numbers indexed so that $F_1=F_2=1$.

## Encoding and boundary

The repository defines deterministic strategies (the middle output may depend on the input bit), the matching input of the $P$-cycle, the winning predicate of the polygon game and the winning probability of a probability distribution over deterministic strategies under uniform inputs. It proves that for every odd $P\ge3$ every such distribution wins with probability at most $1-F_{P-1}/2^P$ and that the source's strategy attains it. The quantum value, the SPT-phase strategies, the even-$P$ value and the $N$-player inscribed polygon games are outside this conclusion.
