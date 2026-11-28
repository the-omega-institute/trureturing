---
bibkey: ariasnoguerales2026riskca
authors: María Teresa Arias Noguerales
year: 2026
title: "Territorial Conflict as a Cellular Automaton: Frozen Domains and Active Fronts in a Risk-Derived Local Rule"
doi: 10.48550/arXiv.2611.34784
url: https://arxiv.org/abs/2611.34784v1
claim: "The repository proves noninjectivity of the deterministic synchronous local step on the full legal carrier of every finite complete simple graph with at least two vertices, at least two available owners, capacity M ≥ 3, zero growth, threshold M − 1, every fixed priority permutation, either fortification setting, and real 1 < ρ < 2. The fixed-image collision holds for every real ρ ≥ 1 under the same remaining hypotheses."
strata_touched:
  - D5/S3/StatisticalMechanics/CellularAutomata/RiskCAEndpoint
license: citation-only
triage: anchor
---

# The highest active threshold in the RiskCA model

Definition 2 on printed p. 3 uses the full product of owner labels and positive capped unit counts, including homogeneous configurations. Section 3.2 on pp. 4–5 and Algorithm 1 on p. 30 specify the local step. Proposition 2 on p. 6 leaves injectivity open at zero growth and threshold one below the capacity in the band $1 < \rho < 2$. Its residual case covers disabled fortification or complete graphs. The repository settles the complete-board branch. The branch for connected incomplete boards with fortification disabled remains open in this formalization. [Versioned preprint](https://arxiv.org/pdf/2611.34784v1)

On a complete graph select distinct cells $u,v$. Give $u$ the cap $M$, give every other cell one unit, and assign a common owner to all cells except $v$. The unique request goes from $u$ to $v$. Its accepted force is $M-1$ and the defence is one. For $\rho\ge1$ the attacker wins and $\lceil 1/\rho\rceil=1$, so the winner leaves $M-2$ units at $v$. This image has a common owner, one unit at all other cells, and is fixed. The two inputs differ at $u$. The registered noninjectivity theorem uses the paper's band $1 < \rho < 2$. [Registered statement](https://github.com/the-omega-institute/trureturing/issues/35259)

The indexed update and selected supporting proofs use the author's Lean source. The MIT notice is carried in the Lean module. [Pinned source](https://github.com/MaTeArNog/RiskAutomata/tree/67bb577bd35855cf605e4457ad8795ec0e923991/lean/RiskCA) · [MIT license](https://github.com/MaTeArNog/RiskAutomata/blob/67bb577bd35855cf605e4457ad8795ec0e923991/LICENSE)
