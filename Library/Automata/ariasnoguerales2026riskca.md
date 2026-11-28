---
bibkey: ariasnoguerales2026riskca
authors: María Teresa Arias Noguerales
year: 2026
title: "Territorial Conflict as a Cellular Automaton: Frozen Domains and Active Fronts in a Risk-Derived Local Rule"
doi: 10.48550/arXiv.2611.34784
url: https://arxiv.org/abs/2611.34784v1
claim: "At zero growth and the highest active threshold, the deterministic local step has a collision on every complete board with at least two cells."
strata_touched:
  - D5/S3/StatisticalMechanics/CellularAutomata/RiskCAEndpoint
license: citation-only
triage: anchor
---

# The highest active threshold in the RiskCA model

Definition 2 on printed p. 3 uses the full product of owner labels and positive capped unit counts, including homogeneous configurations. Section 3.2 on pp. 4–5 and Algorithm 1 on p. 30 specify the local step. Proposition 2 on p. 6 leaves injectivity open at zero growth and threshold one below the capacity in the band $1 < \rho < 2$. Its residual case covers disabled fortification or complete graphs. [Versioned preprint](https://arxiv.org/pdf/2611.34784v1)

On a complete graph select distinct cells $u,v$. Give $u$ the cap $M$, give every other cell one unit, and assign a common owner to all cells except $v$. The unique request goes from $u$ to $v$. Its accepted force is $M-1$, its defence is one, and the winner leaves $M-2$ units at $v$. This image has a common owner, one unit at all other cells, and is fixed. The two inputs differ at $u$. The registered result uses $M \ge 3$ and at least two available owner labels, and applies to every fixed priority permutation and either fortification setting. [Registered statement](https://github.com/the-omega-institute/trureturing/issues/35259)

The indexed update and selected supporting proofs use the author's Lean source. The MIT notice is carried in the Lean module. [Pinned source](https://github.com/MaTeArNog/RiskAutomata/tree/67bb577bd35855cf605e4457ad8795ec0e923991/lean/RiskCA) · [MIT license](https://github.com/MaTeArNog/RiskAutomata/blob/67bb577bd35855cf605e4457ad8795ec0e923991/LICENSE)
