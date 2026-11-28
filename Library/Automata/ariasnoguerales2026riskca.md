---
bibkey: ariasnoguerales2026riskca
authors: María Teresa Arias Noguerales
year: 2026
title: "Territorial Conflict as a Cellular Automaton: Frozen Domains and Active Fronts in a Risk-Derived Local Rule"
doi: 10.48550/arXiv.2611.34784
url: https://arxiv.org/abs/2611.34784v1
claim: "Proposition 2 leaves injectivity open at the highest active threshold. Take any finite complete simple graph with at least two vertices, P ≥ 2 available owner labels and capacity M = Nmax ≥ 3. Fix any priority permutation and either fortification setting. For any real 1 < ρ < 2, is the synchronous deterministic local step injective at zero growth and threshold θ = M − 1? The carrier is the full product over the vertices of the P owner labels and unit counts 1 through M, with pointwise equality."
strata_touched:
  - D5/S3/StatisticalMechanics/CellularAutomata/RiskCAEndpoint
license: citation-only
triage: anchor
---

# The highest active threshold in the RiskCA model

Definition 2 on printed p. 3 uses the full product of owner labels and positive capped unit counts, including homogeneous configurations. Section 3.2 on pp. 4–5 and Algorithm 1 on p. 30 specify the local step. Proposition 2 on p. 6 leaves injectivity open at zero growth and threshold one below the capacity in the band $1 < \rho < 2$. Its residual case covers disabled fortification or complete graphs. The repository settles the complete-board branch. The branch for connected incomplete boards with fortification disabled remains open in this formalization. [Versioned preprint](https://arxiv.org/pdf/2611.34784v1)

## Verified locator

DOI 10.48550/arXiv.2611.34784 identifies the preprint. The version cited here is arXiv v1. [Versioned abstract](https://arxiv.org/abs/2611.34784v1)

Definition 2 gives the carrier on printed p. 3. Section 3.2 on pp. 4–5 and Algorithm 1 on p. 30 give the step. Proposition 2 on p. 6 states the residual case. Proposition 4(a) on p. 7 gives the zero-growth homogeneous fixed point. [Definition 2](https://arxiv.org/pdf/2611.34784v1#page=3) · [Proposition 2](https://arxiv.org/pdf/2611.34784v1#page=6) · [Proposition 4(a)](https://arxiv.org/pdf/2611.34784v1#page=7) · [Algorithm 1](https://arxiv.org/pdf/2611.34784v1#page=30)

## Complete-board collision

On a complete graph select distinct cells $u,v$. Give $u$ the cap $M$, give every other cell one unit, and assign a common owner to all cells except $v$. The unique request goes from $u$ to $v$. Its accepted force is $M-1$ and the defence is one. For $\rho\ge1$ the attacker wins and $\lceil 1/\rho\rceil=1$, so the winner leaves $M-2$ units at $v$. This image has a common owner, one unit at all other cells, and is fixed. The two inputs differ at $u$. The registered noninjectivity theorem uses the paper's band $1 < \rho < 2$. [Registered statement](https://github.com/the-omega-institute/trureturing/issues/35259)

The repository's stronger fixed-image theorem gives distinct configurations $X,Y$ with $\Phi(X)=Y=\Phi(Y)$ for every real $\rho\ge1$ under the same complete-board, carrier, priority, growth, threshold and fortification hypotheses. [Blueprint](../../Blueprint/D5/S3/StatisticalMechanics/CellularAutomata/RiskCAEndpoint.md)

The indexed update and selected supporting proofs use the author's Lean source. The MIT notice is carried in the Lean module. [Pinned source](https://github.com/MaTeArNog/RiskAutomata/tree/67bb577bd35855cf605e4457ad8795ec0e923991/lean/RiskCA) · [MIT license](https://github.com/MaTeArNog/RiskAutomata/blob/67bb577bd35855cf605e4457ad8795ec0e923991/LICENSE)
