---
bibkey: hasheminejadramazi2023equilibration
authors: Nazanin Hasheminejad; Pouria Ramazi
year: 2023
title: "Equilibration of Coordinating Imitation and Best-Response Dynamics"
doi: 10.1109/LCSYS.2023.3292049
url: https://arxiv.org/abs/2306.03243v3
claim: "The paper studies networks of agents who play two-strategy coordination games with their neighbours and update asynchronously, each either imitating its highest-earning neighbour or best-responding; it proves that linear graphs, rings, starlike networks under a condition on the branching agent, and sparse trees equilibrate under every persistent activation sequence, and leaves open whether dense trees or general graphs equilibrate under every activation sequence."
strata_touched:
  - D5/S3/ConceptDynamics/DecisionValue/MixedImitationBestResponseCycle
license: citation-only
triage: anchor
---

# Hasheminejad and Ramazi, equilibration of mixed imitation and best-response dynamics

N. Hasheminejad and P. Ramazi, arXiv:2306.03243v3 [math.DS] (29 June 2023; v1 5 June 2023); IEEE Control Systems Letters 7 (2023) 3078–3083. Quotations are from the v3 TeX source, with macros expanded and equation references replaced by bracketed descriptions.

The model (Section 2): agent $i$ has neighbours $\mathcal N_i\subseteq\mathcal N\setminus\{i\}$ and payoff matrix $\pi^i=\begin{bmatrix}R_i&S_i\\T_i&P_i\end{bmatrix}$ with $\min\{R_i,P_i\}>\max\{T_i,S_i\}$, and earns $u_i(x)=\sum_{j\in\mathcal N_i}\pi^i_{x_i,x_j}$. At each time one agent is active. An imitator updates to

> $x_i(t+1) = x_k(t), \qquad k=\arg\max_{j\in\mathcal N_i} u_j(x(t))$,

a best-responder to $\arg\max_{X\in\{A,B\}}u_i(x_{i=X}(t))$, and

> In the case where both strategies $A$ and $B$ maximize the utilities in [the two update rules], agent $i$ does not switch strategies, i.e., $x_i(t+1) = x_i(t)$.

A state is an equilibrium if under every activation sequence it stays fixed, and activation sequences are persistent: each agent becomes active infinitely many times.

The questions (abstract; Section 2; Conclusion):

> It is therefore, unknown, whether a potential function also exists for mixed populations or if there actually exists a counter example where an activation sequence prevents equilibration.

> However, it remains open whether the dynamics equilibrate under an arbitrary persistent activation sequence.

> Whether dense trees or general graphs equilibrate under every activation sequence remains an open problem.

## Verified locator

Source: https://arxiv.org/abs/2306.03243v3
- DOI: https://doi.org/10.1109/LCSYS.2023.3292049 (IEEE Control Systems Letters 7 (2023) 3078–3083; title, volume and pages from Crossref).
- URL: https://arxiv.org/abs/2306.03243v3 (the e-print is a gzipped tar archive; member `main.tex`, 791 lines, md5 `d6a8538afcd8dabd0bfc9743b289fb62`):
  - the abstract question, l. 71;
  - the network, payoffs and utilities, l. 134–148;
  - the update rules and the no-switch convention, l. 149–167;
  - equilibrium and persistence, l. 206–218;
  - the open question for arbitrary persistent sequences, l. 225;
  - the concluding open problem, l. 668.
- The author list and the arXiv version dates are from the arXiv metadata; the primary category is math.DS.
