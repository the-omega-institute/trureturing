---
bibkey: gu2023dissipationtimetradeoff
authors: Jie Gu
year: 2023
title: "Speed limit, dissipation bound, and dissipation-time trade-off in thermal relaxation processes"
doi: 10.1103/PhysRevE.108.L052103
url: https://arxiv.org/abs/2304.08752v2
claim: "The letter proves a speed limit for Markov jump processes with time-independent rates in terms of the infinity-Rényi divergence and the total rate, and conjectures, with numerical evidence, a divergence bound and a dissipation-time trade-off bound on the non-adiabatic entropy production obtained from two-state pseudo-coarse-grainings."
strata_touched:
  - D5/S3/StatisticalMechanics/PseudoCoarseGrainedTradeoffRefutation
license: citation-only
triage: anchor
---

# Speed limit, dissipation bound, and dissipation-time trade-off in thermal relaxation processes

J. Gu, arXiv:2304.08752v2 (31 October 2023); Phys. Rev. E 108(5) (2023), L052103. Quotations are from the v2 TeX source, with citation commands and equation labels omitted.

The dynamics:

> \begin{equation} \frac{\text{d} {p}_{m}}{\text{d} t}=\sum_{n} W_{mn} p_{n}, \end{equation} where \(p_m\) is the probability of state \(m\), \(W_{mn} (m\ne n)\) is the time-{independent} transition rate from state \(n\) to \(m\), and \(W_{mm} = -\sum_{n,n\ne m} W_{nm}\). For later use, we define the \emph{total rate} as \begin{equation} \mathcal{W} = \sum_{m \ne n} W_{mn} = -\mathrm{Tr} \mathbf{W}. \end{equation}

The non-adiabatic entropy production:

> \begin{equation} \Sigma_\text{na}  = D_1(\boldsymbol{p}^\text{(i)} \| \boldsymbol{p}^\text{(ss)})-D_1(\boldsymbol{p}^\text{(f)} \| \boldsymbol{p}^\text{(ss)}) , \end{equation} where \({D}_1(\boldsymbol{p} \|\boldsymbol{q}) = \sum_n p_n \ln(p_n/q_n)\) is the $1$-R\'enyi divergence between the two probability distributions.

The two-state steady state:

> $p_1^\text{(ss)} = p_1^\text{(i)} + \frac{p_1^\text{(f)}-p_1^\text{(i)}}{1-e^{-\mathcal{W} \tau}}$

The trade-off conjecture, Eq. (13):

> Let us state  the third main result: for $N$-state dynamics evolving from $\boldsymbol{p}^\text{(i)}$ to $\boldsymbol{p}^\text{(f)}$ during $\tau$ with an total rate $\mathcal{W}$, the conjecture is that the entropy production $\Sigma$ is bounded from below by (referred to as trade-off bound) \begin{equation} \Sigma_\text{na} \ge \Sigma_{\Omega_i}(\mathcal W \tau) \quad i =1,2,\ldots,S_N^{(2)}. \end{equation} Here , $\Sigma_{\Omega_i}(\mathcal W \tau)$ is the entropy production of two-state dynamics obtained from a pseudo-coarse-graining procedure as follows:  partition the set of $N$ states into two nonempty sets where the first set is denoted by $\Omega_i$, then we have the two endpoints $\boldsymbol{P}_{\Omega_i}^\text{(i)} = [\sum_{n\in {\Omega_i}}p_n^\text{(i)},1-\sum_{n\in {\Omega_i}}p_n^\text{(i)}]^\text{T}$ to $\boldsymbol{P}_{\Omega_i}^\text{(f)} = [\sum_{n\in {\Omega_i}}p_n^\text{(f)},1-\sum_{n\in {\Omega_i}}p_n^\text{(f)}]^\text{T}$. We then use Eq. \eqref{eq:p1} to find the steady state distribution, where $\mathcal{W}$ and $\tau$ of the original $N$-state dynamics are used. The entropy production of the two-state dynamics is obtained by substituting the steady state distribution into  \eqref{eq:na}.

The abstract describes the bound as conjectured: "we conjecture and provide extensive numerical evidence for an  information-theoretical bound on the non-adiabatic entropy production and a novel dissipation-time trade-off relation".

## Verified locator

Source: https://arxiv.org/abs/2304.08752v2
- URL: https://arxiv.org/abs/2304.08752v2 (the e-print is a tar archive; member `relaxation.tex`, md5 `73c406829510539d2db7d2bb969829fb`, 1476 lines):
  - the abstract, l. 83–85;
  - the master equation and the total rate, l. 162–172;
  - the non-adiabatic entropy production, l. 178–184;
  - the two-state steady state, Eq. `eq:p1`, l. 191–195;
  - the trade-off conjecture, Eq. `eq:newbound`, l. 327–336.
- DOI: 10.1103/PhysRevE.108.L052103 (https://doi.org/10.1103/PhysRevE.108.L052103; Crossref lists Physical Review E, volume 108, issue 5, article L052103, published 6 November 2023).
