---
bibkey: peltomaki2020abelianperiods
authors: J. Peltomäki
year: 2020
title: "Abelian periods of factors of Sturmian words"
doi: 10.1016/j.jnt.2020.04.007
url: https://arxiv.org/abs/1905.06138
claim: "Let $\\alpha = [0; \\overline{2}]$. The abelian period set of a Sturmian word of slope $\\alpha$ is $\\mathcal{Q}^+_\\alpha \\cup \\mathcal{M}_\\alpha$."
strata_touched:
  - D5/S1/Words/Mechanical/SilverSlopeAbelianPeriods
license: citation-only
triage: anchor
---

# Abelian periods of factors of Sturmian words

J. Peltomäki, *Abelian periods of factors of Sturmian words*, Journal of Number Theory 214 (2020), 251–285, DOI [10.1016/j.jnt.2020.04.007](https://doi.org/10.1016/j.jnt.2020.04.007), arXiv:1905.06138v3.

The paper's Conjecture on page 283, line 1722, states verbatim:

> Let $\alpha = [0; \overline{2}]$. The abelian period set of a Sturmian word of slope $\alpha$ is $\mathcal{Q}^+_\alpha \cup \mathcal{M}_\alpha$.

The paper defines the abelian period set as the set of minimum abelian periods of nonempty factors. It defines $\mathcal{Q}^+_\alpha$ as the denominators of convergents and semiconvergents and $\mathcal{M}_\alpha = \{tq_k : k \geq 0, 1 \leq t \leq a_{k+1}\}$. For the silver slope, the candidate set is $\{q_k\} \cup \{2q_k\} \cup \{q_k+q_{k-1}: k\geq1\}$ with $q_0=1$, $q_1=2$, and $q_{k+1}=2q_k+q_{k-1}$.

The source states the conjecture after reporting computer experiments. The Lean theorem proves the equality: explicit Pell-phase constructions realise all three candidate families, and singular-window packing combined with approximation gaps excludes every noncandidate minimum period. The argument here is specific to the silver slope; the analogous question for constant partial quotients greater than two remains open.

## Verified locator

DOI: https://doi.org/10.1016/j.jnt.2020.04.007

Source: https://arxiv.org/abs/1905.06138

## Abelian definitions

The source states (arXiv v3, p. 7):

> If $\mathcal{P}$ and $\mathcal{Q}$ are two Parikh vectors and $\mathcal{P}$ is componentwise less than or equal to $\mathcal{Q}$ but is not equal to $\mathcal{Q}$, then we say that $\mathcal{P}$ is contained in $\mathcal{Q}$.

Definition 2.4 states (arXiv v3, p. 8):

> An abelian decomposition of a word $w$ is a factorization $w = u_0 u_1 \dotsm u_{n-1} u_n$ such that $n \geq 2$, the words $u_1$, $\ldots$, $u_{n-1}$ have a common Parikh vector $\mathcal{P}$ (i.e., they are abelian equivalent), and the Parikh vectors of $u_0$ and $u_n$ are contained in $\mathcal{P}$.

> The common length $m$ of the words $u_1$, $\ldots$, $u_{n-1}$ is called an abelian period of $w$. The minimum abelian period (i.e., the shortest) of $w$ is denoted by $\mu_w$.

The encoding uses Boolean letters, natural block lengths, a nonempty block list, and proper coordinatewise containment for both ends.
