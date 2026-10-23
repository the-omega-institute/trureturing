---
bibkey: bernards2023nonlocalitydepth
authors: F. Bernards; O. Gühne
year: 2023
title: "Bell inequalities for nonlocality depth"
doi: 10.1103/PhysRevA.107.022412
url: https://arxiv.org/abs/2205.04250v2
claim: "For (k,m) models with m > 2, the classical bound F_n <= n 2^(n-2) is conjectured and proving it or finding a counterexample remains open."
strata_touched:
  - D5/S3/QuantumBounds/HybridMerminDepthBound
  - D5/S3/QuantumBounds/NonlocalityDepthQuantumBound
license: citation-only
triage: anchor
---

# Bell inequalities for nonlocality depth

F. Bernards and O. Gühne, *Bell inequalities for nonlocality depth*,
Phys. Rev. A 107, 022412 (2023), arXiv:2205.04250v2, DOI
10.1103/PhysRevA.107.022412.

Section III.F, Eq. (28), PDF p. 5, displays

> $F_n = \sum_{\ell=1}^n (-1)^{1+\lceil\ell/2\rceil} \ell (1\ldots1\,2\ldots2) \leq n 2^{n-2}$, (28)

and states that the bound can be achieved in any $(k,m)$ model with $k,m>1$.
Section V, PDF p. 8, states verbatim:

> For $(k, m)$ models with $m > 2$, we have a conjecture for the classical bound. Proving this bound or finding a counterexample remains an open problem.

Section II, PDF p. 2, states verbatim:

> Every cell c_i of the partition is considered as one system. The measurement settings are all combinations of measurement settings that apply to each subsystem within a cell. However, no restrictions apply to the correlations between subsystems within a cell, since the cell is regarded as one system. In particular, this allows for signaling to take place between the parties within one cell.

Section II, PDF p. 3, states:

> where ’party permutations’ only includes permutations that yield different terms.

The hybrid model treats each cell as one system and permits signaling inside a cell;
its convex-hull description means a linear functional reaches its maximum at a
deterministic point. The correlator brackets sum over distinct party permutations,
and the functional is symmetric under party permutations, so the cell assignment
does not change the value. The Lean encoding uses Boolean setting strings, integer
unit responses, and the displayed weight and sign $(-1)^{1+\lceil h/2\rceil}$.
The sign is evaluated by natural-number division as $(-1)^{1+\lfloor(h+1)/2\rfloor}$.

## Verified locator

- DOI: https://doi.org/10.1103/PhysRevA.107.022412
- URL: https://arxiv.org/abs/2205.04250v2

## Quantum source statement

Section III.F, PDF p. 5, Eq. (28), displays:

> $F_n = \sum_{\ell=1}^n (-1)^{1+\lceil\ell/2\rceil} \ell (1\ldots1\,2\ldots2) \leq n 2^{n-2}$, (28)

On the same page, Eq. (29) states verbatim:

> In the following, we discuss numerical findings concerning the Bell inequalities F_n for n ≤ 8 parties. We find, that the quantum bound of the inequalities is F_n = √2 n 2^{n−2} (29) up to numerical precision, which is achieved by choosing A₁ = B₁ = … = σ_x and A₂ = B₂ = … = σ_z

The quantum statement reported here is numerical for at most eight parties.
`NonlocalityDepthQuantumBound.result` proves the exact maximum for every n ≥ 3,
all finite local dimensions, Hermitian binary observables and positive trace-one
states. The entrywise tensor product, the Hamming weight and the existing integer
phase encode the distinct-party-permutation sum of Eq. (28). The proof uses the
all-party shifted operator estimate and a phase-adjusted GHZ state with X/Y settings.
