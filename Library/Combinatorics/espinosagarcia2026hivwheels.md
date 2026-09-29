---
bibkey: espinosagarcia2026hivwheels
authors: Manuel A. Espinosa-García, Ana Paulina Figueroa, Julián A. Fresán-Figueroa, Gerardo L. Maldonado, L. Ariadna Sánchez-Solís
year: 2026
title: 'Extinction thresholds in a graph-based model of HIV infection dynamics'
doi: 10.48550/arXiv.2608.00340
url: https://arxiv.org/abs/2608.00340v1
claim: "The paper studies Mukwembi's cellular-automaton model of HIV infection on graphs, defines extinction sets and the thresholds hiv(G) and HIV(G), determines them for several graph families, and conjectures (Conjecture 1) from computations that the extinction set of the wheel W_n is {3} together with all R >= n - 1 for even n >= 12 and {4} together with all R >= n - 1 for odd n >= 17."
strata_touched:
  - D5/S3/Combinatorics/WheelHivExtinctionRefutation
license: citation-only
triage: anchor
---

# Extinction thresholds in a graph-based model of HIV infection dynamics

The paper works with Mukwembi's graph model of HIV infection. A state of a
graph `G` gives each vertex one of the values `0` (healthy), `1` (infected)
and `2` (dead); an admissible initial state uses only `0` and `1`. With
`d_{t,I}(v)` the number of infected neighbours of `v` at time `t` and a
positive replacement parameter `R`, a healthy vertex becomes infected when
`d_{t,I}(v) ≥ 1`, an infected vertex dies, and a dead vertex is replaced by an
infected one when `d_{t,I}(v) ≥ R` and by a healthy one otherwise. The
extinction set `𝓔(G)` collects the `R` for which every admissible initial
state reaches the all-healthy state; `hiv(G) = min 𝓔(G)` and `HIV(G)` is one
more than the largest `R` outside `𝓔(G)`.

For the wheels `W_n = K₁ ∨ C_{n−1}` the paper reports an exhaustive
computation for `4 ≤ n ≤ 10` and, for `11 ≤ n ≤ 26`, computations described
as experimental evidence rather than an exhaustive determination. Its table
and Conjecture 1 state:

> The extinction sets of the wheel graphs satisfy $\mathcal{E}(W_n) = \{3\}\cup\{R\in\mathbb{Z^+}:R\geq n-1\}$ for every even $n\geq12$, and $\mathcal{E}(W_n) = \{4\}\cup\{R\in\mathbb{Z^+}:R\geq n-1\}$ for every odd $n\geq17$.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2608.00340
- URL: https://arxiv.org/abs/2608.00340v1
- Version and location: arXiv:2608.00340v1 (2026-07-31), the only version listed by the arXiv API on 2026-09-26; source file `main.tex`: Section 2 for the rules and the extinction sets, Section 4 ("Results for families of graphs") for the wheel table and Conjecture 1, the only `conjecture` environment of the paper.
