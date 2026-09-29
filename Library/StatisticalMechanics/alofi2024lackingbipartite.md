---
bibkey: alofi2024lackingbipartite
authors: Amal Alofi, Mark Dukes
year: 2024
title: "A note on the lacking polynomial of the complete bipartite graph"
doi: 10.1016/j.disc.2024.114323
url: https://arxiv.org/abs/2411.02667v1
claim: "For the stochastic sandpile model of Chan, Marckert and Selig, the paper characterises the stochastically recurrent states of K_{2,n} and K_{m,n} with n = 2, bounds n^(m-1) m^(n-1) <= |Sto(K_{m,n})| <= n^(m-1) m^n, and asks in Question 6 whether |Sto(K_{m,n})| is larger or smaller than n^(m-1) m^n / 2."
strata_touched:
  - D5/S3/StatisticalMechanics/Sandpiles/StochasticSandpileBipartiteHalf
license: citation-only
triage: anchor
---

# Alofi and Dukes, the lacking polynomial of the complete bipartite graph

In the stochastic sandpile model a stable configuration assigns to each
non-sink vertex `v` a number of grains `0 ≤ c(v) < d(v)`. An orientation `O`
of `G` is compatible with `c` when

> in_O(v) ≥ d(v) − c(v)

at every non-sink vertex (Definition 1, following Chan, Marckert and Selig),
and `Sto(G)` is the union over all orientations of the compatible stable
configurations (Theorem 2). On `K_{m,n}` the sink `v_0` lies in the part
`{v_0, …, v_{m−1}}`. From the spanning-tree count and the number of stable
configurations the paper records

> n^{m−1} m^{n−1} ≤ |Sto(K_{m,n})| ≤ n^{m−1} m^n

and asks:

> Question 6. Can it be determined whether or not the number of stochastically
> recurrent states dominates the set of stable states? I.e. can it be decided
> |Sto(K_{m,n})| ≶ n^{m−1} m^n / 2 ?

## Verified locator

- DOI: 10.1016/j.disc.2024.114323 (Crossref record retrieved 2026-09-27:
  Discrete Mathematics 348(2) (2025), article 114323; authors Alofi, Dukes).
- URL: https://arxiv.org/abs/2411.02667v1 (the only version listed by the arXiv
  API on 2026-09-27); source file `ssm_final.tex`: stable configurations
  (lines 158–162), Definition 1 `defcom` (lines 164–173), Theorem 2 `thcom`
  (lines 177–181), the graph `K_{m,n}` (lines 194–197), Example 5 (lines
  222–328), the bounds (lines 330–340) and Question 6 (lines 342–345).
