---
bibkey: alcalaarroyo2025lazy
authors: Edgar Alcalá-Arroyo; Alonso Castillo-Ramirez
year: 2025
title: "On the order of lazy cellular automata"
doi: 10.1016/j.tcs.2026.115965
url: https://arxiv.org/abs/2510.14841v3
claim: "A cellular automaton over A^G is lazy when a local map on a neighborhood containing the identity returns the central value on every pattern except one, the unique active transition p. The paper bounds the order of a lazy cellular automaton in terms of the fibers of p, shows the bound is attained for quasi-constant p, and asks in Problem 2 whether the invertible and the lazy cellular automata generate the monoid CA(G, A) of all cellular automata."
strata_touched:
  - D5/S3/StatisticalMechanics/CellularAutomata/LazyInvertibleGeneration
license: citation-only
triage: anchor
---

# On the order of lazy cellular automata

E. Alcalá-Arroyo and A. Castillo-Ramirez, arXiv:2510.14841 (v1 2025-10-16,
v3 2026-02-26); Theoret. Comput. Sci. 1076 (2026) 115965. Subjects: cs.FL,
cross-listed to nlin.CG, math.DS and math.GR.

For a group `G` and an alphabet `A` with at least two symbols, a cellular
automaton `τ : A^G → A^G` has a finite neighborhood `S` and a local map
`μ : A^S → A` with `τ(x)(g) = μ((g · x)|_S)`, where `(g · x)(h) = x(hg)`. It is
lazy when `e ∈ S` and `μ(z) = z(e)` holds exactly for `z ≠ p`, for a single
pattern `p`. The paper bounds the order of a lazy automaton through the fibers
of `p`, proves the bound is attained for quasi-constant patterns, and states
two open problems. Problem 2 reads:

> If $\mathcal{L}(G,A)$ is the set of all lazy cellular automata over $A^G$,
> prove or disprove the following:
> $\text{CA}(G,A) = \langle \text{ICA}(G,A) \cup \mathcal{L}(G,A) \rangle$.

## Verified locator

- DOI: https://doi.org/10.1016/j.tcs.2026.115965 (journal reference from the
  arXiv record; the journal text was not read).
- URL: https://arxiv.org/abs/2510.14841v3 (source `Lazy_CA_ver_4.tex`
  retrieved 2026-10-01): the definition of cellular automata and of the shift
  action (§1), Definition 1 of lazy automata (§2), and Problem 2 (§4).
