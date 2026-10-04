---
bibkey: fuks2023solvable
authors: Henryk Fukś
year: 2023
title: "Solvable Cellular Automata: Methods and Applications"
doi: 10.1007/978-3-031-38700-5
url: https://lie.ac.brocku.ca/~hfuks/solvableca.html
claim: "Appendix B lists explicit solutions [F^n(x)]_j of solvable elementary cellular automata for an arbitrary initial configuration x; for Rule 13 it gives [F_13^n(x)]_j = x_j + sum_{r=1}^{n} (-1)^r prod_{i=0}^{r} x_{j-i} + sum_{r=1}^{n} (-1)^{r+1} prod_{i=-1}^{r} xbar_{j-i} + x_{j+2} xbar_{j+1} xbar_j sum_{r=2}^{n} (-1)^r prod_{i=1}^{r} x_{j-i}, where xbar = 1 - x."
strata_touched:
  - D5/S3/StatisticalMechanics/CellularAutomata/Rule13OnCellCount
license: citation-only
triage: anchor
---

# Explicit solutions of elementary cellular automata

H. Fukś, *Solvable Cellular Automata: Methods and Applications*, Understanding
Complex Systems, Springer, Cham, 2023. Appendix B gives, for each solvable
minimal elementary rule, a closed formula for the state of cell `j` after `n`
steps from an arbitrary initial configuration `x`. The Rule 13 entry is

> [F_{13}^n(x)]_j = x_j + ∑_{r=1}^{n} (−1)^r ∏_{i=0}^{r} x_{j−i}
> + ∑_{r=1}^{n} (−1)^{r+1} ∏_{i=−1}^{r} x̄_{j−i}
> + x_{j+2} x̄_{j+1} x̄_j ∑_{r=2}^{n} (−1)^r ∏_{i=1}^{r} x_{j−i}.

Evaluating this formula agrees with direct simulation for 300 random initial
configurations of length at most 12 (cells around the support, `n ≤ 12`).
For the single ON seed (`x_0 = 1`, all other cells 0) the last term vanishes,
since each product `∏_{i=1}^{r} x_{j−i}` with `r ≥ 2` needs two ON cells, and
the formula gives the row pattern of `D5/S3/StatisticalMechanics/CellularAutomata/Rule13OnCellCount`:
row `2k` is ON exactly at the even `x` with `0 ≤ x ≤ 2k`, and row `2k + 1` is
OFF exactly at the odd `x` with `−1 ≤ x ≤ 2k + 1`; evaluating the formula
agrees with direct simulation on the cells `−n − 5, …, n + 5` for `n ≤ 40`.
Rule 79 is the black/white conjugate of Rule 13.

## Verified locator

- DOI: 10.1007/978-3-031-38700-5 (Crossref: *Solvable Cellular Automata*,
  Fukś, Springer Nature Switzerland, 2023, series Understanding Complex
  Systems).
- URL: https://lie.ac.brocku.ca/~hfuks/solvableca.html (the author's page
  reproducing the Appendix B formulas; the Rule 13 formula above was read
  there).
