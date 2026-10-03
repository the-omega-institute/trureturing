---
bibkey: araoka2026integrable
authors: Aoi Araoka; Tetsuji Tokihiro
year: 2026
title: "Integrable Cellular Automata on Finite Fields of Order 2^n"
doi: 10.1007/s11040-026-09569-9
url: https://arxiv.org/abs/2602.17148v1
claim: "For a map f of a finite field of characteristic 2, the R-matrix R(x,y) = (y + f(x+y), x - f(x+y)) satisfies the Yang-Baxter equation exactly when f(x) + f(x + f(y)) = f(x + f(y + f(x))); the cellular automaton that runs R along N cells with the helical boundary condition b(t+1) = y_N(t) is conjectured, for bijective f, to have period dividing the order of the field (proved in the paper for orders 4 and 8)."
strata_touched:
  - D5/S3/StatisticalMechanics/CellularAutomata/YangBaxterAutomatonPeriod
license: citation-only
triage: anchor
---

# Integrable Cellular Automata on Finite Fields of Order 2^n

A. Araoka and T. Tokihiro, arXiv:2602.17148 (v1 2026-02); Math. Phys. Anal.
Geom. 29, 30 (2026). Subject: nlin.SI.

The paper builds R-matrices on a finite field from a single map `f`,
`R: (x, y) ↦ (y + f(x + y), x − f(x + y))`, shows that in characteristic 2 the
Yang–Baxter equation reduces to `f(x) + f(x + f(y)) = f(x + f(y + f(x)))`, and
counts the bijective solutions (16, 736 and 269,056 for orders 4, 8 and 16). It
constructs a cellular automaton by running `R` along a row,
`R: (x_i(t), y_{i−1}(t)) ↦ (x_i(t+1), y_i(t))` with `y_0 = b(t)`, and the helical
boundary condition `b(t+1) = y_N(t)`. It states:

> Conjecture. The cellular automaton thus constructed over a finite field of
> order 2^n has a period that is a divisor of the order of the field.

and proves it for orders 4 and 8.

## Verified locator

- DOI: https://doi.org/10.1007/s11040-026-09569-9 (publication metadata from
  the Springer page; the journal text was not read).
- URL: https://arxiv.org/abs/2602.17148v1 (source retrieved 2026-09-30):
  `sn-article_tokihiro.tex`, the R-matrix (eq. `eq:finiteYB`), the reduced
  equation (eq. `FYB_eq`), the construction of the automaton (§3.1) and the
  conjecture (§3.2).
