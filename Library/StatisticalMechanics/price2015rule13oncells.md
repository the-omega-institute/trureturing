---
bibkey: price2015rule13oncells
authors: Robert Price
year: 2015
title: "OEIS A266285, ON cells of the Rule 13 elementary cellular automaton: closed-form, recurrence, generating-function and parity conjectures"
doi: null
url: https://oeis.org/A266285
claim: "A266285 is the number of ON (black) cells in the n-th iteration of the Rule 13 elementary cellular automaton started from a single ON cell; the entry records Colin Barker's conjectures a(n) = ((-1)^n*(3-2*n)+4*n+1)/4, a(n) = 2*a(n-2)-a(n-4) for n>3 and g.f. (1+x+2*x^3)/((1-x)^2*(1+x)^2), and Ctibor O. Zizka's conjectures a(2*n) = n+1 and a(2*n+1) = 3*n+1."
strata_touched:
  - D5/S3/StatisticalMechanics/CellularAutomata/Rule13OnCellCount
license: citation-only
triage: anchor
---

# OEIS A266285

A266285 (Robert Price, Dec 26 2015, offset 0, data `1, 1, 2, 4, 3, 7, 4, 10,
5, 13, 6, 16, …`) is

> Number of ON (black) cells in the n-th iteration of the "Rule 13" elementary
> cellular automaton starting with a single ON (black) cell.

Its program evolves `CellularAutomaton[13, {{1}, 0}, …]`, keeps the central
`2n + 1` cells of row `n` and counts the ON cells. The formula field reads

> Conjectures from _Colin Barker_, Dec 28 2015 and Apr 14 2019: (Start)
> a(n) = ((-1)^n*(3-2*n)+4*n+1)/4.
> a(n) = 2*a(n-2)-a(n-4) for n>3.
> G.f.: (1+x+2*x^3) / ((1-x)^2*(1+x)^2). (End)
> Conjecture from _Ctibor O. Zizka_, Mar 11 2025: (Start)
> a(2*n) = n + 1.
> a(2*n + 1) = 3*n + 1.(End)

The references are S. Wolfram, *A New Kind of Science*, Wolfram Media, 2002,
p. 55, and the MathWorld page on elementary cellular automata.

## Verified locator

- URL: https://oeis.org/A266285 (revision 28, last modified 2025-03-12; name,
  program and formula fields; retrieved through the OEIS JSON interface).
