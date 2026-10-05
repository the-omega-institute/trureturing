---
bibkey: price2016rule41oncells
authors: Robert Price
year: 2016
title: "OEIS A266614, ON cells of the Rule 41 elementary cellular automaton: recurrence and generating-function conjectures"
doi: null
url: https://oeis.org/A266614
claim: "A266614 is the number of ON (black) cells in the n-th iteration of the Rule 41 elementary cellular automaton started from a single ON cell; the entry records Colin Barker's conjectures a(n) = a(n-2)+a(n-4)-a(n-6) for n>5 and g.f. (1+x^2+3*x^3-2*x^4+5*x^5)/((1-x)^2*(1+x)^2*(1+x^2))."
strata_touched:
  - D5/S3/StatisticalMechanics/CellularAutomata/Rule41OnCellCount
license: citation-only
triage: anchor
---

# OEIS A266614

A266614 (Robert Price, Jan 01 2016, offset 0, data `1, 0, 2, 3, 1, 8, 2, 11,
1, 16, 2, 19, …`) is

> Number of ON (black) cells in the n-th iteration of the "Rule 41" elementary
> cellular automaton starting with a single ON (black) cell.

Its program evolves `CellularAutomaton[41, {{1}, 0}, …]`, keeps the central
`2n + 1` cells of row `n` and counts the ON cells. The formula field reads

> Conjectures from _Colin Barker_, Jan 02 2016 and Apr 18 2019: (Start)
> a(n) = a(n-2)+a(n-4)-a(n-6) for n>5.
> G.f.: (1+x^2+3*x^3-2*x^4+5*x^5) / ((1-x)^2*(1+x)^2*(1+x^2)).
> (End)

The references are S. Wolfram, *A New Kind of Science*, Wolfram Media, 2002,
p. 55, and the MathWorld page on elementary cellular automata.

## Verified locator

- URL: https://oeis.org/A266614 (revision 18, last modified 2025-02-16; name,
  program and formula fields; retrieved through the OEIS JSON interface).
