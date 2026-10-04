---
bibkey: price2016rule79oncells
authors: Robert Price
year: 2016
title: "OEIS A266981, ON cells of the Rule 79 elementary cellular automaton: closed-form, recurrence, generating-function and parity conjectures"
doi: null
url: https://oeis.org/A266981
claim: "A266981 is the number of ON (black) cells in the n-th iteration of the Rule 79 elementary cellular automaton started from a single ON cell; the entry records Colin Barker's conjectures a(n) = (3+(-1)^n-2*(-2+(-1)^n)*n)/4, a(n) = 2*a(n-2)-a(n-4) for n>3 and g.f. (1+2*x+x^3)/((1-x)^2*(1+x)^2), and Ctibor O. Zizka's conjectures a(2*n) = n+1 and a(2*n+1) = 3*n+2."
strata_touched:
  - D5/S3/StatisticalMechanics/CellularAutomata/Rule79OnCellCount
license: citation-only
triage: anchor
---

# OEIS A266981

A266981 (Robert Price, offset 0, data `1, 2, 2, 5, 3, 8, 4, 11, 5, 14, 6, 17,
…`) is

> Number of ON (black) cells in the n-th iteration of the "Rule 79" elementary
> cellular automaton starting with a single ON (black) cell.

Its program evolves `CellularAutomaton[79, {{1}, 0}, …]`, keeps the central
`2n + 1` cells of row `n` and counts the ON cells. The formula field reads

> Conjectures from _Colin Barker_, Jan 08 2016 and Apr 19 2019: (Start)
> a(n) = (3+(-1)^n-2*(-2+(-1)^n)*n)/4.
> a(n) = 2*a(n-2)-a(n-4) for n>3.
> G.f.: (1+2*x+x^3) / ((1-x)^2*(1+x)^2). (End)
> Conjecture from _Ctibor O. Zizka_, Mar 11 2025: (Start)
> a(2*n) = n + 1.
> a(2*n + 1) = 3*n + 2.(End)

The references are S. Wolfram, *A New Kind of Science*, Wolfram Media, 2002,
p. 55, and the MathWorld page on elementary cellular automata.

## Verified locator

- URL: https://oeis.org/A266981 (revision 33, last modified 2025-03-12; name,
  program and formula fields; retrieved through the OEIS JSON interface).
