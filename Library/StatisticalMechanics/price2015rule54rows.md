---
bibkey: price2015rule54rows
authors: Robert Price; Eric W. Weisstein
year: 2015
title: "OEIS A259661, A118109 and A265225, centre column, rows and ON-cell totals of the Rule 54 elementary cellular automaton: recurrence, generating-function and closed-form conjectures"
doi: null
url: https://oeis.org/A259661
claim: "A259661 is the binary representation of the middle column of the Rule 54 elementary cellular automaton started from a single ON cell, A118109 the binary representation of its n-th iteration and A265225 the total number of ON cells after n iterations; the entries record Colin Barker's conjectures a(n) = 11*a(n-1) - 11*a(n-2) + 11*a(n-3) - 10*a(n-4) for n>3 with g.f. 1/((1-x)*(1-10*x)*(1+x^2)) for A259661, a(n) = 10001*a(n-2)-10000*a(n-4) for n>3 with g.f. (1+111*x)/((1-x)*(1+x)*(1-100*x)*(1+100*x)) for A118109, and a(n) = (n+1)*(2*n -(-1)^n +5)/4, a(n) = a(n-1) + 2*a(n-2) - 2*a(n-3) - a(n-4) + a(n-5) for n>4 with g.f. (1+3*x)/((1-x)^3*(1+x)^2) for A265225, Karl V. Keller's a(n) = floor((10000+1100*(n mod 2))*100^n/9999) for A118109 and Wesley Ivan Hurt's a(n) = n + 1 + (n+1)*floor((n+1)/2) for A265225."
strata_touched:
  - D5/S3/StatisticalMechanics/CellularAutomata/Rule54Rows
license: citation-only
triage: anchor
---

# OEIS A259661, A118109 and A265225

A259661 (Robert Price, Dec 05 2015, offset 0, data `1, 11, 110, 1100, 11001, …`)
is

> Binary representation of the middle column of the "Rule 54" elementary
> cellular automaton starting with a single ON (black) cell.

with formula field

> Conjectures from _Colin Barker_, Dec 08 2015 and Apr 17 2019: (Start)
> a(n) = 11*a(n-1) - 11*a(n-2) + 11*a(n-3) - 10*a(n-4) for n>3.
> G.f.: 1 / ((1-x)*(1-10*x)*(1+x^2)).
> (End)

A118109 (Eric W. Weisstein, 2006, offset 0, data `1, 111, 10001, 1110111, …`)
is

> Binary representation of n-th iteration of the Rule 54 elementary cellular
> automaton starting with a single black cell.

Its program takes the central `2n + 1` cells of row `n` and applies
`FromDigits` in base 10. The formula field reads

> Conjectures from _Colin Barker_, Dec 08 2015 and Apr 16 2019: (Start)
> a(n) = 10001*a(n-2)-10000*a(n-4) for n>3.
> G.f.: (1+111*x) / ((1-x)*(1+x)*(1-100*x)*(1+100*x)).
> (End)
> Conjecture: a(n) = floor((10000+1100*(n mod 2))*100^n/9999). - _Karl V.
> Keller, Jr._, Sep 24 2021

A265225 (Robert Price, Dec 05 2015, offset 0, data `1, 4, 6, 12, 15, 24, …`)
is

> Total number of ON (black) cells after n iterations of the "Rule 54"
> elementary cellular automaton starting with a single ON (black) cell.

Its program is `Accumulate[Total /@ CellularAutomaton[54, {{1}, 0}, 52]]`. The
formula field reads

> Conjectures from _Colin Barker_, Dec 08 2015 and Apr 20 2019: (Start)
> a(n) = (n+1)*(2*n -(-1)^n +5)/4.
> a(n) = a(n-1) + 2*a(n-2) - 2*a(n-3) - a(n-4) + a(n-5) for n>4.
> G.f.: (1+3*x) / ((1-x)^3*(1+x)^2).
> (End)
> a(n) = n + 1 + (n+1) * floor((n+1)/2), conjectured. - _Wesley Ivan Hurt_,
> Dec 25 2016

Rule 54 is the elementary rule behind the interacting integrable reversible
cellular automaton of Bobenko, Bordemann, Gunn and Pinkall (1993), studied as
"Rule 54" by Buča, Klobas and Prosen (arXiv:2103.16543), which apply it on a
staggered lattice; the entries use the synchronous elementary automaton.

## Verified locator

- URL: https://oeis.org/A259661 (revision 55, last modified 2025-02-16; name,
  program and formula fields; retrieved 2026-09-29 through the OEIS JSON
  interface).
- URL: https://oeis.org/A118109 (revision 53, last modified 2025-02-16; name,
  program and formula fields; retrieved 2026-09-29 through the OEIS JSON
  interface).
- URL: https://oeis.org/A265225 (revision 48, last modified 2025-02-16; name,
  program and formula fields; retrieved 2026-09-29 through the OEIS JSON
  interface).
