---
bibkey: price2016rule201rows
authors: Robert Price
year: 2016
title: "OEIS A267681 and A267680, rows of the Rule 201 elementary cellular automaton: recurrence, generating-function and closed-form conjectures"
doi: null
url: https://oeis.org/A267681
claim: "A267681 is the decimal representation of the n-th iteration of the Rule 201 elementary cellular automaton started from a single ON cell, and A267680 its binary representation; the entries record Colin Barker's conjectures a(n) = 5*a(n-1)-20*a(n-3)+16*a(n-4) for n>4 with g.f. (1-5*x+21*x^2+14*x^3-40*x^4)/((1-x)*(1-2*x)*(1+2*x)*(1-4*x)) for A267681, a(n) = 101*a(n-1)-10100*a(n-3)+10000*a(n-4) for n>4 with g.f. (1-101*x+10101*x^2+89910*x^3-101000*x^4)/((1-x)*(1-10*x)*(1+10*x)*(1-100*x)) for A267680, and M. F. Hasler's conjecture a(n) = 2*4^n - (n%2*2 + [n]*5)*2^(n-1) - 1 for A267681."
strata_touched:
  - D5/S3/StatisticalMechanics/CellularAutomata/Rule201Rows
license: citation-only
triage: anchor
---

# OEIS A267681 and A267680

A267681 (Robert Price, Jan 19 2016, offset 0, data `1, 0, 21, 99, 471, 1935, …`)
is

> Decimal representation of the n-th iteration of the "Rule 201" elementary
> cellular automaton starting with a single ON (black) cell.

Its program takes the central `2n + 1` cells of row `n` of
`CellularAutomaton[201, {{1}, 0}, …]` and applies `FromDigits` in base 2. The
formula field reads

> Conjectures from _Colin Barker_, Jan 19 2016: (Start)
> a(n) = 5*a(n-1)-20*a(n-3)+16*a(n-4) for n>4.
> G.f.: (1-5*x+21*x^2+14*x^3-40*x^4) / ((1-x)*(1-2*x)*(1+2*x)*(1-4*x)).
> (End)
> Conjecture: a(n) = 2*4^n - (n%2*2 + [n]*5)*2^(n-1) - 1, where [n] = 1 iff
> n > 0; n%2 = 1 iff n is odd. - _M. F. Hasler_, Jul 28 2018

and the history records

> Removed an unjustified claim that _Colin Barker_'s conjectures are correct.
> Removed a program based on a conjecture. - _Michael De Vlieger_, Jun 13 2022

A267680 (Robert Price, Jan 19 2016) is the binary representation of the same
rows: the same digits read as a decimal numeral. Its formula field reads

> Conjectures from _Colin Barker_, Jan 19 2016 and Apr 20 2019: (Start)
> a(n) = 101*a(n-1)-10100*a(n-3)+10000*a(n-4) for n>4.
> G.f.: (1-101*x+10101*x^2+89910*x^3-101000*x^4) / ((1-x)*(1-10*x)*(1+10*x)*(1-100*x)).
> (End)

Rule 201 is the local update rule of the Floquet-PXP cellular automaton of
Wilkinson, Klobas, Prosen and Garrahan, Phys. Rev. E 102 (2020) 062107, which
applies it to alternating sublattices; the entries use the synchronous
elementary automaton.

## Verified locator

- URL: https://oeis.org/A267681 (revision 30, last modified 2025-02-16; name,
  program, formula and history fields; retrieved 2026-09-28 through the OEIS
  JSON interface).
- URL: https://oeis.org/A267680 (revision 21, last modified 2025-02-16; name,
  program and formula fields; retrieved 2026-09-28 through the OEIS JSON
  interface).
