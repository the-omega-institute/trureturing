---
bibkey: hofmann2025rule163
authors: Karl-Heinz Hofmann; Robert Price; Colin Barker; Yosu Yurramendi
year: 2025
title: "OEIS A392003 and A266753: the Rule 163 even-subsequence, closed-form, recurrence and generating-function conjectures"
doi: null
url: https://oeis.org/A392003
claim: "The even subsequence of A392003 equals A266753; A266753 has closed form (7*4^n-4)/6 for n>1, first-order recurrence a(n)=4*a(n-1)+2 for n>1, second-order recurrence a(n)=5*a(n-1)-4*a(n-2) for n>2, and generating function (1-x+2*x^2)/((1-x)*(1-4*x))."
strata_touched:
  - D5/S3/StatisticalMechanics/CellularAutomata/Rule163EvenSubsequence
license: citation-only
triage: anchor
---

## Verified locator

Source: https://oeis.org/A392003 (revision 30, NAME and FORMULA; unpaginated).

Source: https://oeis.org/A266753 (revision 49, NAME, FORMULA and Mathematica
program; unpaginated).

## Source statements

A392003, NAME and FORMULA:

```text
a(n) = (7*2^n - 9 + 5*(-1)^n) / 6.
Conjecture: a(2*n) = A266753(n).
```

A266753, NAME:

```text
Decimal representation of the n-th iteration of the "Rule 163" elementary cellular automaton starting with a single ON (black) cell.
```

A266753, FORMULA:

```text
Conjectures from _Colin Barker_, Jan 20 2016 and Apr 20 2019: (Start)
a(n) = 5*a(n-1)-4*a(n-2) for n>2.
G.f.: (1-x+2*x^2) / ((1-x)*(1-4*x)).
(End)
Empirical a(n) = (7*4^n - 4)/6 for n>1. - _Colin Barker_, Nov 25 2016 and Apr 20 2019
a(n) = 4*a(n-1) + 2, n>1, conjectured. - _Yosu Yurramendi_, Jan 22 2017
```

## Mathematical interpretation

A266753 reads the cells at integer coordinates -n through n of time n from
left to right as a base-2 integer, the rightmost bit having weight 1. The
single ON cell is at the origin at time 0. All integer cells update
synchronously, including the initially zero exterior. Wolfram rule 163
returns bit 4l+2c+r of 163. Its 000 and 111 neighborhoods both produce 1.
A392003 has source offset 1; the subsequence equation uses n at least 1.
The closed form uses rational division. The second-order recurrence uses
integer subtraction. The generating function is a formal power series over
the integers, expressed by multiplying by its denominator, whose constant
term is 1.

The five source assertions and the exact source-to-Lean correspondence are
specified in [issue #22909](https://github.com/the-omega-institute/trureturing/issues/22909).
The row invariant is the central word 100(10)^(n-1), with exterior 1, at every
positive time. The closed form extends to n=1; the first recurrence starts
at n=2 and the second at n=3. The exceptional first step accounts for the
numerator's 2*x^2 term.

## Evidence and limits

The independent finite experiment is in
`the-omega-institute/trureturing-experiments`, commit
`543c6e1f3bdaa0d1c2325175c9d5b689c58135db`, at
`docs/reports/rule-163-even-subsequence/check.py`, sha256
`393f5bf922e569fae046125a37dc1b5024d157013b8000f3b8de69008065df82`.
The preregistration reports exit 0 for
`python3 docs/reports/rule-163-even-subsequence/check.py` and exact checks
through time 300; finite computation does not prove the unbounded claim.

The literature screen and its unavailable searches are specified in issue
#22909. No settling reference was located in that searched scope;
completeness is ASSUMED-UNVERIFIED. Additional binary-as-decimal identities,
A266752 base-10 formulas and arbitrary initial configurations are outside
the five assertions.
