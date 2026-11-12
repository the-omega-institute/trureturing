---
bibkey: hardinbarker2018a202330
authors: R. H. Hardin; Colin Barker; OEIS Foundation Inc.
year: 2018
title: "OEIS A202330: four-column binary arrays with nondecreasing two-bit windows"
doi: null
url: https://oeis.org/A202330
claim: "The empirical quartic and Barker conjectural generating function and recurrence count the native labeled (n+1) by 4 binary arrays."
strata_touched:
  - D5/S3/Combinatorics/TraceAvoidingArrays/HardinA202330
license: CC-BY-SA-4.0
triage: anchor
---

# OEIS A202330

## Source and license

The OEIS Foundation Inc., [A202330](https://oeis.org/A202330), revision 8,
2018-05-27 14:42:35, NAME, FORMULA and OFFSET fields, unpaginated.
R. H. Hardin authored the sequence; Colin Barker supplied the conjectural
generating function and recurrence. The quoted entry text is licensed
[CC BY-SA 4.0](https://creativecommons.org/licenses/by-sa/4.0/).
The mathematical exposition and Lean proof are original to this repository.

Immutable source:
<https://raw.githubusercontent.com/oeis/oeisdata/2066359a24c83163fd067fc54d1d20d143c5be69/seq/A202/A202330.seq>.

```text
Number of (n+1) X 4 binary arrays with consecutive windows of two bits considered as a binary number nondecreasing in every row and column.
Column 3 of A202335.
Empirical: a(n) = (1/12)*n^4 + (4/3)*n^3 + (83/12)*n^2 + (44/3)*n + 13.
Conjectures from _Colin Barker_, May 27 2018: (Start)
G.f.: x*(36 - 98*x + 112*x^2 - 61*x^3 + 13*x^4) / (1 - x)^5.
a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5).
(End)
```

The source offset is `1,1`. The recurrence applies when all five lagged source
indices are positive, namely at every index at least six. The formal series has
zero constant coefficient; evaluating the quartic at zero does not give that
coefficient. The parent A202335 uses `(n+1)` by `(k+1)` arrays, so its column
`k=3` has the source width four.

## Scope and existing results

[Preregistration #28964](https://github.com/the-omega-institute/trureturing/issues/28964)
fixes the full native counting event, all three formulas and their domains.
The bounded source screen identifies LODA's direct quartic program, joeis's
`Conjectural` generating-function program and the integer-program equivalence
benchmark as formula evidence. They do not supply the native-cardinality bridge.
No covering native proof was identified in that screen; completeness of the
literature screen and worldwide priority remain `ASSUMED-UNVERIFIED`.

## Mathematical route

The legal horizontal rows are exactly `0000,0001,0010,0011,0111,1111`.
All 36 ordered row pairs are retained. A transition from `(a,b)` to `(d,c)`
is allowed exactly when `d=b` and every column has
`2*a_j+b_j <= 2*b_j+c_j` in the integers. The coordinate-preserving row
bijection and the exact initial and transition fibres instantiate
`TransferMatrix.good_iff_local` and `TransferMatrix.cardMatrix`.
The continuation vector has a polynomial invariant from exponent two onward.
Induction gives the quartic for all larger indices; the actual counts at one
and two are 36 and 82. The fifth difference and formal coefficient comparison
give the recurrence and generating function. No finite-height extrapolation,
symmetry quotient or assumed ordering between `0001` and `0010` is used.
