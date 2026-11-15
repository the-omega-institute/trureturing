---
bibkey: vsp2026pascalhadamard
authors: VSP
year: 2026
title: "Total positivity of Hadamard powers of Binomial matrix"
doi: null
url: https://mathoverflow.net/questions/515594
claim: "Every strictly separated minor of the Pascal matrix's real Hadamard power is positive for every r>0."
strata_touched:
  - D5/S3/Combinatorics/BinomialBases/PascalHadamardPositivityRefutation
license: CC-BY-SA-4.0
triage: anchor
---

# Fractional Hadamard powers of the Pascal matrix

The original independent question asks whether, for every natural size n,
every strictly separated pair of increasing row and column lists and every
real exponent r>0, the selected minor of the entrywise-powered Pascal
matrix has strictly positive determinant. The later appended question
about nonzero determinants for r>1 is a separate unresolved assertion.

## Verified locator

- Source: https://mathoverflow.net/questions/515594
- Author: [VSP](https://mathoverflow.net/users/126770/vsp).
- Original revision 1 GUID: `24043C19-8B17-4527-819F-D0DAEA1E8F86`.
- Exact revision: https://mathoverflow.net/revisions/24043C19-8B17-4527-819F-D0DAEA1E8F86/view-source
- API: https://api.stackexchange.com/2.3/revisions/24043C19-8B17-4527-819F-D0DAEA1E8F86?site=mathoverflow&filter=withbody

The original source states:

> Let $A = \left[\binom{i}{j}\right]$ for $0 \leq i,j \leq n$.
> We know that A is totally nonnegative, i.e., all its minors are nonnegative.
> Consider the matrix $A^{\circ r}=\left[\binom{i}{j}^r\right]$, where $r>0$ is real.
> Can we say that every minor of lower triangular matrix $A^{\circ r}$ below
> the main diagonal are positive, i.e. $\det(\binom{i}{j}^r)>0$ for
> $i=\alpha_1,\ldots,\alpha_k$, $j=\beta_1,\ldots,\beta_k$, and
> $\beta_1<\ldots<\beta_k<\alpha_1<\ldots<\alpha_k$?

Source text is attributed to VSP under
[CC BY-SA 4.0](https://creativecommons.org/licenses/by-sa/4.0/).
The quotation normalizes mathematical spacing and omits the closing
request for help. The Lean and Blueprint adaptation expresses the lists
as natural-valued functions on `Fin k`, makes the bound by n explicit,
uses `Nat.choose`, real `rpow` and `Matrix.det`, and supplies a refutation.
The adapted source exposition is shared under the same license. No source
computer program is copied; Mathlib proof ingredients retain their own license.

## Exact counterexample and scope

For n=5, rows (3,4,5), columns (0,1,2), and r=1/10, the unpowered minor is
`[[1,3,3],[1,4,6],[1,5,10]]`. Its powered determinant equals
`40^(1/10)+18^(1/10)+15^(1/10)-2*30^(1/10)-12^(1/10)`.
Exact tenth-power comparisons bound this above by `-30/1000000`.
The natural quantifiers include k=0; the empty determinant is one and
does not alter the original positive-size question's truth value.

Fallat, Johnson and Sokal, *Total positivity of sums, Hadamard products
and Hadamard powers: Results and counterexamples*, arXiv:1612.02210v2,
DOI 10.1016/j.laa.2017.01.013, with corrigendum
DOI 10.1016/j.laa.2020.12.019, supplies general fractional-power
counterexamples and exponent-preservation results. The inspected
Hadamard-power section and corrigendum did not establish a complete
answer to this fixed Pascal-family question. Their explicit rank-two
Hankel counterexample has unpowered determinant zero; the Pascal minor
above has unpowered determinant one, so positive diagonal rescaling
does not identify those matrices.

The bounded source qualifications found no identified prior complete
answer for the original independent assertion. Worldwide priority and
uninspected equivalent arguments remain unknown. The inaccessible
Ashrafi-Gibson symmetric-Pascal article (DOI 10.1016/j.laa.2005.02.041)
has not been excluded by its title. No originality claim for general
fractional Hadamard-power failure, nor a result for the appended r>1
nonvanishing question, follows from this refutation.
