---
bibkey: hardinbarker2018a185858
authors: R. H. Hardin and Colin Barker
year: 2018
title: "OEIS A185858: binary arrays with unequal neighboring three-by-three subblock traces"
doi: null
url: https://oeis.org/A185858
claim: "The literal array count divided by 128 has generating function 2*x*(2 + 3*x)/(1 - 4*x - 9*x^2) and the radical expression recorded in the FORMULA field."
strata_touched:
  - D5/S3/Combinatorics/TraceArrays/HardinA185858
license: citation-only
triage: anchor
---

# Hardin–Barker A185858

## Verified locator

Source: https://oeis.org/A185858

Revision 9, NAME and FORMULA, unpaginated. Hardin authored the entry;
Barker's conjecture block is attributed to Apr 17 2018. There is no associated
source arXiv identifier or located journal version.

The NAME field reads verbatim:

> 1/128 the number of (n+2) X 3 binary arrays with no 3 X 3 subblock trace equal to any horizontal or vertical neighbor 3 X 3 subblock trace.

The FORMULA field reads verbatim:

> Empirical: a(n) = 4*a(n-1) + 9*a(n-2).
>
> Conjectures from _Colin Barker_, Apr 17 2018: (Start)
>
> G.f.: 2*x*(2 + 3*x) / (1 - 4*x - 9*x^2).
>
> a(n) = ((2 - sqrt(13))^n*(-4+sqrt(13)) + (2+sqrt(13))^n*(4+sqrt(13))) / (3*sqrt(13)).
>
> (End)

The offset is 1; the first terms are 4, 22, 124, 694, 3892.
The arrays have entries in Fin 2, n+2 rows and three columns. Contiguous
three-by-three blocks have their ordinary main-diagonal sums in ℕ.
There is one block column, so the adjacency condition compares successive
block rows. There is no periodic boundary or quotient by symmetry.
The count is cast to ℚ and divided by 128. The formal generating series has
zero constant coefficient and coefficient a(n) at each positive index.
The radical formula is an equality in ℝ for n ≥ 1; sqrt is the nonnegative
real square root. No source term a(0) is asserted.

The repository proof separates the diagonal triples by column shifts,
leaving six free cells. Trace multiplicities 1, 3, 3, 1 give a transfer
recurrence with characteristic polynomial r² − 4r − 9. Coefficient comparison
and uniqueness of recurrence solutions give the two formulas for the literal
array count, rather than for an independently generated numerical sequence.

The literature screen in https://github.com/the-omega-institute/trureturing/issues/22162
is partial. Citation tracing, MathOverflow and broader non-arXiv discovery
remain ASSUMED-UNVERIFIED. No global priority claim is made. No inspected
source theorem depends on these conjectures; wider arrays, horizontal
constraints, other block sizes and periodic boundaries remain separate questions.

Independent finite corroboration is in
https://github.com/the-omega-institute/trureturing-experiments at commit
476ba03c81438134ebdda63dc9d0687d78f5beb8,
path docs/reports/hardin-a185858-trace-arrays/check.py,
SHA-256 19059d1da9d578751c7bcfbc604e9fcf7f8d4bbe7c5600220adaa8fc55b12bce.
The command `python3 docs/reports/hardin-a185858-trace-arrays/check.py`
has recorded exit 0 and final line ALL_CHECKS_OK. Exhaustive enumeration
at n = 1,…,5 and exact row-transfer, recurrence, power-series and radical
checks through n = 200 are corroboration, not the all-length proof.
