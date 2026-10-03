---
bibkey: kimberling2025a035513
authors: Clark Kimberling
year: 2025
title: "OEIS A035513: Wythoff array read by falling antidiagonals"
doi: null
url: https://oeis.org/A035513
claim: "Conjecture: If m >= 2, then {(T(n,1), T(n,2)) mod m} has cardinality m^2."
strata_touched:
  - D5/S3/Arith/Wythoff/ColumnResiduePairs
license: citation-only
triage: anchor
---

# OEIS A035513

The conjecture appears in the comment block signed Clark Kimberling,
4 June 2025. The block uses positive row indices and numbers the first
two columns as 1 and 2; the first row begins `1,2,3,5,...`.
The official text interface returned revision 223, timestamp
13 May 2026 12:12:42, when retrieved on 3 October 2026. The assertion
is still labelled `Conjecture` in that revision.

Henry Bottomley's formula in the entry, signed 10 December 2001, is
`T(n,k)=F(k+1)*floor(n*phi)+F(k)*(n-1)`.
R. J. Mathar's formula, signed 3 September 2016, extends the columns by
`T(n,-1)=n-1`, `T(n,0)=floor(n*phi)`, and the Fibonacci recurrence.
For positive rows, the formal proof identifies the nested floors with
Bottomley's first two expressions, `floor(n*phi)+n-1` and
`2*floor(n*phi)+n-1`. The array definition continues these two columns
by the same Fibonacci recurrence. The all-column closed formula is
not a separate theorem in this module.

The OEIS entry links Kimberling, *Complementary equations and Wythoff
Sequences*, Journal of Integer Sequences 11 (2008), Article 08.3.3,
and identifies its Theorem 10 as an explicit formula for compound
Wythoff sequences. This bibliographic locator is checked in the OEIS
entry; this note does not assert a checked proof of the residue conjecture
in that paper.

## Verified locator

- https://oeis.org/search?q=id:A035513&fmt=text : revision 223, Kimberling's
  conjecture block and the Bottomley and Mathar formulas; retrieved 2026-10-03.
- https://oeis.org/history?seq=A035513 : history page retrieved with HTTP 200
  on 2026-10-03; no claim of an exhaustive historical search.
- https://cs.uwaterloo.ca/journals/JIS/VOL11/Kimberling/kimberling719a.html :
  bibliographic link supplied by the OEIS entry.

The bounded prior-work check is recorded in issue #12448. No claim of
publication priority or global novelty is made.
