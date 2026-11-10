---
bibkey: hasler2026a359482proof
authors: M. F. Hasler
year: 2026
title: A359482, Proof by MFH
doi: null
url: https://oeis.org/w/index.php?title=A359482&oldid=1675118
claim: "The original A359482 sequence has no later single-digit term and has exactly 10 among its positive two-digit multiples of ten."
strata_touched:
  - D5/S3/Arith/SumInConcatenation/DecimalMultiples
license: citation-only
triage: anchor
---

# Hasler's full A359482 proof

## Verified locator

doi: null
url: https://oeis.org/w/index.php?title=A359482&oldid=1675118

The approved OEIS Wiki revision 1675118, section “2023 Conjecture”, subsection
“Proof by MFH”, contains the complete proof. The second part begins with
the successor case a(n+1)=10m, 2<=m<=9. Its three cases place the sum at
the last digit, one digit before the end, or in the old operand. OEIS main
entry revision 52, dated October 2, 2026, explicitly credits Wenlin Zhang
and Haobo Ma's prior Lean proof of the first part and Hasler's independent
proof of both parts. The entry is readable at
https://oeis.org/search?q=id%3AA359482&fmt=text.

## Mathematical correspondence

For x>0 and 1<=m<10, the formal classification is Legal(x,10m) iff x=m.
The reverse decimal concatenation begins with the digits 0,m followed by
the digits of x. Put q=10^length(digits(x+10m)). A substring beginning at
the first of these positions gives 99x=qR. Coprimality of q and 99 forces
q to divide x, contradicting 0<x<q. Beginning one digit later gives
9(x-m)=qR; coprimality with 9 forces x=m. An occurrence entirely in the
digits of x forces x+10m=x. Conversely x=m is legal for each of the nine
positive one-digit values of m.

This formulation retains the exceptional predecessor x=m in the middle
position. The sequence conclusion then uses its actual preceding term:
the initial term is 1 and every term from index 2 is at least 10. Hence
20,30,...,90 are absent. The least-unused rule chooses 10 at index 2.
Consequently a positive index with value 10m exists exactly when m=1.

## Attribution and scope

The full published conjecture resolution is Hasler's. The canonical
`D5/S3/Arith/SumInConcatenation` module records the earlier repository
contribution by Ma and Zhang; its definitions and six public theorems are
preserved. The extension is a formal transfer of the known decimal
argument. It makes no discovery, priority, or coauthorship claim and says
nothing about hundreds or other bases. The proof is re-expressed in Lean
from the supplied formal source; the OEIS text is cited, not redistributed
as code under a different license.
