---
bibkey: chenchen2026stepm
authors: Xin Chen and Yudian Chen
year: 2026
title: "OEIS A392664, A392665 and A392666: negative-step Eulerian triangles"
doi: null
url: https://oeis.org/A392664
claim: "Conjecture: T(n,k) >= 0 for all even n and all 1 <= k <= n, for m=-3,-4,-5."
strata_touched:
  - D5/S1/Recurrence/Algebraic/ChenChenParityPositivity
license: citation-only
triage: anchor
---

# Chen and Chen's step-m Eulerian triangles

The NAME and FORMULA sections of the three entries prescribe integer values
T(n,1)=T(n,n)=1 for n>=1 and, for 1<k<n,

`T(n,k)=(m*(n-k)+1)*T(n-1,k-1)+(m*(k-1)+1)*T(n-1,k)`.

A392664 uses m=-3, A392665 uses m=-4, and A392666 uses m=-5.
Each COMMENTS section states:

> Conjecture: T(n,k) >= 0 for all even n and all 1 <= k <= n.
> Verified for even n <= 400.

The proof target is this nonnegativity assertion, with existence and the
universal quantifier over all functions satisfying the boundary and recursion.
Other source comments about row sums, roots and parameter maps are outside it.
The source text is attributed to Xin Chen and Yudian Chen; citation-only
use here does not import source software or sequence tables.

## Verified locator

- https://oeis.org/A392664 and https://oeis.org/A392664/internal
- https://oeis.org/A392665 and https://oeis.org/A392665/internal
- https://oeis.org/A392666 and https://oeis.org/A392666/internal
