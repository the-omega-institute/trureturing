---
bibkey: kimberling2021a341249
authors: Clark Kimberling
year: 2021
title: "OEIS A341249: a(n) = floor(r*floor(s*n)), where r = 2 + sqrt(2) and s = sqrt(2)."
doi: null
url: https://oeis.org/A341249
claim: "Conjecture:  1 < r*s*n - a(n) < 2 for n >= 1."
strata_touched:
  - D5/S0/Certificates/KimberlingA341249BoundRefutation
license: citation-only
triage: anchor
---

# OEIS A341249

## Verified locator

Source: https://oeis.org/A341249

The entry's NAME and COMMENTS fields, revision 10, state:

> a(n) = floor(r*floor(s*n)), where r = 2 + sqrt(2) and s = sqrt(2).

> Conjecture:  1 < r*s*n - a(n) < 2 for n >= 1.

OEIS is an unpaginated source; these locators identify the fields rather than a page.
Its offset is 1, and its data begin 3, 6, 13, 17, 23, 27, 30, 37.

The Lean sequence uses natural indices and integer-valued floors of real products.
The universal proposition restricts the index to n at least 1. At n = 2, the
inner floor is 2 and a(2) = 6, so the difference is 4 sqrt(2) - 2 > 2.
This refutes the stated upper bound; no universal corrected bound is asserted here.
