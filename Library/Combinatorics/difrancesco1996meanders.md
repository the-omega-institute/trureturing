---
bibkey: difrancesco1996meanders
authors: P. Di Francesco, O. Golinelli, E. Guitter
year: 1996
title: "Meanders: A Direct Enumeration Approach"
doi: 10.1016/S0550-3213(96)00505-6
url: https://arxiv.org/abs/hep-th/9607039
claim: "Appendix D (D.14) gives a resummed small-t prediction whose second diagonal yields the A400429 polynomial; the text does not establish its all-n coefficient validity."
strata_touched:
  - D5/S3/Combinatorics/SemiMeanderSecondDiagonal
license: citation-only
triage: anchor
---

# Di Francesco, Golinelli and Guitter, meanders

P. Di Francesco, O. Golinelli and E. Guitter, *Meanders: A Direct Enumeration
Approach*, Nuclear Physics B **482** (1996), 497-535,
DOI `10.1016/S0550-3213(96)00505-6`, arXiv:hep-th/9607039.
The 46-page arXiv PDF at `https://arxiv.org/pdf/hep-th/9607039` was inspected
on 29 September 2026, especially Appendix D, PDF pages 41-44 (printed pages
40-43), and the conclusion, PDF page 32 (printed page 31).

## Verified locator

- DOI: 10.1016/S0550-3213(96)00505-6 (Nuclear Physics B 482, 497-535).
- URL: https://arxiv.org/abs/hep-th/9607039 (46-page arXiv PDF, Appendix D
  and conclusion inspected 2026-09-29).

Appendix D defines a generating function in (D.1) whose `q` exponent counts
connected components and whose `t` exponent indexes the winding deficit:
`t^j` corresponds to winding `n-2j`. For fixed `k`, (D.9) expresses the count
with `n-k` components and winding `n-2j` as a polynomial in `n`, with small-`n`
corrections. The authors say they computed these polynomials for `0<=j<=k<=14`
from enumeration through `n<=24`. The text then says, "we expect the numbers"
to be polynomials "for large enough n". Equations (D.11)-(D.13) concern
large-`n` and large-`q` asymptotics.

Before (D.14), the authors write that they "have been able to re-sum the large
q series coefficients of this expansion up to order 3 in t". The displayed
`t^2` rational terms of the two functions in (D.14), inserted into the
asymptotic factorization (D.11), predict the same second diagonal polynomial
`(n^2+2*n+(n mod 2)-20)/2`. The conclusion calls (D.14) a "purported
re-summation". The inspected text does not prove that extracting the `q^1 t^2`
coefficient of this asymptotic resummation is valid for every finite `n`: that
coefficient has `k=n-1`, outside the fixed-`k` scope of (D.9). Thus the
polynomial was predicted in 1996; it is not a new formula, and the present
theorem is described as an independent all-`n` proof rather than a certified
first proof.
