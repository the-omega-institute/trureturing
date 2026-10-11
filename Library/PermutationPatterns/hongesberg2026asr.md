---
bibkey: hongesberg2026asr
authors: H. Höngesberg; Matjaž Konvalinka; Svante Linusson
year: 2026
title: "Pattern avoidance in alternating sign rectangles I: Extended avoidance"
doi: 10.48550/arXiv.2610.07442
url: https://arxiv.org/abs/2610.07442v1
claim: "Conjecture 4.5 gives the closed form (4.2) for the number of extendably 312-avoiding alternating sign rectangles."
strata_touched:
  - D5/S3/Combinatorics/AlternatingSignRectangles/ExtendedAvoidanceClosedForm
license: citation-only
triage: anchor
---

# Pattern avoidance in alternating sign rectangles I: Extended avoidance

H. Höngesberg, Matjaž Konvalinka, and Svante Linusson define alternating sign rectangles in Section 2, prove the row-complete and empty-row recurrences in Propositions 4.2 and 4.3, prove the interior recurrence in Theorem 4.4, and state the closed form for extendably 312-avoiding rectangles as Conjecture 4.5 and equation (4.2). The Lean development uses the binding definitions from preregistration issue #14736 and settles that conjecture.

Section 2 (p. 3) states: “Let r and k be positive integers. An alternating sign rectangle (ASR) of size r × k is an r × k matrix with entries in {−1, 0, 1} such that”:

- “the nonzero entries alternate in each row and column;”
- “if a row contains a nonzero entry, then its leftmost and rightmost nonzero entries are 1;”
- “if a column contains a nonzero entry, then its topmost nonzero entry is 1.”

“An ASM is a square ASR whose rows and columns each sum to 1.” (p. 3).

“An ASR is said to extendably avoid a pattern if there exists an extension of the ASR to a square ASM that avoids the pattern.” (p. 3).

Conjecture 4.5 (p. 9) reads: “Conjecture 4.5. For integers d ≤ r, k, we have” followed by equation (4.2), the displayed closed form for `S^{312}_{r,k,d}`. Here `C_n = 1/(n+1) (2n choose n)` is the nth Catalan number.

## Verified locator

DOI: https://doi.org/10.48550/arXiv.2610.07442

Source: https://arxiv.org/abs/2610.07442v1
