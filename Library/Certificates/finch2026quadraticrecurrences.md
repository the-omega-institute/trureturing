---
bibkey: finch2026quadraticrecurrences
authors: Steven Finch
year: 2026
title: "Three Quadratic Recurrences Modulo 3: What We Can Prove and What We Can Guess"
doi: null
url: https://arxiv.org/abs/2610.34300v1
claim: "Conjecture 23: For every k congruent to 2 or 3 modulo 4 with N_A(k)=4, z(k)-mu_A(k)=6."
strata_touched:
  - D5/S0/Certificates/FinchConjecture23CaptureOffsetRefutation
license: citation-only
triage: anchor
---

# Three quadratic recurrences modulo 3

Recurrence (A) starts at positive indices with zeros through k-1 and x(k)=1,
and continues by x(n)=x(n-1)+x(n-k)^2 in Z/3 for n≥k+1. The final Addendum
fixes k≥2. Definition 15 requires a run to start at r≥k+1, have positive gap
count g, and have exactly the zeros r,r+4,...,r+4g in that interval.
Definition 21 takes the least endpoint of a run with G=ceil((k-1)/4) gaps.
Definition 22 takes the least natural μ with x(n+4)=x(n) for all n>μ.
Conjecture 23 asserts z-μ=6 when k mod 4 is 2 or 3 and the least positive
eventual period is 4.

The source labels the identity a conjecture. Its displayed evidence starts
at k=3. The k=2 small-case refutation uses the explicit least-μ definition;
the source's accompanying last-disagreement equivalence has no last
mismatch in a purely periodic case. No corrected domain is proved.

## Verified locator

- URL: https://arxiv.org/abs/2610.34300v1
- TeX: https://arxiv.org/src/2610.34300v1, qrm3.tex, recurrence (A), Definition 15, Definitions 21–22 and Conjecture 23.
- PDF: https://arxiv.org/pdf/2610.34300v1, pp. 1, 6 and 9.
- Source archive SHA256: b3579798626ad820df20dac27a52305017f3fc9fb09b97a5e0481f7936b02b7b.
- TeX SHA256: 833076fda3c8577da619fcfa2f1ad7738894121a5445772287cdb4ab22a61302.
