---
bibkey: hennessey2024tree
authors: Aidan Hennessey
year: 2024
title: Tree and Tripod Nim
doi: 10.48550/arXiv.2401.07943
claim: Section 9.3 defines D(k,n); printed Conjecture 2 says that each periodic orbit of D(3,n) has a period dividing 2(4n)(4n+1).
strata_touched:
  - D5/S0/Certificates/TripodNimPeriodRefutation
license: citation-only
triage: anchor
---

# Tree and Tripod Nim

Source: https://arxiv.org/pdf/2401.07943v1, printed pages 28 and 30.
The arXiv version is dated 15 January 2024; the title page is dated September 2023.

Section 9.3 uses k rows and 2n+k columns. Rows are processed from bottom
to top, with lower rows representing smaller entries. The transition first
shifts left and fills the rightmost column with zeros. Each row whose
harvested bit was zero receives a one at its leftmost permitted zero.
The leftmost n columns are excluded, and two new ones in one transition
cannot occupy the same column. Existing ones in other rows do not by
themselves block that column.

Printed page 30 states Conjecture 2 with the expression 2(4n)(4n+1), and
Remark 9.2 reports confirmation for n ≤ 9. This note attests that source
statement and transition, not its truth or the repository's counterexample.
Only the printed conjecture is at issue; no conclusion about the rest of
the paper, the author's intended claim, or a corrected formula is asserted.

No priority for the counterexample is claimed.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2401.07943
- Preprint: https://arxiv.org/abs/2401.07943
