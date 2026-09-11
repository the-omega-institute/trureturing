---
bibkey: wiseman2024antiruns
authors: Gus Wiseman
year: 2024
title: OEIS A373409, Length of the n-th maximal antirun of nonsquarefree numbers differing by more than one
doi: null
url: https://oeis.org/A373409
claim: "An antirun is an interval of positions in the nonsquarefree sequence whose consecutive terms differ by more than one. The entry conjectures that the maximum length is nine."
strata_touched:
  - D5/S3/Arith/Congruence/NonsquarefreeAntirun
license: citation-only
triage: anchor
---

# Nonsquarefree antiruns

The internal entry was retrieved on 2026-09-10. It states the upper bound as
a conjecture, reports confirmation to 100,000,000, and displays the nine-term
antirun beginning at 6345. Its computational report is not a proof of the
universal bound. The associated Lean module supplies an independent proof
using adjacent pairs forced by divisibility by four and nine.

## Verified locator

Canonical entry: https://oeis.org/A373409. Its internal text at
https://oeis.org/A373409/internal was retrieved on 2026-09-10:
the NAME field defines the sequence, the COMMENTS field states the
maximum-nine conjecture, and the EXAMPLE field gives the antirun beginning
at 6345. These passages attest the question and the reported example;
they do not supply the universal proof in this repository.
