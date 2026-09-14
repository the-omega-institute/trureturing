---
bibkey: kimberling2012a192023
authors: Clark Kimberling
year: 2012
title: "OEIS A192023, The Wiener index of the comb-shaped graph |_|_|...|_| with 2n (n>=1) nodes"
doi: null
url: https://oeis.org/A192023
claim: "The Wiener index of the comb-shaped graph |_|_|...|_| with 2n (n>=1) nodes. The Wiener index of a connected graph is the sum of the distances between all unordered pairs of vertices in the graph. Conjecture: for n>2, A192023(n-2) is the number of 2 X 2 matrices with all terms in {1,2,...,n} and determinant 2n. - _Clark Kimberling_, Mar 31 2012"
strata_touched:
  - D5/S0/Certificates/KimberlingCombWienerDeterminantRefutation
license: citation-only
triage: anchor
---

# OEIS A192023

The NAME of A192023 defines the graph statistic:

> The Wiener index of the comb-shaped graph |_|_|...|_| with 2n (n>=1) nodes. The Wiener index of a connected graph is the sum of the distances between all unordered pairs of vertices in the graph.

The FORMULA line gives `a(n) = n*(2*n^2 + 6*n - 5)/3.` The 2022 paper
*Wiener Index of Some Brooms* proves this graph-index formula, not the
matrix-count comment. The literal comment fails already at n = 3: the
two-vertex comb has index one and exactly two allowed matrices have
determinant six. No corrected comment or exhaustive literature claim follows.

## Verified locator

- URL: https://oeis.org/A192023
- NAME (verbatim): The Wiener index of the comb-shaped graph |_|_|...|_| with 2n (n>=1) nodes. The Wiener index of a connected graph is the sum of the distances between all unordered pairs of vertices in the graph.
- FORMULA (verbatim): a(n) = n*(2*n^2 + 6*n - 5)/3.
- COMMENTS conjecture line (verbatim): Conjecture: for n>2, A192023(n-2) is the number of 2 X 2 matrices with all terms in {1,2,...,n} and determinant 2n. - _Clark Kimberling_, Mar 31 2012
