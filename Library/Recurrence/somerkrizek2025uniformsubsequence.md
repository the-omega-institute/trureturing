---
bibkey: somerkrizek2025uniformsubsequence
authors: Lawrence Somer; Michal Krizek
year: 2025
title: "Generalization of a Theorem of Velez on Uniform Distribution in Second-Order Linear Recurrences"
doi: 10.5281/zenodo.14679256
url: https://math.colgate.edu/~integers/z1/z1.pdf
claim: "Conjecture 4.2 proposes that every uniformly distributed k-th order integer recurrence modulo p^e, with least period p^e E and last coefficient coprime to p, remains uniformly distributed on every coprime-step subsequence, with E/gcd(g,E) copies of each residue in the stated finite range."
strata_touched:
  - D5/S1/Recurrence/Periodic/SomerUniformSubsequenceRefutation
license: citation-only
triage: anchor
---

# Somer and Krizek, Conjecture 4.2

The paper defines the k-th order integer recurrence

`w(n+k) = a1*w(n+k-1) + a2*w(n+k-2) + ... + ak*w(n)`

for `k >= 2`. Conjecture 4.2 assumes that modulo `p^e` the sequence has
least period `p^e E`, that the last coefficient `ak` is coprime to `p`,
and that every residue occurs exactly `E` times in that least period. For
each positive `g` coprime to `p` and nonnegative `s`, it sets
`r = E/gcd(g,E)` and asserts that every residue occurs exactly `r` times
among `w(s+ng)` for `0 <= n < p^e r`.

The paper's Example 4.3 supplies positive evidence from a different
third-order recurrence. It does not prove the conjecture.

## Verified locator

- DOI: 10.5281/zenodo.14679256
- URL: https://math.colgate.edu/~integers/z1/z1.pdf
- Printed location: page 8, Conjecture 4.2
- Publication: INTEGERS 25 (2025), A1, published January 17, 2025
