---
bibkey: naimi2026swapping
authors: Ramin Naimi
year: 2026
title: Swapping Compatible Words
doi: 10.48550/arXiv.2610.31967
url: https://arxiv.org/html/2610.31967v2#S8.p1
claim: Section 8 asks whether adjacent compatibility suffices for bijective cyclic replacement of all pattern occurrences at their original positions.
strata_touched:
  - D5/S1/Words/Forbidden/NaimiCyclicWordReplacement
license: CC-BY-4.0
triage: anchor
---

# Swapping Compatible Words

## Verified locator

DOI: https://doi.org/10.48550/arXiv.2610.31967

The question is in the opening paragraph of §8 on printed and PDF page 33 of
arXiv:2610.31967v2. Section 2.1 defines borders, compatibility and occurrences.
Section 2.3, PDF p. 5, defines a swap by an equivalence of occurrences at
the same position in hosts of the same length. Ramin Naimi is the paper's
sole author. [Swap definition](https://arxiv.org/html/2610.31967v2#S2.SS3.p4.1) · [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)
[Versioned abstract](https://arxiv.org/abs/2610.31967v2) · [PDF page 33](https://arxiv.org/pdf/2610.31967v2#page=33)

## Finite linear words

The counterexample formalized here uses the cycle `001, 002, 011, 021`,
which has equal self-border lengths and equal
directed border lengths in both directions along each adjacent edge. In
`0021`, replacing `002` and `021` at their respective starts would require
different letters at one output coordinate. The exact finite-linear claim
and its negation are `NaimiCyclicWordReplacement.claim` and
`NaimiCyclicWordReplacement.result`.
