---
bibkey: dekking2022twoblock
authors: F. M. Dekking and M. Keane
year: 2022
title: Two-block substitutions and morphic words
doi: 10.48550/arXiv.2202.13548
url: https://arxiv.org/abs/2202.13548v1
claim: Conjecture 4 of v1 asserts that the frequency of 1 in the Thue-Morse two-block fixed point with prefix 00 exists and equals one half.
strata_touched:
  - D5/S1/Words/TwoBlockSubstitution/ThueMorseFrequency
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.48550/arXiv.2202.13548

Source: https://arxiv.org/abs/2202.13548v1

## The source word

Section 4, “Thue-Morse meets Kolakoski”, p. 5 of v1:

> We consider the two-block substitution $\kappa_{\rm TM}$ defined by
> $\kappa_{\rm TM}(00)=001,\quad \kappa_{\rm TM}(01)=010,\quad \kappa_{\rm TM}(10)=101,\quad \kappa_{\rm TM}(11)=110.$

> The fixed point $x=x^{(00)}=x_0x_1\ldots$ of the two-block morphism $\kappa_{\rm TM}$ with prefix 00 satisfies very similar recurrence relations:
> $x_{3n}=x_{2n},\quad x_{3n+1}=x_{2n+1},\quad x_{3n+2}=1-x_{2n+1}.$

The encoding uses `false` for 0, `true` for 1 and natural indices starting at
zero. The recursion reads the residue before making a recursive call; its
prefix is 00. The source prints
$x^{(00)}=001110101101110010110001101110001\ldots$.

## Conjecture 4

Section 4, p. 6 of v1:

> **Conjecture 4** The frequency of 1 in $x^{(00)}$ exists and equals $\frac12$.

Frequency means the limit of the number of indices $n<N$ with $x_n=1$, divided
by $N$. The formal statement uses a real-valued `Filter.Tendsto` of this ratio
along `Filter.atTop`. The value at $N=0$ is immaterial to the limit.

This locator is specifically v1. ArXiv v2 and the journal version, *Advances in
Applied Mathematics* 148 (2023), 102536, change the substitution. The present
statement concerns the table quoted above.

## Scope of the conclusion

The coefficient functional of the signed substitution has zero adjacent cyclic
correlation and squared energy $3^{k-1}$ for $k\ge1$. Finite Cauchy–Schwarz
bounds aligned block sums; a prefix decomposition makes their normalized sum
tend to zero. This proves the quoted single-letter frequency assertion.
Mirror invariance, quadratic complexity, uniform recurrence and frequencies of
longer factors are separate questions.
