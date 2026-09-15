---
bibkey: benfieldlippard2024fixedpoints
authors: Brennan Benfield, Oliver Lippard
year: 2024
title: "Fixed points of K-Fibonacci sequences"
doi: 10.1080/00150517.2025.2491986
url: https://arxiv.org/abs/2404.08194v2
claim: '(v) $a \equiv -1 \pmod{6}$ and $m = p_i^{j_i}$ or $m = 6 \cdot p_1^{j_1+1} \cdots p_t^{j_t}$.'
strata_touched:
  - D5/S1/Recurrence/LucasCompanion
  - D5/S1/Scale/Lucas
license: citation-only
triage: anchor
---

# Fixed points of K-Fibonacci sequences

The paper determines the fixed points of the K-Fibonacci recurrence
`F_0=0`, `F_1=1`, `F_n=K*F_{n-1}+F_{n-2}` from the factorization of `K^2+4`.
It also proves that iteration of its period map from every modulus greater than
3 eventually reaches a fixed point.

Section 6, "Final Thoughts", considers the general recurrence
`U_n=a*U_{n-1}+b*U_{n-2}`. Conjecture 6.5 concerns `U_0=0`, `U_1=1`, `b=-1`:
for `a>2`, `m>1`, prime factorization `a^2-4=p_1^{e_1}...p_t^{e_t}`, and
nonnegative integers `j_i`, it asserts an if-and-only-if classification of
`pi_(a,-1)(m)=m`. The quoted clause (v) is its `a=-1 (mod 6)` case; the exponent
`j_1+1` is retained literally. The following unnumbered observation says that
only one prime has powers that are fixed points for a given parameter, calls
it the critical prime, and singles out `a=3` as having no critical prime.

Status: clause (v) 'only if' direction refuted by a=47, m=15 (this repository,
theory volume PERIODIC_TREE, appendix TR.15). The same appendix proves the
complete fixed-point towers at both 3 and 5, refuting the uniqueness observation.
These counterexamples are supplied by this repository, not by the cited paper.

## Source locator

The cited text is arXiv:2404.08194v2, 29 July 2024, Section 6, Conjecture 6.5(v)
and the paragraph immediately following it: https://arxiv.org/abs/2404.08194v2.
PR #7709 reports publication in The Fibonacci Quarterly (2025) and DOI
10.1080/00150517.2025.2491986; that journal DOI has not been independently
resolved here.
