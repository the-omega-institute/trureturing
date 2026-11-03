---
bibkey: bala2021triangularcuberoots
authors: Peter Bala; Paul D. Hanna
year: 2021
title: OEIS A193237 and A193236, congruences for triangular reciprocal cube roots
doi: null
url: https://oeis.org/A193237/internal
claim: "Conjectures: a(5*n+4) == 0 (mod 5) and a(7*n+5) == 0 (mod 7) (both checked up to n = 200). - _Peter Bala_, Feb 26 2021"
strata_touched:
  - D5/S1/Recurrence/Residue/BalaA193237ModFiveSeven
  - D5/S1/Recurrence/Residue/BalaA193236ModFiveSeven
license: citation-only
triage: anchor
---

## Verified locator

Source: https://oeis.org/A193237/internal

Companion source: https://oeis.org/A193236/internal

The source has no DOI, arXiv identifier or page number. A193237 revision 18
and A193236 revision 20 share the revision timestamp Sep 22 2025 16:01:08.
Their unnumbered FORMULA lines attribute both conjectures to Peter Bala;
Paul D. Hanna authored both sequence entries.

## Source statements

A193237's NAME line reads verbatim:

> Expansion of g.f.:  ( Sum_{n>=0} (2*n+1)*3^n*(-x)^(n*(n+1)/2) )^(-1/3).

A193236's NAME line reads verbatim:

> Expansion of g.f.: ( Sum_{n>=0} (-3)^n*(2*n+1)*x^(n*(n+1)/2) )^(-1/3).

Each entry's FORMULA line reads verbatim:

> Conjectures: a(5*n+4) == 0 (mod 5) and a(7*n+5) == 0 (mod 7) (both checked up to n = 200). - _Peter Bala_, Feb 26 2021

Both offsets are zero. The examples choose the reciprocal cube root with
constant coefficient one. The Lean definitions use rational formal power
series and the literal weights; each coefficient is a finite sum over
j in Finset.range(m+1). The claim asserts existence, integral coefficients
for every normalized rational solution, and both divisibilities for every
natural n, without a finite index bound.

## Mathematical scope

For F=1+9H over the integers with constantCoeff(H)=0, coefficient contraction
constructs U=H-3U²-3U³. Thus B=1+3U satisfies B³=F, and its inverse is integral.
For any integer weights w, the series with coefficient (2j+1)w(j) at triangular
degree j(j+1)/2 is supported in residues {0,1} modulo five and {0,1,3} modulo
seven. Its cube misses residue four modulo five; its square misses residue
five modulo seven. Frobenius transfers these gaps to an integral reciprocal
cube root. Rational uniqueness covers every normalized solution.

## Finite evidence and literature boundary

The independent exact-arithmetic experiment is in
`the-omega-institute/trureturing-experiments`, commit
`67ccba7d1caa3774156d523b819df3316774e695`, directory
`docs/reports/bala-a193237-a193236-mod5-mod7/`. The SHA-256 of `check.py` is
`7613bcfbf58f29e849b82b9e80a311bf05c535445c74477217e58e8e83a44ad7`.
The reported command `python3 /tmp/op-bala193237/check.py --bfile-dir /tmp/op-bala193237/src`
exited 0 with final line `ALL_CHECKS_OK`. It checked both b-files through
index 1000, 701 mod-five cases and 501 mod-seven cases per source through
degree 3505. These are reported finite checks, independent of the Lean proof.

Literature completeness is ASSUMED-UNVERIFIED. Issues
https://github.com/the-omega-institute/trureturing/issues/22112 and
https://github.com/the-omega-institute/trureturing/issues/22113 record the
screened scope and rate-limited searches. No absence-of-prior-proof claim
follows from those limits. Other moduli, higher prime powers and asymptotics
remain open here; no downstream source theorem relying on these conjectures
was identified in the recorded screen.
