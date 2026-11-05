---
bibkey: mazhang2026baladivisibilities
authors: Haobo Ma; Wenlin Zhang
year: 2026
title: "Bala's parity conjecture and product extensions of his divisibilities (2026): OEIS A295462, References (#19, 23 August 2026)"
doi: null
url: https://oeis.org/A295431
claim: "Corollary 5: five fixed divisibilities of T(n) and two product families with explicit sufficient constants."
strata_touched:
  - D5/S3/Arith/FactorialRatio/BalaA295431Divisibility
license: CC-BY-4.0
triage: anchor
---

# Actual T divisibilities

## Verified locator

Question and context: https://oeis.org/A295431

Proof source: the supplied Ma–Zhang revision 3, 4 November 2026,
section “The divisibility questions in A295431”, Corollary 5
(`cor:families`) and its complete proof. The exact release, tag and
source hashes below identify the checked source bytes. The OEIS URL
locates the posing question; no public URL for the supplied revision
was verified.

Ma and Zhang, revision 3, 4 November 2026, Corollary 5 (`cor:families`)
and its complete proof. Supplied release 433788709, tag
`outreach-task-shortnote-e3f06e33a1179fd1a53bf8a9fd4b3a7e`. The released `note.tex` has SHA256
`13161dd555043bd323b307643c249bf47281bd7408567b6b752d2dec19d40e18`.
The six-member source archive has SHA256
`77d04b7b832ae88438ad00983cab0662884205257eaa7c31bc3879b308883bcb`.
The supplied source is licensed under CC BY 4.0:
https://creativecommons.org/licenses/by/4.0/.

For every natural n, let T(n)=(12n)! n!/((6n)! (4n)! (3n)!).
The five integer expressions are 385T(n)/(n+1), 5T(n)/(2n+1),
T(n)/(3n+1), 770T(n)/((n+1)(2n+1)(3n+1)), and T(n)/(12n-1).
The last subtraction is signed, giving -1 at n=0.
For every R>=1 and k=1,2,3, the first product denominator is
product(i=1,...,R)(kn+i), with constant 36(R-1)! lcm(1,...,12R).
The second is the signed product of 12n-i over 1<=i<=R with gcd(i,12)=1,
with constant (R-1)! lcm(1,...,R). All factors are nonzero; an empty
product is one. The constants are sufficient, without a minimality claim.

Peter Bala posed these questions in A295431 Comments, 28 August 2025:
https://oeis.org/A295431/internal.
Integrality of this sporadic factorial ratio predates the source: see
J. W. Bober, Table 2, entry 1, DOI 10.1112/jlms/jdn078,
https://arxiv.org/abs/0709.1977v2.
The formalization reuses the repository's original factorial-ratio producer.
The fifth fixed expression is an internal R=1 specialization of the second
family, not an independent discovery. No new priority claim is made.

The supplied finite checker supports only its stated finite ranges and is
not used as an all-input proof. Other Bala parity, XOR and formula results,
Blanco Gomez's congruence and Gamma statements, the remaining moment density,
minimal constants and the other sporadic ratios are outside this module.
