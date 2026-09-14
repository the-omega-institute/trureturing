---
bibkey: grellpeng2015pellheight
authors: George Grell; Wayne Peng
year: 2015
title: Wall's Conjecture and the ABC Conjecture
arxiv: 1511.01210
claim: Number-field abc implies infinitely many non-Fibonacci-Wieferich primes; the appended Pell-block argument records an explicit conditional budget for the original initial depths.
license: citation-only
triage: anchor
---

# Fixed-golden Pell heights and original WSS depth mass

## Primary sources actually read

1. George Grell and Wayne Peng, arXiv:1511.01210v1,
   https://arxiv.org/abs/1511.01210 . The six-page PDF was fetched and
   Section 4, Theorem 3 and its proof were read in parsed text and a rendered
   screenshot of printed page 4. Their argument uses abc over Q(sqrt(5)),
   the simple-prime-divisor part of F_n and a radical bound to prove
   conditional infinitude of non-WSS primes. This mechanism is prior art,
   not a new solved conjecture in our continuation. The earlier displayed
   product-style claim about Pisano periods is not used here.

2. Wayne Peng, Journal of Number Theory 212 (2020), 354-375,
   DOI 10.1016/j.jnt.2019.11.010,
   https://www.sciencedirect.com/science/article/pii/S0022314X1930410X .
   Publisher abstract and author-university metadata were read. The result
   generalizes conditional non-Wieferich infinitude to a finite algebraic
   base set. The complete published 22-page proof was not inspected in this
   increment. The related preprint is arXiv:1511.05645.

3. Luis A. Medina and Eric Rowland, *p-regularity of the p-adic valuation of
   the Fibonacci sequence*, Fibonacci Quarterly 53 (2015), 265-271,
   https://arxiv.org/abs/0910.2907 . The current v4 PDF's Theorems 1.2 and
   1.4 were read; the latter was also visually inspected on printed page 2.
   The initial valuation remains arbitrary. Its historic computation bound
   is not treated as an up-to-date WSS search bound.

4. OEIS A113650, https://oeis.org/A113650/internal . The retrieved entry
   contains its July 2026 update and still states that no WSS prime is known.
   Bounded current searches found no verified WSS example or complete
   resolution. This is not an exhaustive novelty or status certificate.

## Exact scope of the new ordinary proof

The mathematical continuation is appended to the existing target document
`Problems/wall-sun-sun-golden-unit-lift.md`, PH.1-PH.7. Its entire captured
5790-byte prefix, blob 199c3215a06d546fef0d5c75b12d8e0b744e4d1c, is preserved.
The historical Gap and Route sections in that prefix are not a fresh audit
of all present-day frozen modules. No new theory volume is introduced.

At a prime INDEX ell>=7, use the actual original values
A=F_ell, B=L_ell, M=F_(2ell)=AB, C=5A^2=B^2+4. Every factor has exact rank
ell or 2ell, and its exponent in M is the original initial WSS depth h_p.
These are not generalized recurrences or a variable quadratic field.

Let U contain only exponent-one primes, W the full factors p^h_p with
h_p>=2, E the excess factors p^(h_p-2) for h_p>=3, and R=10 rad(M).
The identities M=UW and WE=100 M^2/R^2 are unconditional.
The depth-d budget W_(>=d)^(d-1) <= (M/rad(M))^d is also unconditional.

The uniform height inequality C<=H R^kappa is an EXPLICIT EXTRA HYPOTHESIS,
required only for these prime-index Pell triples. Rational abc would imply
it for every kappa>1. It has not been proved here. Under it, W is bounded by
100(H/sqrt(5))^(2/kappa) M^(2-2/kappa)/E. Kappa<2 forces a non-WSS factor
in every sufficiently large paired block; kappa<4/3 forces one in EACH of
the exact-rank ell and 2ell channels. The quantified exponents, particularly
4/kappa-3 in the separate-channel lower bounds, are derived in full.

The limiting logarithmic WSS-factor mass under all these height hypotheses
is zero. This is not the natural density of WSS primes. The argument is
consistent with an empty WSS set and cannot establish WSS existence.
Its classical height/radical mechanism is credited above; no first-discovery
claim is made for this prime-rank packaging or its corollaries.

## Relation to concurrent repository work

Inspected captured dev a5f31555da3d1c07befe13beea8010ffeba91f3e and the
actual #7708 head 9fd688d9cfe67c92d15409868435aa53c636fc34. That open branch
contains separate initial-depth parity, ramified digits, 5040 readouts,
density decoding and conditional EMW arguments. It has a pre-existing
merge conflict. This independent dev-based branch does not replace,
revert or import those pending sources. Integrating their additions to the
same problem document later requires preserving both appendices.

Also read the dispositions of #7446 and #7607, whose candidate Lean modules
were withdrawn as bind-only and ingested as theory. No such module is
reinstated. The real norm identity already doubles the return-trace depth;
that observation alone cannot force or exclude initial depth two.

## Verification and unresolved obligation

Exact finite diagnostics actually run:
- 15 prime-index pairs, ell=7 through 61, with complete factorization.
- 43 distinct actual prime factors; independent exact-rank tests and direct
  fast-doubling evaluation at the ORIGINAL index p-(5/p) modulo p^(h_p+1).
- 625 synthetic exponent patterns on fixed primes, testing factor identities;
  these are not actual WSS examples or Fibonacci realizability evidence.
- The old-factor boundary at index 91: thirteen has a square factor there
  while its initial depth remains one.

No actual WSS prime occurs in these samples. Pointwise height checks do not
prove a uniform H, and no exhaustive prime-search bound is advanced.
No Lean/lake, Scribe/C# compilation, CI, independent-model review, frozen
admission or new external-open-problem resolution is claimed. No Lean or
Scribe files are added for the classical factorization and conditional
inequalities. Diagnostic scripts remain outside the repository delta.

The remaining arithmetic obligation is an unconditional height/radical or
other depth constraint on the original fixed-golden blocks that yields a
new restriction without assuming the displayed height hypothesis. A proof
of WSS existence would additionally have to force a positive exceptional
contribution; none of the upper bounds does so.
