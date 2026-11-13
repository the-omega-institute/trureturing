---
bibkey: hanna2010a181070family
authors: Paul D. Hanna
year: 2010
title: OEIS A181070, A181074, A181078 and A181080 integrality conjectures
doi: null
url: https://oeis.org/A181070
claim: All coefficients of the four specified formal exponential generating functions are integers.
strata_touched:
  - D5/S1/Recurrence/Algebraic/HannaA181070Integrality
  - D5/S1/Recurrence/Algebraic/HannaA181074Integrality
  - D5/S1/Recurrence/Algebraic/HannaA181080Integrality
  - D5/S1/Recurrence/Algebraic/HannaA181078Integrality
license: citation-only
triage: anchor
---

## Verified locator

Source: https://oeis.org/A181070

Companion entries: https://oeis.org/A181074 and https://oeis.org/A181080.
The entries have no page numbers. The source is OEIS; it has no arXiv identifier.

## Source statements

### A181070

```text
%N A181070 Expansion of G.f.: A(x) = exp( Sum_{n>=1} (Sum_{k=0..n} C(n,k)^(k+1)*x^k)*x^n/n ).
%C A181070 Conjecture: this sequence consists entirely of integers.
%C A181070 Note that the following g.f. does NOT yield an integer series:
%C A181070 exp( Sum_{n>=1} (Sum_{k=0..n} C(n,k)^k * x^k) * x^n/n ).
%A A181070 _Paul D. Hanna_, Oct 02 2010
```

### A181074

```text
%N A181074 Expansion of g.f.: exp( Sum_{n>=1} [ Sum_{k>=0} C(n+k-1,k)^(k+1) *x^k ] *x^n/n ).
%C A181074 Conjecture: this sequence consists entirely of integers.
%C A181074 Note that the following g.f. does NOT yield an integer series:
%C A181074   exp( Sum_{n>=1} [Sum_{k>=0} C(n+k-1,k)^k * x^k] * x^n/n ).
%A A181074 _Paul D. Hanna_, Oct 02 2010
```

### A181078

```text
%N A181078 Expansion of g.f.: exp( Sum_{n>=1} [ Sum_{k>=0} C(n+k-1,k)^(n+k-1) *x^k ] *x^n/n ).
%C A181078 Conjecture: this sequence consists entirely of integers.
%A A181078 _Paul D. Hanna_, Oct 03 2010
```

Immutable source: https://raw.githubusercontent.com/oeis/oeisdata/de48538e52019dc132e250666b0d677b40045ceb/seq/A181/A181078.seq

Revision #6, Sep 22 2025 16:01:04; SHA-256
`ed0f486cf0c2324b9fafb0fe3cbe8ef726eee79481c310f6a6a63b07f2c760e1`.
This is an ordinary formal exponential with natural subtraction in both the
binomial top and exponent. The term n=1,k=0 has exponent zero and value x.
Every degree m, including zero, is in scope. The companion A181079 describes
its logarithm and does not constitute a second assertion of integrality here.
Worldwide openness and priority completeness remain unverified.

### A181080

```text
%N A181080 Expansion of g.f.: exp( Sum_{n>=1} [Sum_{k=0..n} C(n,k)^(n-k+1) * x^k] * x^n/n ).
%C A181080 Conjecture: this sequence consists entirely of integers.
%C A181080 Note that the following g.f. does NOT yield an integer series:
%C A181080   exp( Sum_{n>=1} [Sum_{k=0..n} C(n,k)^(n-k) * x^k] * x^n/n ).
%A A181080 _Paul D. Hanna_, Oct 02 2010
```

## Formal interpretation

The sums and exponential are formal over the rationals. In degree m only terms
with n+k=m contribute. A181070 and A181080 retain 0 <= k <= n;
A181074 and A181078 retain all k >= 0. The exponent in A181078 is n+k-1. The exponent in A181080 is n-k+1.
The assertion includes degree zero and does not assert analytic convergence.

## Experiment

The exact Python checker is in the-omega-institute/trureturing-experiments,
commit 829585d8339cc9be1ffe3f927053962a5a8cef08, at
docs/reports/hanna-a181070-family-integrality/check.py.
Its SHA-256 is ff3ba3ed51b2256abb1177c3f1341491e0468a0f1607fd8627ab6a2ac036ce11.
The recorded command is `python3 docs/reports/hanna-a181070-family-integrality/check.py`,
exit 0, with final output ALL_CHECKS_OK. These finite checks are separate
from the all-degree Lean proofs.

## Literature boundary

The literature screen is recorded in issues #22220, #22221 and #22222.
Completeness is ASSUMED-UNVERIFIED; unavailable citation searches do not
establish the absence of a published proof.
