---
bibkey: hanna2009logarithmicclosure
authors: Paul D. Hanna
year: 2009
title: "Hanna's logarithmic integer-series power closure conjecture"
doi: null
url: https://oeis.org/A167138
claim: "Conjecture: For all integers m > 0, Sum_{n>=0} L(n)^m * log(1+x)^n/n! is an integer series whenever Sum_{n>=0} L(n)*log(1+x)^n/n! is an integer series."
strata_touched:
  - D5/S1/Recurrence/Algebraic/HannaLogarithmicPowerClosure
license: citation-only
triage: anchor
---

# Hanna's logarithmic closure question

The quoted general conjecture occurs identically in OEIS A167138 and A167139.
A167141 repeats the same assertion with capitalization and grammar differences. These are locations of one question. The partition example
A167137 and the square examples do not restrict its arbitrary sequence L.
The A167138/A167139 AUTHOR attribution is Paul D. Hanna, Nov 03 2009.
A167141 attributes it to Hanna, Nov 04 2009, and prints:

> CONJECTURE: For all integer m>0, Sum_{n>=0} L(n)^m * log(1+x)^n/n! is an integer series whenever Sum_{n>=0} L(n)*log(1+x)^n/n! is an integer series.

Its immutable source SHA-256 is
`05a1d290827a2932b439b91520c4ecd907f1b0275f50331af0a0ebbb0396a475`. The retained
revision-one histories already contain the assertion.

A167138 and A167139 revision 13 use ordinary coefficients: their examples
are ordinary integer series, and the signed first-kind Stirling transform
is divided by the ordinary degree factorial. Every natural sequence index
and degree, including zero, is retained. The field interpretation uses any
characteristic-zero field and its canonical integer image. No convergence,
positivity, normalization or support restriction is needed.

The immutable OEIS mirror at
`bd331f23038f1570c996386c6c221342aeb36fc5` has source hashes
`45abbe815cbec381fd5b71c3a2679a2981442ce6091ae8594ea5a0cb4463c255`
for A167138 and
`bcb45b2a17e9ecb8502ec5f54614d17092d97397935b30607171e8f9aeef4b82`
for A167139. Preregistration is issue
https://github.com/the-omega-institute/trureturing/issues/16500.

## Classical suppliers

Boyadzhiev and Frontczak, *The Hadamard product of series with Stirling
numbers of the second kind and other special numbers*, Electronic Journal
of Mathematics 4 (2022), 32–38, DOI 10.47443/ejm.2022.024, Corollary 3.1,
supply the fixed-column Hadamard EGF identity. Their analytic theorem is
used only through its finite entire-column identity. Arbitrary formal
input series need no analytic hypothesis. The finite formal extension
uses factorial-weighted Stirling inclusion-exclusion and degreewise finite
sums. Classical supplier identities are not claimed as new.

The exp/log inverse leaves are adapted from Ralf Stephan's Mathlib
`Mathlib/RingTheory/PowerSeries/Log.lean` at immutable revision
`ff5815e8fe1ecf6880c38ea997fb56395951822b`, source SHA-256
`ced40d5066d36c16787715c93fbadb9c3b63b773813ebe7c4f5bfa9ee21bfdad`.
Copyright (c) 2026 Ralf Stephan; Apache-2.0. The full license is
`docs/reports/log-inverse-suppliers/mathlib-LICENSE.txt`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`.
The complete immutable upstream tree has no NOTICE path. Upstream Lean
4.35 differs from the adopted Lean 4.33 pin; dependency form is unavailable.
Only consumed inverse leaves are adapted. Retire them when this repository's
adopted Mathlib Log.lean contains `PowerSeries.subst_exp_log` and
`PowerSeries.subst_log_exp_sub_one` with equivalent compiled types; direct
upstream calls then replace the adaptation.

## Bounded literature status

The original source qualification inspected the full primary 2022 paper,
current and immutable OEIS records and retained histories, exact-ID
Crossref/arXiv/MSE/MO queries, related Stirling/Hadamard queries and bounded
all-state repository ownership bodies. No exact earlier settlement was
identified in that scope. SeqFan archive access failed, and several general
search services rejected or rate-limited requests. This is neither worldwide
open-status certification nor a proof-novelty claim. A later exact settlement
would require reuse and would exclude a new-question count.

## Verified locator

https://oeis.org/A167138
