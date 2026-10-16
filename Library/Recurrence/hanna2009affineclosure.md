---
bibkey: hanna2009affineclosure
authors: Paul D. Hanna
year: 2009
title: "Hanna's logarithmic integer-series arithmetic-subsequence conjecture"
doi: null
url: https://oeis.org/A167540
claim: "For integers m>0, b>=0, Sum_{n>=0} L(m*n+b) * log(1+x)^n/n! is an integer series whenever Sum_{n>=0} L(n)*log(1+x)^n/n! is an integer series."
strata_touched:
  - D5/S1/Recurrence/Algebraic/HannaLogarithmicAffineClosure
license: citation-only
triage: anchor
---

# Hanna's arithmetic-subsequence question

The OEIS CONJECTURE comment attributes the exact quoted assertion to Paul D.
Hanna, Nov 06 2009. The initial retained official history already contains it;
the subsequent retained revision changes attribution formatting. The immutable
mirror is `seq/A167/A167540.seq` at OEIS data commit
`72c53dd50967ac7166f7d31bf79be95174ec5bc6`, SHA-256
`97049e84b0bc33cbccb54c92588ee3472280c6236d0d6e8517ef14c8e716e9a6`.
The entry's displayed ordinary generating function and coefficient extraction
code fix "integer series" to mean integer ordinary coefficients. Its named
example uses log(1-2x), whereas the universal conjecture explicitly uses
log(1+x); the example does not alter that logarithm or restrict arbitrary L.
A167532 is a pointwise-power question, distinct from arithmetic extraction.

## Classical suppliers

DLMF 26.8, equations E6, E8, E10 and E12, records the classical Stirling
inclusion-exclusion, logarithmic, falling-factorial and exponential column
identities. Rahmani, *Generalized Stirling transform*, arXiv `1212.0957v1`,
DOI `10.18514/mmn.2014.1084`, and Bounebirat–Laissaoui–Rahmani,
*Some combinatorial identities via Stirling transform*, DOI
`10.7546/nntdm.2018.24.4.92-98`, supply related inversion and shifted-index
identities. Their inspected complete statements do not assert the arbitrary
dilation question quoted here. These are citation sources, not copied code.

The formal proof directly uses the repository's factorial-weighted
`stirling2_inclusion_exclusion` and original
`HannaLogarithmicPowerClosure.reconstruction`, `subst_exp_log`,
`map_transform`, `coeff_transform` and `T_window`. The original inverse
leaves retain their Apache-2.0 source and full-license provenance in
`hanna2009logarithmicclosure.md`; no inverse proof is copied into the affine
module. The pinned Mathlib exponential-rescaling and coefficient identities
are applied directly. No classical supplier or proof method is claimed novel.

## Bounded literature status

The source qualification inspected current and immutable OEIS records and
retained history, exact-ID arXiv/MSE/MO/GitHub queries, related Stirling and
integer-valued-polynomial searches, the complete Rahmani source and the
complete seven-page NNTDM paper, and bounded repository issue/PR ownership
indices. No exact whole settlement or conflicting owner was identified within
those scopes. Blocked history views, rate-limited queries, unavailable SeqFan
and challenged general search services provide no absence evidence. There is
no global absence, priority or method-novelty claim. Preregistration and the
full-field interpretation are at
https://github.com/the-omega-institute/trureturing/issues/16545.

## Verified locator

https://oeis.org/A167540

https://raw.githubusercontent.com/oeis/oeisdata/72c53dd50967ac7166f7d31bf79be95174ec5bc6/seq/A167/A167540.seq

https://dlmf.nist.gov/26.8

https://arxiv.org/abs/1212.0957

https://doi.org/10.18514/mmn.2014.1084

https://doi.org/10.7546/nntdm.2018.24.4.92-98
