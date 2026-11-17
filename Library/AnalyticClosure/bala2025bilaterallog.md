---
bibkey: bala2025bilaterallog
authors: Peter Bala
year: 2025
title: "The bilateral logarithm conjecture in OEIS A292179 and A292178"
doi: null
url: https://oeis.org/A292179
claim: "A two-parameter bilateral variable-exponent series equals the negative logarithm on the separate unit disks."
strata_touched:
  - D5/S3/Analytic/PowerSeries/BalaBilateralLog
license: citation-only
triage: anchor
---

# The bilateral logarithm question

## Verified locator

https://oeis.org/A292179 and https://oeis.org/A292178.
The fixed source for A292179 is revision 20, stored in oeis/oeisdata at
733c77ba475e0b6fa0b8abe7681ef040217ae7f7, seq/A292/A292179.seq:

> Conjecture: Sum_{n in Z - {0}} (x - a^n)^n / n = -log(1 - x) for |x| < 1 and |a| < 1. - _Peter Bala_, Mar 02 2025

The fixed source for A292178 is revision 27, stored at
571197984aeda7b8b680fe3a1f6a43f9898cd441, seq/A292/A292178.seq:

> More generally, it appears that Sum_{n = -oo..+oo, n <> 0} (x - a^n)^n / n = -log(1 - x) for |x| < 1 and |a| < 1. - _Peter Bala_, Nov 03 2024

These are two presentations of one question. The exact semantic event is
registered at https://github.com/the-omega-institute/trureturing/issues/29113#issuecomment-6786264041.

The complete result is frozen as
[`D5/S3/Analytic/PowerSeries/BalaBilateralLog.full_event`](../../D5/S3/Analytic/PowerSeries/BalaBilateralLog.lean).
Its theorem statement identity is
`sha256:cfa16b4f63ea3670ff516012c45819638398745620c257362a49a16d260c8285`.
The [canonical module state](../../Golden/Frozen/state/D5/S3/Analytic/PowerSeries/BalaBilateralLog.lean.json)
has statement identity
`sha256:a91c3224893d9bc66032f238309adae06a62c9e5e9db320c9e8614ae74066776`.

## Definition correspondence

The real source is restricted to a!=0 because its negative powers require
that condition. The source index n is unchanged. The regular tails use
m=k+1, p_m=(x-a^m)^m/m and
q_m=(-1)^(m+1)*a^(m*m)/(m*(1-x*a^m)^m).
They define F as their two unordered sums independently of the proposed value.
For nonzero a, q_m equals the raw term at -m, with every ordinary negative
base and divisor proved nonzero. The raw family is defined only on nonzero
parameters and nonzero integer indices. The regular tails give the separate
continuous extension at a=0.

The complex version uses separate bounds norm(x)<1 and norm(a)<1 and the
principal Complex.log. Its argument 1-x lies in the right half-plane.
The real source value is -Real.log(1-x), with 1-x>0. Absolute summability
justifies unordered, two-tail and symmetric interpretations.

## Suppliers and conclusion

Pinned Mathlib supplies hasSum_choose_mul_geometric_of_norm_lt_one,
summable_prod_of_nonneg, Summable.of_norm, Summable.tsum_comm,
Complex.hasSum_taylorSeries_neg_log, and Complex.ofReal_log.
The application establishes joint absolute summability of the triangular
variable-exponent coefficients by an eventual geometric row majorant.
The owning Scribe gives the cancellation and all source-domain bridges.
The full event and its 18 consumed private theorem helpers have
`proof_shape: bind-only`; no escape witness is claimed. The proposed
admission basis is `open-problem-resolution` for the single source problem
in [the owning dossier](../../Problems/bala-a292179-a292178-bilateral-logarithm.md),
with the original preregistration and bounded qualification in issue #29113.

## Literature search boundary

The source qualifier and bounded source/literature readings are identified
in issue #29113. No full-target supplier was identified in the inspected
repository D5 declarations, including private originals, or pinned Mathlib.
The private native integer-binomial wrappers in FinalLaurentEvaluation
reduce to the upstream Nat.choose supplier; this result uses that supplier
directly and does not copy those wrappers.

Wang-Wang's full paper, the original Horn 2003 item, Berndt-Chu's full paper,
untraversed citations, other implicit suppliers, and individual OEIS revision
views requiring sign-in remain uninspected. These bounded readings do not
certify global absence of a prior proof, novelty, priority or continued openness.
