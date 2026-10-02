---
slug: bar-lev-2026-universal-hyperbolic-bound-refutation
bibkey: barlev2026blockretrieval
doi: 10.48550/arXiv.2603.17154
url: https://arxiv.org/html/2603.17154v2
triage: theorem
motivation_gids:
  - D5/S3/Resource/VandermondeHyperbolicRefutation.result
---

# The universal hyperbolic retrieval bound

## Problem

Bar-Lev, arXiv:2603.17154v2, Section V-B, Conjecture 1, asserts
`s1/E1+s2/E2<=1` for every finite field, every positive two-file
partition `s1+s2=k` with `max(s1,s2)>=2`, every length `n>=k`, and every
rank-`k` generator. Each physical column index is drawn independently,
uniformly and with replacement. `Ei` is the expectation of the minimum
time at which the sampled-column span contains the entire coordinate
file. Duplicate indices remain separate draws. Preregistration #11729
fixes this complete statement and a nonzero-column refutation criterion.

## Motivation

The assertion proposes a universal tradeoff between complementary files
under arbitrary linear encoding. A single valid counterexample decides
this all-generators assertion. A systematic positive subcase or a
projected-rank bound does not decide it.

## Gap

The mathematical certificate uses the actual iid expectation bridge;
there is no assumed recurrence or chosen expectation definition.
The escape audit is unfinished. Scoped compilation reports
`IE-C050`, `unclassified_form`, `E5.unsaturated_definition`
at the mirrored Reg source's `predicate`; current accepted binding
evidence for this source is not obtained. The compiled bridge, law
variation and sensitivity do not establish `declared_validated`.
The concrete registration obstacle and missing binding evidence are
tracked in https://github.com/the-omega-institute/trureturing/issues/11765.
Normal admission, freezing, rendering and merged delivery are separate
obligations. No merged settlement KPI is claimed.

## Route

Over `ZMod 11`, take `k=3`, `(s1,s2)=(1,2)`, `n=20`. Ten physical
columns are `(1,0,0)`. The other ten are `(1,x,x^2)` for `x=1,...,10`.
Every column is nonzero. Parameters `0,1,2` give three independent
Vandermonde columns, so the matrix has rank three.

For a finite set `S` of observed parameters, three distinct parameters
span the ambient space. When `S` has at most two elements, choose
`a,b` with `S` contained in `{a,b}`. The functional
`y2-(a+b)y1+ab*y0` annihilates every sampled column. Its value at the
first basis vector is `ab`; its value at the last basis vector is one.
Consequently the first whole file is recovered exactly when zero is
observed or at least three distinct parameters are observed. The second
whole file is recovered exactly when at least three distinct parameters
are observed.

For iid prefixes with at most two allowed types, count two-element
supersets and singleton supersets of the observed set. If the allowed
type set has size `m`, its failure indicator is the sum of pair-container
indicators minus `m-2` times the sum of singleton-container indicators,
plus `choose(m-1,2)` times the empty-prefix indicator. Actual finite
cylinders have probability equal to the total physical-index mass of the
container raised to the prefix length.

The resulting exact failure tails, including the empty prefix, are

`45(1/10)^t-80(1/20)^t+36*0^t`

and

`10(11/20)^t+45(1/10)^t-9(1/2)^t-90(1/20)^t+45*0^t`.

Summing these tails through the frozen
`retrieval_time_probability_bridge` gives the actual expectations
`E1=34/19` and `E2=767/171`. Thus
`1/E1+2/E2=26201/26078=1+123/26078>1`.

## Falsifier

The certificate would fail if the generator were rank deficient, if
either whole-file recovery characterization failed, if any physical
index multiplicity were lost in the iid law, or if the exact failure-tail
sum did not give these actual stopping-time expectations. Changing the
sampling law, information coordinates or conjecture scope cannot repair
such a failure.

## Evidence

The formal target is
`D5/S3/Resource/VandermondeHyperbolicRefutation.result : not claim`.
The sole public mathematical theorem is the full refutation. Its
field-specific negative derivation, probability and geometry proofs
are local to `result`, and it directly uses the frozen
actual retrieval bridge and coordinate-file definitions. The intended
admission basis is `open-problem-resolution` under #11729, with a
conservative `bind-only` proof-shape classification under the strict
normalization rule. No escape-witness admission or bind-only companion
theorem is claimed.

The mirrored Reg source uses the enrolled counterexample template,
extracting a finite-field witness and its negative predicate from the
full source theorem using classical `not_forall`. Its bridge retains
the full negated assertion, with law variation and slot sensitivity.
These proofs and the mathematical certificate have axiom closure
`propext`, `Classical.choice`, and `Quot.sound`. Scoped compilation
reports `E5.unsaturated_definition` at `predicate`; no current accepted
or validated binding certificate is claimed. The mathematical theorem
is not a registration-completion claim.

## Triage

The counterexample mechanism is the high sampling mass of the repeated
singleton column together with many independent quadratic-curve types.
The complementary plane waits for rank three, but its reciprocal-time
penalty does not offset the singleton advantage. The witness is
nonsystematic in the fixed file coordinates; a row-basis change would
also change those files and would not establish the original assertion.

The source's file-dedicated bound and restricted systematic results are
not contradicted. Claims about the limiting-region conjecture require
their own source-faithful field and length quantifiers; this result does
not assert an independently formalized settlement of Conjecture 3.

## ASSUMED-UNVERIFIED

The original and restricted follow-up retain the arbitrary-generator
conjecture. The bounded literature and supplier searches found no
dominating full settlement. This is not an exhaustive priority
certificate. Canonical producer output, current registration binding
evidence, normal admission, freezing and merged delivery are not
established by the mathematical source alone.
