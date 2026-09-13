---
slug: shin-four-point-sumset-compression
bibkey: shin2026iterated
doi: 10.48550/arXiv.2609.01690
triage: theorem
motivation_gids:
  - D5/S0/Certificates/FiniteExhaustion
---

# Shin's four-point sumset compression question

## Problem

For every natural h>=2, put D_h=choose(h+2,2)+1 when h is odd, and
D_h=choose(h+2,2) otherwise. Must every four-element integer set A have
a four-element integer set B in [0,D_h] with |hB|=|hA|? Here hA is the set
of sums of exactly h elements of A with repetitions allowed. This is the
question after Corollary 10.5 and equation (193) in arXiv:2609.01690v1,
equivalently nu(h,4)=D_h for all h>=2. It is restated as open in
arXiv:2609.08915v1, Question 12.5.

## Motivation

FiniteExhaustion provides the existing setting for complete finite
certificate arguments. This source question has an unbounded universal
statement, but one cardinality absent from a bounded interval suffices
to refute its affirmative answer.

## Gap

The question preserves only cardinality. A failure to preserve a complete
additive relation type would not answer it. The obstruction must therefore
exclude every four-element set in the proposed interval, including sets
with nontrivial common divisors and unnormalized translates.

## Route

Use h=11 and A={0,7,17,80}, whose repeated sumset has 347 elements.
Order an arbitrary B in [0,79], subtract its least element, and obtain
0<a<b<c<=79 without changing the repeated-sum cardinality. A bitset
recurrence starts at {0} and takes the union with its shifts by a,b,c
eleven times. Its kernel-verified interpretation is the actual sumset.
Its cardinality excludes 347 for all 79,079 normalized triples.
The designated Lean result is Not claim for the full universal proposition.

## Falsifier

Any normalized triple 0<a<b<c<=79 with count 347 invalidates the finite
obstruction. A different witness cardinality, an incomplete normalization,
or interpreting scalar images as repeated sums also invalidates it.
The kernel proofs address each of these mathematical possibilities.

## Evidence

The source definition and question are pinned in
Library/Certificates/shin2026iterated.md; the independent restatement is in
Library/Certificates/zhang2026sharp.md. The intended full result is
D5/S0/Certificates/ShinFourPointCompression.result, negating its claim.
The finite exclusion was kernel checked with only propext, Classical.choice
and Quot.sound. Definitions, count soundness, normalization and the full
negation are assembled in that single module.

## Triage

`theorem`: a concrete finite obstruction with a full source-negation target.
Neither a stronger equality nu(11,4)=80 nor positive cases at other h are
part of the claimed result.

## ASSUMED-UNVERIFIED

The bounded public searches found no prior matching solution; they do not
prove first-publication priority or exhaust all literature. The kernel
cannot prove correspondence with natural-language source text. Independent
fidelity review, the canonical delivery gates, freeze/resolution binding,
and merged delivery remain required before counting a solved problem.
