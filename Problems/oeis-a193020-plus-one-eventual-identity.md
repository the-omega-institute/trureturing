---
slug: oeis-a193020-plus-one-eventual-identity
bibkey: layman2011a193020
doi: null
url: https://oeis.org/A193020
triage: theorem
motivation_gids:
  - D5/S1/Words/EndpointShuffleSupport.result
---

# The A193020 plus-one eventual identity

## Problem

OEIS A193020, revision 13, with the 2011 entry attribution to John W.
Layman, states the separate assertion `a(2^k+1)=k^2` with its
sufficiently-large lower-bound caveat. Here a(n), for positive n, counts
DISTINCT output words obtained by shuffling the ordinary binary expansion
of n with itself. Each shuffle preserves the order within both copies;
different schedules producing the same word contribute only once.

The exact selected assertion is

$$\exists K\in\mathbb N,\quad 1\le K\ \land\
  \forall k\in\mathbb N,\quad K\le k\ \Longrightarrow\ a(2^k+1)=k^2.$$

This dossier anchors only that plus-one question. The other identities in
A193020 are separate questions.

## Motivation

The frozen theorem `D5/S1/Words/EndpointShuffleSupport.result` retains the
eventual assertion and supplies the uniform threshold K=1. Counting the
support of the shuffle language makes the distinction between output words
and interleaving schedules essential.

## Gap

The mathematical gap is an exhaustive description of the distinct support
for an unbounded family of binary words. A finite sequence table or a
count of labelled schedules does not give that description. The source
and literature verification for this first-tier externally stated question
is the bounded scope recorded with
[issue 23034](https://github.com/the-omega-institute/trureturing/issues/23034).
No claim of worldwide openness or publication priority follows from that
scope.

## Route

For k at least one, the ordinary binary numeral of 2^k+1 is
one, k-1 zeros, one. Write m=k-1. Every distinct self-shuffle of
one, m zeros, one has the form

$$1\,0^a\,1\,0^{(m-a)+(m-c)}\,1\,0^c\,1,
  \qquad 0\le a\le m,\quad 0\le c\le m.$$

The first two ones bound a by m; the last two bound c by m. There are
2m zeros altogether, fixing the middle gap. Conversely, label the copies
A and B: take A's initial one and a zeros, B's initial one, the remaining
m-a zeros from A and m-c zeros from B, A's final one, then B's c zeros
and final one. This realizes every bounded pair while preserving both
source orders.

The output word determines a and c, so the rectangle of pairs has no
collisions. Its cardinality is (m+1)^2=k^2. Empty zero blocks are allowed,
including m=0, so the argument applies from k=1 onward.

## Falsifier

Refuting the selected eventual assertion would require counterexamples
at arbitrarily large natural exponents: for every K at least one, some
k at least K would have a(2^k+1) different from k^2. A single failure
at k at least one would refute the stronger threshold-one conclusion,
but would not by itself refute the eventual assertion. Matching a finite
prefix does not prove either conclusion.

## Evidence

`D5/S1/Words/EndpointShuffleSupport.result` has statement identity
`sha256:f4c35407fff00d562c2aaec9ad687f4c2f754a1f8c46a0948d55d80a31cffec8`.
It states the existential natural threshold and the universal tail
without additional mathematical hypotheses. Its proof chooses K=1.

The sequence definition uses the existing ordinary order-preserving
shuffle operation, then converts its output list to a finite set before
taking cardinality. For positive inputs, `binaryWord` uses the ordinary
most-significant-first binary numeral without leading zeros. Its empty
list at zero is a totalization outside the published positive-input
scope, and is not needed for the selected assertion. The accepted axiom
closure is propext, Classical.choice and Quot.sound.

## Triage

### What the settlement shows

Proved: `D5/S1/Words/EndpointShuffleSupport.endpoint_support_eq` identifies
the entire distinct support with the two-gap rectangle for every natural
m. `D5/S1/Words/EndpointShuffleSupport.endpointFamily_card` proves the
rectangle's cardinality, and
`D5/S1/Words/EndpointShuffleSupport.endpoint_self_shuffle_card` gives
the exact count (m+1)^2. The decisive mechanism is the recoverability
of the two bounded outer gaps, with the middle gap fixed by conservation
of zeros.

Proved: `D5/S1/Words/EndpointShuffleSupport.binaryWord_pow_add_one`
connects that word family to every positive exponent. Together with the
support theorem, `D5/S1/Words/EndpointShuffleSupport.result` proves the
source's eventual identity with K=1. This is an exact unbounded family,
including the boundary k=1; it does not assert a threshold at k=0.

Open here: the other special-input identities posed in A193020 remain
separate questions. In particular, the separate plus-two and minus-four
questions receive no resolution from this claim. Other binary patterns
need their own exhaustive support descriptions; the endpoint-word
rectangle alone does not supply them. The selected conclusion can be
used wherever this particular plus-one identity is a premise, but gives
no automatic change to the entry's other assertions or their truth.

## ASSUMED-UNVERIFIED

The external source identity, revision-13 interpretation and literature
limits are those of the existing source verification associated with
issue 23034 and `Library/Words/layman2011a193020.md`; no fresh external
source or literature search is asserted here. Later revisions, linked
material not read in that scope, worldwide openness and first-publication
priority are not certified. The source is credited to John W. Layman and
the OEIS contributors under CC-BY-SA-4.0. Only the separate plus-one
question is attached to the theorem's resolution claim.
