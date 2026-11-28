---
slug: guo-pan-wang-du-2026-set-imaginarity-conjecture-1
bibkey: guopanwangdu2026setimaginarity
doi: 10.1103/1yc6-lzfk
url: https://arxiv.org/abs/2608.28985v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/SetImaginarity/PrintedConjecture.result
  - D5/S3/Quantum/Information/SetImaginarity/TraceWordDetection.result
---

# Guo–Pan–Wang–Du Conjecture 1 on set imaginarity

## Problem

In Appendix C, page 11, of *Measure of set imaginarity*, Conjecture 1 says
that a family “is set imaginarity free if and only if” some ordered product
of length $3\le k\le d(d+1)/2$ has trace with nonzero imaginary part.
Here a free family admits one unitary $U$ for which all $U\rho_jU^\dagger$
are entrywise real. The family consists of at least three distinct
positive semidefinite, trace-one complex matrices in dimension $d\ge 2$.
Write $F$ for the common-real-basis property and $B$ for the existence of
the bounded nonreal trace word. `PrintedConjecture.claim` asserts the
printed $F\iff B$. [Versioned preprint](https://arxiv.org/pdf/2608.28985v1)

## Motivation

A nonreal trace word detects the absence of a common real basis. Trace
is invariant under simultaneous unitary conjugation, and a product of
real matrices has real trace. The surrounding discussion suggests the
criterion $\neg F\iff B$, whose converse detection direction is
$\neg B\Rightarrow F$. `TraceWordDetection.claim` tests this direction
for four states in dimension four with the stronger premise that the
trace is real for every word of every length.

## Gap

The search recorded in the preregistration found no exact prior settlement
in the checked repository records and related literature. Li, Wagner and
Zhang give a triplet criterion for qubit families in Corollary III.7 and
a dimension-four example detected by a fourth-order invariant. The
dimension-four result here concerns real traces at every length.
Miyazaki and Matsumoto's Theorem 1 on common antiunitary symmetries is
related literature. Its hypotheses and proof are outside the settlement.
`not-found-in-searched-scope`. [Preregistration #35040](https://github.com/the-omega-institute/trureturing/issues/35040) · [Literature note](../Library/HilbertOperators/guopanwangdu2026setimaginarity.md)

## Route

1. For the printed biconditional, take the three diagonal qubit states
   with diagonals $(3/4,1/4)$, $(1/4,3/4)$ and $(1/2,1/2)$. They are
   distinct and have positive entries and trace one. The identity gives
   $F$, while every ordered word is real and hence $B$ fails.
2. For the all-word implication, take the Pauli matrices $X,Y,Z$ with
   $Y_{12}=-i$. The four generators $G_j$ are $Z\otimes I_2$, $X\otimes I_2$,
   $Y\otimes X$ and $Y\otimes Z$. Each is a traceless Hermitian involution.
   The four distinct states $(2I_4+G_j)/8$ have trace one and are positive
   definite by the Gram decomposition $I_4/8+(I_4+G_j)^\dagger(I_4+G_j)/16$.
3. Put $Q=I_2\otimes J$, where $J$ has rows $(0,1)$ and $(-1,0)$. Each state
   satisfies $\rho_j Q=Q\overline{\rho_j}$. Induction gives the same relation
   for each ordered word. Since $Q^{-1}=-Q$, cyclicity of trace identifies
   the trace of each word with its complex conjugate.
4. A unitary $U$ giving a common real basis would produce a symmetric
   unitary $C=U^\dagger\overline U$ with $G_j C=C\overline{G_j}$. The first two
   generators force $C=I_2\otimes M$. The last two force $M$ to anticommute
   with $X$ and $Z$, yielding $M=bJ$. Such a $C$ is skew-symmetric, so its
   symmetry forces it to be zero, contradicting unitarity.

## Falsifier

The Lean statements use one common unitary, actual density matrices,
and traces of products in increasing word-position order. The printed
claim uses the inclusive length bound and the printed polarity. The
all-word claim quantifies over arbitrary words, including repeated
letters. At dimension four the source window is $3\le k\le10$, so the
all-word witness also falsifies $\neg B\Rightarrow F$ in that window.
Restricting the allowed words to distinct letters preserves both witnesses.

## Evidence

- `PrintedConjecture.result : ¬ claim` is the designated refutation of the
  printed biconditional. It uses the open-problem-resolution admission
  basis. [Lean](../D5/S3/Quantum/Information/SetImaginarity/PrintedConjecture.lean) · [Blueprint](../Blueprint/D5/S3/Quantum/Information/SetImaginarity/PrintedConjecture.md) · [Frozen state](../Golden/Frozen/state/D5/S3/Quantum/Information/SetImaginarity/PrintedConjecture.lean.json)
- `TraceWordDetection.result : ¬ claim` is the designated refutation of the
  separately stated all-word implication. The induction on words and the
  classification of common intertwiners supply the content of its proof.
  [Lean](../D5/S3/Quantum/Information/SetImaginarity/TraceWordDetection.lean) · [Blueprint](../Blueprint/D5/S3/Quantum/Information/SetImaginarity/TraceWordDetection.md) · [Frozen state](../Golden/Frozen/state/D5/S3/Quantum/Information/SetImaginarity/TraceWordDetection.lean.json)
- Both results use the pinned Mathlib backend and the axiom closure
  `Classical.choice`, `Quot.sound` and `propext`. Each is the sole public
  theorem of its module and is exempt from four-slot escape registration
  as the designated typed refutation.

## Triage

Tier 1, `theorem`, resolution `refuted` for Conjecture 1 as printed in
arXiv v1. The all-word sufficiency implication is a separate refutation.
The counterexample rules out detecting every nonfree family by checking
trace words, even with no length bound. The implication from a nonreal
word to the absence of a common real basis follows by the trace argument
above.

## ASSUMED-UNVERIFIED

The journal DOI and publication metadata were verified. The journal
full-text wording and exhaustive literature priority remain unverified.
