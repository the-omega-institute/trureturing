---
slug: oeis-a193020-minus-four-eventual-identity
bibkey: layman2011a193020
doi: null
url: https://oeis.org/A193020
triage: theorem
motivation_gids:
  - D5/S1/Words/DoubleTailShuffleSupport.result
---

# The A193020 minus-four eventual identity

## Problem

OEIS A193020, revision 13, attributed to John W. Layman and the OEIS
contributors, states the separate assertion `a(2^k-4)=k*(k-1)/2` with its
sufficiently-large lower-bound caveat. For positive n, a(n) counts distinct
complete order-preserving self-shuffle output words of the ordinary binary
expansion of n. Different schedules producing the same word count once.

The exact selected assertion is

$$\exists K\in\mathbb N,\quad 3\le K\ \land\
  \forall k\in\mathbb N,\quad K\le k\ \Longrightarrow\
  a(2^k-4)=\frac{k(k-1)}2.$$

The OEIS entry includes a(0). The selected event uses positive inputs
throughout its tail; it does not impose a source convention at zero.
This dossier anchors only the minus-four question.

## Motivation

The frozen theorem `D5/S1/Words/DoubleTailShuffleSupport.result` proves the
whole eventual assertion with K=3. An exhaustive description of the
unbounded family's distinct support separates word cardinality from the
number of labelled interleaving schedules.

## Gap

A finite sequence table cannot establish the universal tail. The required
bridge identifies both every possible output word and a complete legal
shuffle producing each parameterized word. The source and bounded
literature scope are recorded in `Library/Digit/layman2011a193020.md`.
That inspected scope does not certify worldwide openness or priority.

## Route

For k at least three, set m=k-2. The ordinary binary expansion of 2^k-4
consists of m ones followed by two zeros. For every natural m, including
zero, the distinct self-shuffle support of this word consists exactly of

$$1^{m+(m-i)}\,0\,1^j\,0\,1^{i-j}\,0\,0,
  \qquad 0\le j\le i\le m.$$

Exhaustion describes the three runs of ones by lengths a,b,c with
a+b+c=2m and a at least m; put i=b+c and j=b. Conversely, take all m
ones from the first copy, m-i ones from the second, the first zero from
the first copy, j ones from the second, the second zero from the first
copy, then the remaining i-j ones and two zeros from the second. This
preserves both source orders and consumes both words completely.

The unary-gap uniqueness theorem recovers i and j from the output word,
including when a gap is empty. The triangular parameter set has cardinality

$$\sum_{i=0}^{m}(i+1)=\frac{(m+2)(m+1)}2.$$

Substituting m=k-2 gives k(k-1)/2 for every k at least three.
Subtraction and division in the Lean statement are natural-number
operations; the selected range supplies the stated positive numeral.

## Falsifier

A counterexample to the eventual assertion would require, for every
natural K at least three, some k at least K with a different count.
A single failure at k at least three would refute the stronger uniform
threshold-three conclusion, but would not by itself refute eventuality.
A finite matching prefix proves neither conclusion.

## Evidence

`D5/S1/Words/DoubleTailShuffleSupport.result` has statement identity
`sha256:f7d5a4314bc9231c36f1523e367338917bb5974d3b87d60343ad12017a198595`.
It retains the existential threshold, the lower bound 3 and the universal
tail without additional mathematical hypotheses; its proof chooses K=3.
The accepted axiom closure is propext, Classical.choice and Quot.sound.

`D5/S1/Words/DoubleTailShuffleSupport.self_shuffle_card` gives the exact
support cardinality for every natural m. The theorem
`D5/S1/Words/DoubleTailShuffleSupport.binary_root_original` supplies the
ordinary binary numeral bridge for every k at least three. The operation
ordinaryShuffles consumes both operands in order, and conversion to a
finite set precedes cardinality. For positive inputs, binaryWord is the
ordinary most-significant-first numeral without leading zeros. Its
empty-list totalization at zero is unused by this selected tail.

## Triage

Proved: the triangular parameterization gives both exhaustive support
and an injective construction of all outputs. Together with the ordinary
binary numeral bridge, it proves this exact unbounded minus-four family
and the whole eventual assertion with K=3.

The plus-one assertion has its own existing theorem and dossier. Other
A193020 assertions remain separate questions; this resolution claim
supplies no automatic conclusion about them.

## ASSUMED-UNVERIFIED

The external source identity, revision-13 interpretation and bounded
literature limits are those recorded in the library note. No fresh
external search is asserted here. Restivo's full chapter, the Li-Qin and
Guo-Xie journal bodies, uninspected Datko-Pawlik tables and displayed
lists, remaining citation branches, and broader or unindexed work were
not read. Later revisions, worldwide openness and first-publication
priority are not certified.

The count definition and eventual assertion are credited to John W.
Layman and the OEIS contributors under CC-BY-SA-4.0. The support proof
is from this repository, with source acknowledgement. Only this separate
minus-four question is attached to the theorem's typed resolution claim.
