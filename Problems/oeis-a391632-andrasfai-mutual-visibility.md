---
slug: oeis-a391632-andrasfai-mutual-visibility
bibkey: howroyd2026a391632
doi: null
url: https://oeis.org/A391632/internal
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiActual
---

# Howroyd's full Andrasfai mutual-visibility generating function

## Problem

OEIS A391632, revision 27, attributes this assertion to Andrew Howroyd:

> Conjectured g.f.: x*(4 - 19*x + 33*x^2 - 40*x^3 + 8*x^4)/(1 - 10*x + 29*x^2 - 32*x^3 + 8*x^4).

The entry's name is "Number of mutual-visibility sets in the n-Andrásfai
graph" and its offset is 1,1. For every integer $n\ge1$, let $G_n$ be the
simple undirected Cayley graph on the labelled vertices
$\mathbb Z/(3n-1)\mathbb Z$, with connection set
$\{1,4,\ldots,3n-2\}$. A subset $S$ is mutual-visible when every distinct
pair $u,v\in S$ admits a shortest $u$-$v$ path in the original host $G_n$
whose internal vertices avoid $S$. Different pairs may choose different
paths. Let $a(n)$ count every such labelled subset, including the empty set
and singletons. The entire question is the identity in $\mathbb Q[[X]]$

$$
\sum_{n\ge1}a(n)X^n
=\frac{X(4-19X+33X^2-40X^3+8X^4)}{1-10X+29X^2-32X^3+8X^4}.
$$

The series has constant coefficient zero; no graph of index zero is
introduced. There is no quotient by graph symmetries, maximality,
independence or induced-host restriction. The quotient denotes
multiplication by the formal inverse of a series with constant coefficient
one, without an analytic convergence premise.

### Statement correspondence

Put $m=n-1$ and $N=3m+2=3n-1$. `Andrasfai.host m` uses `ZMod N`, with
adjacency determined by the canonical representative of $v-u$ being one
modulo three. `Andrasfai.count m` is the cardinality of the original
`Configuration (host m)` subtype of actual finite vertex subsets.
`AndrasfaiActual.generatingSeries` is defined directly as
$X\operatorname{mk}(m\mapsto(\operatorname{count}(m):\mathbb Q))$.
`AndrasfaiActual.result` has no hypotheses and states the displayed
identity for that series.

## Motivation

This is a named whole-family enumeration problem. The central issue is
whether all original-host feasible subsets, with their labels retained,
are counted by a finite-state trace. Rationality alone, an eventual
recurrence, or agreement of finitely many coefficients does not settle the
question.

## Gap

The source calls the full expression conjectural. The bounded source and
literature scope in issue 22305 includes the original entry, its linked
graph and visibility definitions, and nine arXiv HTML versions concerning
mutual visibility. No exact full-identity proof supplier was identified in
that scope. The available graph model and matrix-walk summation theorem
supply carriers and counting machinery, rather than the required
original-subset/periodic-word correspondence.

## Route

Original-host shortest paths reduce to common-neighbor obstructions.
Arithmetic in the cyclic host identifies those obstructions with the whole
cyclic forbidden-factor family. Canonical membership labels give an
invertible encoding of actual subsets, and the forbidden-factor argument
handles factors crossing the labelled origin or spanning many periods.

The finite-word language avoids $11(\Sigma\Sigma1)^*1$, where
$\Sigma=\{0,1\}$. A five-state DFA has four nonrejecting states. At lengths
not divisible by three, periodic avoidance gives exactly one closed
nonrejecting starting state. A labelled-walk induction counts every Boolean
label separately, including both labels on the same transition. In the
nonrejecting state order the transfer matrix is

$$
M=\begin{pmatrix}1&1&0&0\\1&0&1&0\\0&0&0&1\\0&2&0&0\end{pmatrix}.
$$

Consequently the actual subset count is $\operatorname{tr}(M^{3m+2})$ for
every $m\ge1$. The original $m=0$ graph has two vertices and four actual
subsets, whereas $\operatorname{tr}(M^2)=3$. Thus exactly $X$ must be added
to the trace series. A uniform matrix-power recurrence and formal-series
coefficient argument yield the full displayed numerator and denominator.
No count/trace bijection is assumed.

## Falsifier

A discrepancy at any original $n\ge1$ in the exact count of all actual
labelled mutual-visibility subsets would contradict the stated identity.
A failure of a stronger automaton-lift statement at other lengths or for a
different host would not by itself refute this question. Finite agreement
and a program generated from the conjectured series are not proofs.

## Evidence

The unconditional theorem is
`D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiActual.result`.
`AndrasfaiWords.visible_iff_word_periodic_avoidance`,
`AndrasfaiEnumeration.periodic_word_card_eq_trace`, and
`AndrasfaiActual.count_eq_trace` provide the exact intervening
correspondences. `AndrasfaiWords.count_zero` supplies the original first
coefficient. The axiom closure of every public declaration is contained
in {propext, Classical.choice, Quot.sound}.

The source note is `Library/GraphInvariants/howroyd2026a391632.md`.
No experimental program or fitted coefficient list is used as proof.

## Triage

### What the settlement shows

Proved: `AndrasfaiActual.result` establishes the entire original formal
series, including the first coefficient four. The decisive mechanism is
the original-host obstruction/periodic-word correspondence, the unique DFA
lift, and preservation of labelled-edge multiplicity. The explicit $+X$
correction is necessary for the original index-one convention.

Proved: `AndrasfaiLanguage.accepts_iff_avoids` concerns every finite Boolean
word. `AndrasfaiLanguage.exists_unique_closed_run` applies whenever its word
length is not divisible by three. `AndrasfaiCounting.closed_run_card_eq_trace`
counts closed labelled runs at every positive length, and
`AndrasfaiEnumeration.periodic_word_card_eq_trace` identifies periodic-word
cardinality with the trace at every positive length not divisible by three.
These scopes extend beyond the graph lengths needed by the identity.

Open: uniqueness at lengths divisible by three, alternative Cayley
connection sets, other visibility notions, and symmetry-quotiented counts
require separate statements and arguments. The present graph counting
formula asserts none of these extensions.

Source scope: no other theorem or follow-up question dependent on this
conjecture was identified in the inspected OEIS entry. The full identity
settles its exact count-series question; no additional external resolution
is asserted.

## ASSUMED-UNVERIFIED

The bounded literature search does not establish worldwide absence of an
earlier proof or first-publication priority. Publisher-final versions and
all historical OEIS revisions were not exhaustively compared. The
source-to-Lean correspondence uses the original-host shortest-path meaning
and labelled subset convention stated above; mathematical compatibility
does not imply any claim about a different graph or visibility notion.
