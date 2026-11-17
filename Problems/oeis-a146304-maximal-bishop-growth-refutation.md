---
slug: oeis-a146304-maximal-bishop-growth-refutation
bibkey: bonzini2008a146304
doi: null
url: https://oeis.org/A146304
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/Domination/BishopMaximalPlacementGrowth.result
---

# Maximal bishop placements exceed the conjectured growth bound

## Problem

The Online Encyclopedia of Integer Sequences, A146304, authored by Paolo
Bonzini, defines the native objects as follows:

> Number of distinct ways to place bishops (up to 2n-2) on an n X n chessboard so that no bishop is attacking another and that it is not possible to add another bishop.

Its conjectured formula is:

> Conjectured to be a(n) = O(n^(n-1)).

Let $a(n)$ count all unordered subsets of the fixed-coordinate board
$\operatorname{Fin}(n)\times\operatorname{Fin}(n)$ that are nonattacking and
maximal under inclusion. Distinct cells attack when their integer coordinate
differences or their coordinate sums agree. There is no symmetry quotient,
prescribed size, or requirement of maximum cardinality. The physical cap
$2n-2$ holds for $n\ge2$; the one-square board has $a(1)=1$. The offset is one,
and the total formal convention at zero is outside the source sequence.

The complete conjecture is

$$\exists C\in\mathbb R,\quad C>0\ \land\
\exists N\in\mathbb N,\quad N\ge1\ \land\
\forall n\in\mathbb N,\quad n\ge N\ \Longrightarrow\
a(n)\le Cn^{n-1}.$$

The refutation retains every positive real constant and every natural cutoff
$N\ge1$: some $n\ge N$ satisfies $a(n)>Cn^{n-1}$.

## Motivation

This is the complete asymptotic assertion preregistered in
[issue 30272](https://github.com/the-omega-institute/trureturing/issues/30272).
Counting actual maximal subsets keeps the conclusion attached to the published
sequence. A finite table cannot decide its eventual growth bound.

## Gap

The immutable OEIS export retains the conjectured formula. The bounded
source and prior-work comparison is recorded in the Library note
`Library/FiniteGeometry/bonzini2008a146304.md` and issue 30272. No complete
settlement was located in that inspected scope; this is not an exhaustive
literature or priority certification.

The Lean construction closes the mathematical gap for the stated native
count. Two information-audit registrations remain unfinished under the
issue-linked exception: the physical cap needs complete original-telescope
variation, sensitivity and native placement-size dependence evidence; the
generic prefix theorem needs lawful reconstruction of its entire
universe-polymorphic and typeclass telescope with dependence evidence.
Neither residual is an assumed mathematical hypothesis.

## Route

For a finite vertex type $V$, prescribed finite lines $L_j$, and a label map
$c:V\to W$ injective on each line, count actual tuples on the first $k$ lines
whose labels are distinct. If $|L_j|\ge m+j$ for every $j<K$, a fixed legal
prefix of length $j$ forbids at most $j$ vertices on the next line. Thus every
prefix has at least $m$ extensions. Injectively appending a choice and summing
the dependent extension fibers gives at least $m^K$ tuples.

Use the single board of side $4m+1$. In each of its two diagonal parities,
order the noncentral difference lines by length and select the fixed $3m$
lines at one-based positions $m+1,\ldots,4m$. For zero-based $j<3m$, the
selected line has at least $m+j$ cells. Its sum labels are injective, so the
prefix bound gives at least $m^{3m}$ choices per color. The two colors have
disjoint sum labels and disjoint difference labels on the same board.

Each combined seed extends to an inclusion-maximal independent set by direct
application of the frozen finite maximal-extension theorem. On every selected
difference line, independence forbids adding any cell besides the chosen
one. Restriction to these fixed lines therefore recovers every seed
coordinate from its maximal completion. This proves the injection and the
uniform bound

$$a(4m+1)\ge m^{6m}\qquad(m\in\mathbb N).$$

For $m\ge50$, the inequalities $4m+1\le5m$ and
$2500\le m^2$ imply

$$4(5m)^4=2500m^4\le m^6.$$

Raising to the power $m$ and applying the counting bound yields

$$4^m(4m+1)^{4m}\le a(4m+1).$$

Given $C>0$ and $N\ge1$, choose $m\ge50,N$ with $4^m>C$.
Then $n=4m+1\ge N$, its comparison factor $n^{n-1}=n^{4m}$ is positive,
and the displayed bound gives the required strict violation.

The physical cap is also proved on the native board. Difference labels have
$2n-1$ possible values. Their two extreme lines are singleton corners with
the same sum, so an independent placement omits at least one extreme label.
Filtering by the cap for $n\ge2$ therefore preserves the count used by the
complete refutation, including the separate one-square boundary.

## Falsifier

A faithful proof of the complete eventual upper bound for this same native
count would contradict the refutation. A legal prefix with fewer than $m$
extensions under the stated line-size hypotheses, an attack between the
two parity classes, or two different seeds with the same maximal completion
would invalidate the corresponding construction step. Counts of symmetry
classes or maximum-size placements address different objects.

## Evidence

The resolution declaration is
`D5/S3/Combinatorics/Graph/Domination/BishopMaximalPlacementGrowth.result`,
with literal type `Not claim`; `claim` has literal type `Prop`. Its live
dependencies include `physical_cap`, `source_family_card`,
`count_lower_bound`, `ratio_lower_bound`, and the generic
`FiniteLinePrefixCount.card_prefix_lower_bound`. The source family is a
finite filter of actual native maximal placements, and the prefix count
uses actual tuples and their dependent extension fibers.

The native maximal-extension supplier is
`D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.lean`, frozen at
module statement identity
`sha256:63ac37387df3873c734bdadbe438736b14550e0de7614868c6f1ce0fb80857a2`.
It is applied directly. The retained Reg mirror supplies whole-law proof
terms for the lower bound, ratio bound and source-family dictionary; the
two audit residuals above remain linked to issue 30272. The designated
refutation result is exempt from that registration requirement.

The immutable [official export](https://raw.githubusercontent.com/oeis/oeisdata/847798eafedfc5f486a00619e2926cfdb6bf73f9/seq/A146/A146304.seq)
has 2956 bytes and SHA256
`509a91a92cbf9c31dd6d18e357fd4d3ce6285d05a3b380f0f3652231292fc65b`.
The quotations are attributed to OEIS and its named contributors under
[CC-BY-SA 4.0](https://oeis.org/wiki/The_OEIS_End-User_License_Agreement?oldid=1653353).
No separate formula author is supplied. Andrew Howroyd is credited for
algorithms and tables, not for this conjecture. Source locators and the
bounded prior-work distinctions are in the Library note. The Lean proof
and its exposition are independently authored; no third-party algorithm
or Lean implementation is copied.

## Triage

`theorem`. The single resolution claim belongs to the complete original
A146304 growth conjecture. The generic prefix bound, physical cap,
source-family dictionary and ratio estimate are supporting results, with
no separate external-problem credit. The argument proves an unbounded
family of violations and does not assert an exact asymptotic equivalent
or a replacement enumeration formula.

## ASSUMED-UNVERIFIED

The interpretation of the OEIS prose as the native board model is a
source-faithfulness judgment. The bounded source screen does not establish
worldwide novelty, absence of every earlier proof, or publication priority;
subscription-blocked texts are not claimed as firsthand full-text evidence.
The two named information-audit registrations remain unfinished under
issue 30272. Successful scoped production and emission do not assert a
successful full content-check or current check; the scoped-reader boundary
is tracked in [issue 29739](https://github.com/the-omega-institute/trureturing/issues/29739).
