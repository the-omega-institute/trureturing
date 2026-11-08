---
slug: alekseyev-halving-partitions-nonregularity
bibkey: alekseyev2026halving
doi: null
url: https://arxiv.org/abs/2611.01243v1
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.result
---

# Halving partitions admit no finite integral decimation family

## Problem

Max A. Alekseyev, *Halving Partitions and Hyperbinary Expansions*,
[arXiv:2611.01243v1](https://arxiv.org/html/2611.01243v1), Definition 1 and
section 6, asks:

> This raises the question of whether a(n) is 2-regular: does there exist a finite family of integer sequences containing a(n) such that, for each sequence b(n) in the family, both b(2n) and b(2n+1) are integer linear combinations of sequences in the family [16]?

This dossier anchors exactly that existence question. The negative answer is
`D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.result`.
The resolution kind `Refuted` refers to the proposed existence of such a family.

### Statement echo

For every natural total n, the source carrier consists of every finite ordered
list of positive integers summing to n. With virtual predecessor p0=n, each
successive part belongs to the value set consisting of the lower and upper
integer halves of its predecessor. Equal halves give one value. Repeated parts,
arbitrary finite lengths and repeated terminal ones are retained. At zero the
empty list is the sole object.

The count a(n) is the cardinality of that independently defined carrier. Its
integer cast admits no positive finite dimension d, vector sequence F and fixed
integer matrices M0,M1 satisfying, for every n including zero,

$$
F(n)_0=a(n),\qquad F(2n)=M_0F(n),\qquad F(2n+1)=M_1F(n).
$$

The same theorem proves both directions of the matrix equivalence with finite
indexed families for every integer sequence, including arbitrary finite index
types with a distinguished member. Duplicate and dependent constituent sequences
are allowed. The distinguished member makes the family nonempty; no dimension
bound, basis assumption or invertibility condition enters the statement. The
result also identifies the actual-list count with the filtered Composition
cardinality for every n and proves a(0)=1.

## Motivation

The question asks whether finitely many integer sequence coordinates suffice
for both binary decimations. An obstruction at the dyadic successors can rule
out every such finite family without restricting its dimension or choosing a
basis among its members.

## Gap

The source poses this regularity question separately from its enumerative
results. The full actual-list count and the unrestricted family interpretation
are the target fixed by the [immutable preregistration](https://github.com/the-omega-institute/trureturing/issues/26191#issuecomment-6613963893).
A finite list table, a bounded-dimension obstruction or an eventual-input law
would leave that target unresolved. The result covers the full target; global
priority and completeness of the literature screen remain unverified.

## Route

The proof classifies every actual source list at total 2^m+1, for m at least two.
There is a unique prefix of rounded-up values followed by deterministic powers
of two and any required terminal ones. Exhaustive, injective coding gives

$$
a(2^m+1)=3+\#\{r\in\mathbb N:r\ge1,\ 2^r+r+1\le m\}\qquad(m\ge2).
$$

A finite matrix family would make u(n)=a(2^(n+2)+1) satisfy a monic forward linear
recurrence, by the integral Cayley-Hamilton theorem. Its first differences
satisfy the same recurrence. The count formula supplies arbitrarily long zero
blocks in those differences followed by another jump of one. A zero block at
least as long as the recurrence order forces every later difference to vanish,
contradicting that jump. The proof uses forward recurrence uniqueness and never
inverts a decimation matrix.

## Falsifier

A finite family with a distinguished source count and fixed integral coefficient
laws for both decimations at every natural input would contradict the result.
A faithful source mismatch would instead invalidate its application to the
paper: in particular, a missing finite list, doubled equal halves, suppressed
terminal ones or an altered zero convention would matter. The list-preserving
source equivalence and unrestricted family/matrix equivalences address these
specific interfaces.

## Evidence

The mathematical source is the Lean module
[HalvingPartitionNonregularity](../D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.lean),
with its [canonical Blueprint](../Blueprint/D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.md)
and [source bibliography](../Library/Words/alekseyev2026halving.md).
The list classification and bijection, the dyadic formula and the recurrence
obstruction are repository proofs; the paper supplies the definition and
question. Existing Mathlib Cayley-Hamilton and recurrence-uniqueness results are
used directly.

The exact-source refresh retrieved arXiv v1 HTML with SHA-256
`7fb9350d38dca0dcfbd0aa2c96de109164f624515da9008cdb72ff9ff00d7c70`;
the arXiv version listing contained only v1. The narrow external prior-result
screen supplied no usable evidence of an equivalent prior answer: Google
returned JavaScript challenges, Bing returned unrelated results, the attempted
UNCG owner locator redirected to a department homepage, and the GWU author-page
request returned HTTP 503. These limitations establish no absence or priority
claim.

## Triage

This is a theorem-level negative answer to the single source existence question.
Its resolution claim binds the complete result rather than a restricted
subproblem.

### What the settlement shows

**Proved in this module:** the independently specified whole count is not
2-regular in the source's finite integral family sense. Arbitrary finite
indexing, duplicate sequences, linear dependence and singular matrices are
already included. The exhaustive list classification yields the displayed
unbounded dyadic count formula. The forward-recurrence mechanism explains the
failure: arbitrarily long flat stretches followed by fresh jumps cannot arise
from a finite matrix family.

**Consequences of the proved mechanism:** the obstruction concerns finite
integral linear decimation families. It imposes no prohibition on recursive
counting algorithms or infinite families. It answers the question posed in
section 6 and does not refute the paper's other enumerative results. No transfer
to another base or coefficient domain is claimed.

**Computed:** no new numerical experiment or finite table is part of this
resolution claim. Finite sanity checks supply corroboration only; the all-input
conclusion comes from the unbounded proof.

**Open:** global literature priority and the author's subsequent communications
are unverified. No theorem about exhaustion of all representations or methods
is asserted; the information-escape registration retains an unknown
continuation.

## ASSUMED-UNVERIFIED

Exhaustive literature coverage and global novelty are ASSUMED-UNVERIFIED. The
source refresh and unsuccessful narrow screen do not certify either. The claim
records this repository's binding of the formal negative answer to the fixed
source question.
