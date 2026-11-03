---
slug: chern-fu-improper-partition-matrix-fixed-image
bibkey: chernfu2026signed
doi: 10.48550/arXiv.2508.21318
url: https://arxiv.org/abs/2508.21318v2
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/PartitionMatrix/ChernFuImage.result
---

# The fixed CDK image of improper partition matrices

## Problem

Shane Chern and Shishuo Fu, *Signed counting of partition matrices*,
arXiv:2508.21318v2, Section 5, Question 5.5, page 26:

> Find a characterization (possibly in terms of pattern avoidance) of the inversion sequences produced by improper partition matrices under the action of the Claesson–Dukes–Kubitzke bijection.

For each integer $n\geq1$, write $[n]=\{1,\ldots,n\}$ and let
$\mathbf I_n=\{e:[n]\to\mathbb N:0\leq e_j\leq j-1\text{ for all }j\in[n]\}$.
A native partition matrix on $[n]$ is an upper triangular square matrix $P$ of
sets, of any permitted positive dimension $k$, whose nonempty cells partition
$[n]$, every row and column is nonempty, and
$\operatorname{col}_P(a)\leq\operatorname{col}_P(b)$ whenever $a<b$.
The row and column of a label are those of its unique cell.

An adjacent pair $i,i+1$, with $1\leq i<n$, is an ascent or descent only when
its labels share a column and have respectively increasing or decreasing row
indices. Such a pair is proper precisely when $i$ has the parity of the least
label of that column. An improper matrix has no proper ascent or descent;
equal-row pairs are neither. Write $\operatorname{IPPM}_n$ for this class.

The fixed source map is

$$
\Pi_n(P)_j=\sum_{d=1}^{\operatorname{row}_P(j)-1} n_d,
\qquad n_d=\sum_{r=1}^{k}|P_{r,d}|.
$$

Thus the summands are column cardinalities, and the sum is zero in the first
row. The requested image uses this map and all permitted dimensions.

## Motivation

The source's natural CDK map does not send the improper matrices to the
restricted inversion sequences in its Theorem 1.4. A condition on the image
sequence itself identifies what that fixed map retains, independently of
constructing another equinumerous family or another bijection.

The theorem `D5/S3/Combinatorics/PartitionMatrix/ChernFuImage.result` proves
for every $n\geq1$ and every $e\in\mathbf I_n$ that

$$
e\in\Pi_n(\operatorname{IPPM}_n)\quad\Longleftrightarrow\quad\Phi_n(e),
$$

where the entire alphabet and its preceding value are

$$
A(e)=\{e_j:j\in[n]\},\qquad
b_e(i)=\max\bigl(\{0\}\cup\{a\in A(e):a<i\}\bigr),
$$

and the criterion is

$$
\Phi_n(e):\quad
\forall i\in\{1,\ldots,n-1\},\quad
\bigl(i\notin A(e)\ \land\ i-b_e(i)\text{ odd}\bigr)
\ \Longrightarrow\ e_i=e_{i+1}.
$$

The alphabet ranges over all positions. For $n=1$ the adjacent-index condition
is vacuous. There is no monotonicity, pattern-class or dimension restriction
on the inversion sequence or its matrix preimage.

## Gap

The prospectively fixed full contract is
[issue 22554, immutable registration](https://github.com/the-omega-institute/trureturing/issues/22554#issuecomment-6430275063).
The ordinary Claesson–Dukes–Kubitzke correspondence is an attributed supplier,
not a Lean axiom. The formal mathematical bridge consists of native matrix
validity, the exact fixed column-cardinality map, and both directions of the
whole-alphabet criterion. These are proved in the named result.

Version v1 Question 5.5 is numbered Question 5.7 in v2 and asks for a different
statistic-preserving minus-class bijection. It is not the present contract.
The bounded source and ownership screen found no identical fixed-image
characterization in the inspected materials; it does not establish worldwide
priority or exhaustive absence of a previous answer.

## Route

Let $A(e)=\{y_1<\cdots<y_k\}$ and set $y_{k+1}=n$. The CDK reconstruction
has cells

$$
P_{r,c}=\{t:e_t=y_r,\ y_c<t\leq y_{c+1}\}.
$$

Inversion bounds alone make this an upper triangular native partition matrix,
with every row and column nonempty. Its column $c$ is the interval
$\{y_c+1,\ldots,y_{c+1}\}$, and preceding column cardinalities telescope to
$y_r$. Consequently its fixed image is exactly $e$.

For an arbitrary native matrix, monotone column indices make the labels before
a column an initial segment. The alphabet of its fixed image is precisely the
set of column starts minus one. Thus adjacent labels $i,i+1$ share a column
exactly when $i$ is absent from that alphabet; its least label is $b_e(i)+1$.
Strictly increasing column cuts make equality of the two rows equivalent to
equality of the two image entries. Proper parity is precisely oddness of
$i-b_e(i)$. Excluding both proper strict row orders therefore gives $\Phi_n$.
This proves necessity for every native matrix; applying it to the reconstruction
proves sufficiency.

The Lean carrier `NativePM n k` is the literal square set-entry matrix on
`Fin n`. `nativeEquiv` proves both matrix/coordinate round trips, including
all cells. A native label $j$ corresponds to Fin index $j-1$; a length-$n$
list represents the same entire inversion sequence. No CDK bijection or
improperness implication is assumed as a premise.

## Falsifier

A counterexample to this exact contract would be an integer $n\geq1$ and
$e\in\mathbf I_n$ for which exactly one of fixed-image membership and
$\Phi_n(e)$ holds. A finite cutoff, one implication, an equinumerosity result,
a different bijection or a restricted subclass would not answer the question.
The named unrestricted theorem excludes such a counterexample in the stated
formalization; source correspondence is an additional content-review obligation.

## Evidence

**Proved:** `D5/S3/Combinatorics/PartitionMatrix/ChernFuImage.result`, with
standard axioms `Classical.choice`, `Quot.sound`, and `propext`. Its statement
quantifies over every positive $n$, every length-$n$ inversion sequence and an
unrestricted native preimage dimension. The corresponding Blueprint contains
the native definitions, fixed map, criterion, reconstruction and complete iff.
No numerical enumeration is used as proof.

The primary Chern–Fu v2 PDF and HTML give Definition 1.1, the fixed map after
Theorem 1.2, Definition 2.1 and Question 5.5. The original CDK source,
arXiv:1006.1312v2, Section 2, Definition 2 and Theorem 3, supplies the ordinary
alphabet-rank construction and its inverse. Both sources are citation-only;
no third-party implementation is copied.

The inspected public [EULER partition-matrix case](https://github.com/randomcat4/euler-combinatorics-conjecture-cases/tree/e7e04318fa1d0dd4233237610618c34adda5dc97/cases/partition-matrix-bijection)
contains the matrix column-pair characterization and a Q5.7 minus-class
bijection, with a six-page extension to full classes through cyclic partitions.
Those existing matrix-side ingredients are not claimed as new research here.
Its stated maps and theorems do not characterize the original fixed $\Pi_n$
image. The bounded checks also include the title/source-id/native-phrase
repository searches recorded in issue 22554, the cited counting records and
completed thesis-source check; these earlier search conclusions are supplied
reports, not an exhaustive literature certificate. The current arXiv abstract
lists v1 and v2; the journal full text and complete forward-citation graph were
not verified.

The Reg mirror compiles, but its source/readout binding audit is
**declared_unresolved**, with no certificate: [issue 22576](https://github.com/the-omega-institute/trureturing/issues/22576).
The diagnostic is `IE-C050 ClosedTruthReadout`, `forbidden_dependency`,
`source.unsafe_or_external`, `Nat.decLt; source_operand=Nat.decLt`.
This is the linked-issue exception for an unfinished audit, not a validated
registration or an additional mathematical assumption.

## Triage

Theorem route: the full native characterization is proved by the named GID.
No new substantive research unit is assigned to the short ordinary argument,
its formal bridge, its implications or parameter cases.

### What the settlement shows

**Proved** (`D5/S3/Combinatorics/PartitionMatrix/ChernFuImage.result`): the
information needed for this fixed image is the sequence's entire alphabet,
the preceding occurring value at each absent boundary, and the indicated
adjacent-entry equalities. The necessity argument holds for every native
matrix and dimension; the sufficiency construction assumes only the original
inversion bounds and the displayed criterion.

The criterion covers nonmonotone inversion sequences and the $n=1$ endpoint.
No finite pattern-avoidance basis, running-time bound, stronger generalization,
or new result for Question 5.7 is asserted. The source's signed-counting and
statistic-preserving bijection questions are not replaced or re-proved by this
image characterization. No successor conjecture is evaluated or registered.

## ASSUMED-UNVERIFIED

Global novelty, complete citation coverage and clause identity with the
inaccessible journal full text are unverified. The Reg binding certificate
remains unresolved under issue 22576. Independent postdoor review, exact-head
required CI and delivery to dev remain publication obligations; the mathematical
GID and the Scribe resolution binding alone do not establish those outcomes or
an external-resolution count.
