---
slug: de-bievre-2022-noncommuting-not-coinc-all-dimensions
bibkey: debievre2023incompatibility
doi: 10.1063/5.0110267
url: https://arxiv.org/abs/2207.07451v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurements/NoncommutingNotCompletelyIncompatible.result
---

# Strong noncommutativity without complete incompatibility in every dimension at least four

## Problem

Stephan De Bièvre, arXiv:2207.07451v1, §5, conjecture following Proposition 7:

> We conjecture it is true that (ii) does not imply (i) in all dimensions
> $d\geq4$, but we have not produced such examples in other dimensions than
> $4$ and $6$.

The space is $\mathbb C^d$ and the bases are arbitrary orthonormal bases.
Condition (ii) says that every pair of coordinate orthogonal projectors
indexed by nonempty proper sets fails to commute. Condition (i), complete
incompatibility, says that their images have zero intersection whenever
the two index-set cardinalities sum to at most $d$; empty sets are included.
Issue #11785 preregisters the exact quantified statement before any Lean.

## Motivation

`D5/S3/Quantum/Measurements/NoncommutingNotCompletelyIncompatible.result`
proves that for every natural $d\geq4$ there exist two complex orthonormal
bases satisfying (ii) and failing (i). This settles the quoted conjecture
as **Proved**, while the assertion that (ii) implies (i) fails in that range.
The source's $1,\ldots,d$ indices are relabelled by `Fin d`.

## Gap

The source provides examples in dimensions four and six. The target is a
uniform construction for every dimension at least four, with the universal
quantifiers over both nontrivial index sets retained. An example in one
dimension, pairwise noncommutativity of rank-one projectors alone, or a
real-only statement would not close that gap.

## Route

Use the standard complex orthonormal basis and the columns of the real
Householder reflection

$$
w=(1,2,\ldots,2),\qquad q=w^T w=4d-3,\qquad
H=I-\frac{2}{q}ww^T.
$$

The identities $H^2=I$ and $H^*=H$ give an orthonormal basis over
$\mathbb C$. For a nonempty proper set $T$, put
$m=\sum_{k\in T}w_k^2$, so $0<m<q$. For $i\ne j$, its coordinate projector
has entry

$$
(HP_T H)_{ij}=\frac{2w_iw_j}{q^2}
\bigl(2m-q(1_T(i)+1_T(j))\bigr).
$$

This entry is nonzero: indicator sums zero and two use the strict mass
bounds, while indicator sum one uses the odd integer $q$. For a nonempty
proper $S$, choose $i\in S$ and $j\notin S$. The commutator entry equals
this nonzero entry. For the failure of (i), take $S=T=\{0,1\}$ and
$z=2e_0-e_1$. Then $z\ne0$, $w^Tz=0$, and $Hz=z$, so $z$ lies in both
selected two-coordinate spans and $|S|+|T|=4\leq d$.

## Falsifier

The settlement fails if the reflected columns are not complex orthonormal,
if a nonempty proper pair of index sets has commuting projectors, or if the
chosen common vector is zero or not in both spans. The Lean proof checks
all of these obligations at arbitrary natural dimension at least four.
A verified prior settlement would invalidate the literature-based admission
premise, without invalidating the kernel-checked mathematical statement.

## Evidence

The module imports pinned `Mathlib.Analysis.InnerProductSpace.PiL2`. Its public
surface is `projector`, `NonCommutingProjectors`, `CompletelyIncompatible`,
`claim`, and the single theorem `result : claim`. The construction and its
intermediate facts are local to `result`; there are no companion theorems.
The accepted axiom boundary is `propext`, `Classical.choice`, and `Quot.sound`.
Canonical freeze and declaration identities are maintained by the door.

## Triage

Tier 1: an explicit conjecture of a quant-ph paper, with a bounded literature
check recorded in #11785. `proof_shape: bind-only`; the basis construction,
finite-sum identities and parity calculations use pinned upstream facts and
normalization. `admission_basis: open-problem-resolution`; `utility: none`.
The result is not presented as a new upstream theorem or an exhaustive
priority determination.

### What the settlement shows

**Proved in this module:** `result` establishes the separation between
strong noncommutativity and complete incompatibility for every $d\geq4$.
Its live proof constructs a real orthogonal transition matrix inside the
complex space, makes every off-diagonal entry of every nontrivial reflected
projector nonzero, and supplies a fixed nonzero common vector on two
coordinates. Thus a common state of two coarse projectors can coexist with
noncommutativity of every nontrivial pair; their action on that common state
alone does not decide whether the operators commute.

**Proved within the proof of `result`:** the noncommutativity calculation
requires only $d>0$; for $d=1$ the nontrivial-set quantifier is empty. The
failure of complete incompatibility uses two coordinates from each basis
and is admitted by its cardinality test precisely when $4\leq d$. No
additional public theorem or stronger settlement is claimed.

**Source result, not proved here:** Proposition 7 states equivalence of (i)
and (ii) in dimensions two and three. Those statements, and its forward
implication (i) ⇒ (ii), are compatible with this settlement. The dimension
threshold four is therefore sharp relative to that proposition. The last bullet of Proposition 7, whose counterexamples cover dimensions
four and six, extends to every dimension at least four by `result`. The
paper's results that assume complete incompatibility keep that assumption: the
settlement supplies no replacement of (i) by (ii) in its uncertainty or
Kirkwood–Dirac conclusions. No other source theorem is claimed to change.

**Source-supported deduction, not formalized here:** combining `result`
with the other nonconverse statements already in Proposition 7 makes each
link of its chain (i) ⇒ (ii) ⇒ (iii) ⇒ (iv) strict for every $d\geq4$. Only
the new first-link separation is kernel-checked by this module.

**Open:** classification of all basis pairs satisfying (ii) but not (i),
and which additional conditions on the transition matrix force (ii) to
imply (i). These are follow-up questions, outside this module's settlement.

## ASSUMED-UNVERIFIED

The arXiv v1 definitions and conjecture have been checked against the primary
HTML. The journal full text has not been checked for preservation of the
conjecture. Preregistration reports three read related papers and a bounded
search with no all-dimensional settlement; the remaining citing works were
not read and the arXiv API search was rate-limited. No exhaustive priority
check or model-family independence is claimed. External-source authenticity
and literature completeness are not consequences of Lean kernel checking.
