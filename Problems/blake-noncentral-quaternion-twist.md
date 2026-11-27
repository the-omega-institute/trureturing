---
slug: blake-noncentral-quaternion-twist
bibkey: blake2026perfectquaternionsequences
doi: 10.48550/arXiv.2611.19627
url: https://arxiv.org/html/2611.19627v1#S5.Thmtheorem2
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/QuaternionSequences/BlakeConjecture52.blake_conjecture_5_2
---

# Blake's noncentral quaternion twist conjecture

## Problem

Sam Blake's Conjecture 5.2 asks whether

> No sequence of length M ≥ 2 over Q₈ has type ±i, ±j or ±k.

The source's Definition 2.1 extends a length-M sequence by
$E(qM+r)=s_r u^q$ for every integer $q$ and $0\le r<M$, with the
twist multiplied on the right. Type $u$ means that
$\sum_{r=0}^{M-1}s_r\,\overline{E(r+\tau)}$ vanishes at every integer shift
$\tau$ outside the multiples of $M$, where the bar is quaternion
conjugation and $u\in\{\pm i,\pm j,\pm k\}$. The formal result keeps the
original all-positive-length scope. It states, for every natural $M$ with
$2\le M$, every sequence with entries in the eight signed quaternion units,
and every noncentral twist, that some integer $\tau$ satisfies
$0<\tau<M$, $M\nmid\tau$, and the literal twisted correlation is nonzero.

### Statement echo

The Lean `extension` uses Euclidean remainder and quotient on every
$n\in\mathbb Z$ and the integer power of the signed twist unit. Thus negative
quotients and all signed shifts are included. The witness in
`blake_conjecture_5_2` is the positive off-period shift required by the
source's type definition.

## Motivation

Issue #34685 preregistered the exact source sentence, its quantifiers, the
integer extension, and a bounded literature screen before the executable
proof. The source presents the assertion as an open conjecture after its
structural reduction and finite exclusions.

## Gap

The bounded screen recorded in #34685 found no exact proof or refutation in
the source, its cited and companion arXiv material, the publisher and index
records searched there, or the repository issue history. That screen does not
establish exhaustive worldwide novelty or priority. The remaining formal gap
was the uniform all-length quaternion statement with the source's right-sided
extension and multiplication order.

## Route

The proof takes a direct characteristic-two route. Mapping every quaternion
letter to one in the field with two elements makes the shift-one correlation
equal to $M$, so the assumed vanishing forces $M$ even. Write $M=dm$, where
$d$ is the highest power of two dividing $M$ and $m$ is odd. In
$R=\mathbb F_2[T]/(T^{2d})$, set $W=1+T$ and $V=1+T^d$. Then
$V=W^d$, $V^2=1$, and $W^M=V$.

For each noncentral twist, a quaternion-algebra character sends that twist
to $V$ and the remaining coordinate choices to $1$ or $V$. It preserves the
image of conjugation in characteristic two. The cyclic product identity groups
the two weighted sums by the index difference. Wrapped terms acquire exactly
the factor $V$, so the assumed zero correlations force the product to vanish.
Lifting each mapped letter to either $1$ or $1+T^d$ leaves both factors with
the geometric-sum coefficient at every degree below $d$. Their coefficient at
degree $2d-2$ is one, and this degree survives the quotient, contradicting
the vanishing product.

## Falsifier

An admissible counterexample would give a natural $M\ge2$, a sequence of
signed quaternion units, and a noncentral twist whose literal correlation is
zero at every integer shift not divisible by $M$. A counterexample restricted
to a single positive shift would not meet the source's type definition.

## Evidence

The settling declaration is
`D5/S3/Combinatorics/QuaternionSequences/BlakeConjecture52.blake_conjecture_5_2`.
The scoped native Lean and Reg builds pass. The native theorem's axiom closure
is `propext`, `Classical.choice`, and `Quot.sound`.

The Reg source is
`Reg/D5/S3/Combinatorics/QuaternionSequences/BlakeConjecture52.lean`.
Its `family` uses the actual sequence readout `p.2 r`, has the source bridge
`bridge := Iff.rfl`, and is inserted into the typed registration with the
same theorem telescope. This is the compiled source-equivalence proof for
the registered readout. The Library note is
`Library/FiniteGroups/blake2026perfectquaternionsequences.md`, with bibkey
`blake2026perfectquaternionsequences`, DOI
`10.48550/arXiv.2611.19627`, and the exact v1 conjecture URL
`https://arxiv.org/html/2611.19627v1#S5.Thmtheorem2`.

## Triage

Tier 1 external conjecture, preregistered in issue #34685. Resolution is
`Proved` by the all-positive-length Lean theorem. The native module is kept
under the open-problem-resolution basis. Its public result is the settling
theorem, and its private polynomial, character, cyclic-product, and
coefficient declarations are consumed on that live proof path.

### What the settlement shows

**Proved in this module.** Every $M\ge2$, every signed-$Q_8$ sequence of
length $M$, and every noncentral twist has a nonzero correlation at an integer
shift strictly between zero and $M$. The proof uses the source's right-sided
signed extension and the original quaternion multiplication order.

**Computed with the scoped Lean and Reg commands.** The native theorem and
its typed Reg mirror compile with the standard axiom closure listed above.
The registration's actual readout is the sequence field, and its source bridge
is definitionally reflexive.

**Open.** Exhaustive literature priority, publisher material outside the
bounded screen, and extensions to other alphabets or altered extension
conventions remain unverified. No statement about those variants is added to
the formal result.

## ASSUMED-UNVERIFIED

The bounded literature screen in #34685 does not prove that no independent
proof exists outside the searched source, companion, index, publisher, and
repository records. The source's physical or analytic interpretations beyond
the integral Hamilton model are not formalized. The result does not cover
different multiplication orders, different twist alphabets, or a weakened
shift quantifier.
