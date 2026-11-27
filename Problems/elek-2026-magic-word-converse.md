---
slug: elek-2026-magic-word-converse
bibkey: elek2026magicwords
doi: 10.48550/arXiv.2610.22730
url: https://arxiv.org/abs/2610.22730v1
triage: theorem
motivation_gids:
  - D5/S3/FiniteGroups/CoxeterMagic/ElekMagicWordConverseRefutation.result
---

# Elek’s magic-word converse

## Problem

Balázs Elek states Conjecture 3.3 in *Hypercube Richardson varieties from
magic words*, arXiv:2610.22730v1:

> A Bruhat interval $[v,w]$ is a hypercube if and only if there exists a magic word $Q$ for $[v,w]$.

The conjecture uses the Kac–Moody Weyl-group setting in §2.1. The Lean
claim quantifies over Coxeter systems whose Coxeter matrix comes from an
integral generalized Cartan matrix on a finite node set. The group may be
infinite. For each such system and each pair $v\leq w$, a hypercube is an
interval isomorphic to a finite Boolean lattice with its subset order. A magic word is a reduced
expression for $w$ having exactly one positional subword with product $v$.
The source counts all position choices, including nonreduced retained
words. [Conjecture 3.3](https://arxiv.org/html/2610.22730v1#S3.Thmtheorem3)

## Motivation

Corollary 3.2 derives the Boolean interval from a magic word. The converse
would give a reduced-word certificate of positional uniqueness for every
Boolean interval in the published Weyl setting.
[Corollary 3.2](https://arxiv.org/html/2610.22730v1#S3.Thmtheorem2)

## Gap

Booleanness records the order of interval elements, while magicness counts
positions in a reduced expression. If the only reduced expression for
the top repeats a simple reflection lying at the bottom, its distinct
occurrences can already violate positional uniqueness.

## Route

Use the canonical crystallographic type $B_2$ presentation with reflections
$s,t$ and braid exponent four. The Cartan matrix with rows $(2,-2)$ and
$(-1,2)$ gives that exponent. Among the words of length at most three,
only $sts$ has the image of $sts$ under the lift to the dihedral group.
A shortest representative in the Coxeter presentation exists and has
length at most three, so the image forces length three and the sole
reduced word $sts$. The positional subword criterion gives the full lower
set, then the entire interval above $s$.

The lift is adapted from Jeromie N. Beasley’s Apache-2.0 Mathlib
contribution.
[Dihedral lift](https://github.com/dicipler-pixel/mathlib4/blob/08e259a357c8e0caed76ca53aef41f40286b3694/Mathlib/GroupTheory/Coxeter/Dihedral.lean) · [License](https://github.com/dicipler-pixel/mathlib4/blob/08e259a357c8e0caed76ca53aef41f40286b3694/LICENSE)

## Falsifier

A Boolean interval with no magic reduced word disproves the biconditional.
Here $[s,sts]$ is such an interval. The masks $100$ and $001$ both give $s$,
and uniqueness of the reduced expression rules out a different top word
with a single positional realization.

## Evidence

The eight masks in order from $000$ to $111$ give
$e,s,t,ts,s,e,st,sts$. In particular, the two selected letters in $101$
multiply to the identity. The interval consists of $s,st,ts,sts$.
The bijection to the empty set, the two singleton subsets, and the whole
two-element set preserves and reflects all sixteen comparisons. The
designated Lean theorem has type `Not claim` for the closed Weyl-domain
proposition. The Bruhat subword criterion is Björner–Brenti, Theorem 2.2.2
and Corollary 2.2.3. [The Bruhat Order](https://doi.org/10.1007/3-540-27596-7_2)

## Triage

Tier 1. This is a named conjecture in a recent paper. The same interval
appears in Umutabazi’s §4 for another descent criterion. Elek’s Lemma 2.17
already excludes even almost magic words with the sole possible last
letter $s$, since $vs=e<v=s\leq ws=st$. The bounded literature search
located these ingredients and related type-A results.
[Umutabazi, §4](https://arxiv.org/pdf/2206.06538v1#page=5) · [Elek, Lemma 2.17](https://arxiv.org/html/2610.22730v1#S2.Thmtheorem17) · [Literature record](https://github.com/the-omega-institute/trureturing/issues/27568)

### What the settlement shows

- **Proved in Lean.** A four-element Boolean interval in the presented
  Weyl group can fail the converse because the sole reduced word repeats
  its bottom generator. The motivation GID identifies the formal negation.
- **Published forward direction.** Corollary 3.2 still gives magic implies
  hypercube for Weyl groups. Its Coxeter-group extension in Remark 3.4
  and the converse restricted to simply laced Weyl groups are separate
  questions left open by this argument. The type-A checks and results in
  Elek remain in their stated scope.
- **Separate deduction from the witness.** In the general Weyl reading of
  Conjecture 3.9, $D(sts)=D(s)=\{s\}$ by the characterization of right
  descents as last letters in reduced expressions, and $s\leq(sts)s=st$.
  Both alternatives in 3.9 fail in this instance. This deduction uses
  the known right-descent characterization in addition to the witness
  and has no separate Lean endpoint here.
  [Conjecture 3.9](https://arxiv.org/html/2610.22730v1#S3.Thmtheorem9)

## ASSUMED-UNVERIFIED

The literature assessment is bounded by the accessible publications and
indexes in the source note. Incomplete citation responses, unindexed
work and unpublished results leave global priority undetermined.
