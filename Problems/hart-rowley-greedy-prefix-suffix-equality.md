---
slug: hart-rowley-greedy-prefix-suffix-equality
bibkey: hartrowley2025involutionprefixes
doi: 10.48550/arXiv.2502.00777
url: https://arxiv.org/abs/2502.00777v1
triage: theorem
motivation_gids:
  - D5/S3/FiniteGroups/HartRowleyGreedyRefutation.result
---

# The tentative Hart–Rowley prefix/suffix equality

## Problem

Sarah B. Hart and Peter J. Rowley, *A note on involution prefixes in Coxeter
groups*, arXiv:2502.00777v1, section 3, printed page 5, immediately before
References, write:

> We suspect that the involution length of any element always equals its
> ‘suffix’ involution length, but have not tested this extensively enough to
> make a firm conjecture.

This is one explicitly tentative, unnumbered published assertion. The quoted
text is licensed CC BY 4.0, https://creativecommons.org/licenses/by/4.0/ ; PDF
line wrapping and typographic ligatures are normalized. It is not Conjecture
1.2 or 1.3.

The domain is every Coxeter system whose every nonidentity element has a unique
maximum-Coxeter-length involution prefix, and every element of such a system.
An involution has order exactly two. A prefix u of w satisfies w = uv and
length(w) = length(u) + length(v). The unique ancestor maximizes length over all
involution prefixes. Remove it and recurse on v, with zero factors at identity.
The suffix procedure removes the analogous right factor. The assertion equates
these two actual greedy counts. No finiteness, rank, or Coxeter-element
restriction is imposed, and neither count minimizes arbitrary factorizations.

## Motivation

The ancestor decomposition gives a canonical length-additive involution
factorization. The question asks whether its number of factors is independent
of orientation. The formal claim and its designated negation belong to
`D5/S3/FiniteGroups/HartRowleyGreedyRefutation`; the motivation selector above
names the intended resolving result. Its frozen-member validation belongs to
the canonical freeze stage.

## Gap

The source supplies an inverse correspondence between involution suffixes of w
and involution prefixes of its inverse. Equality at w would additionally require
invariance of the prefix count under inversion. That extra assertion can fail.
The two notions of involution length must also be distinguished: a short
arbitrary involution factorization does not establish the length-additive,
maximum-at-every-step greedy count.

## Route

Use the standard adjacent swaps in S4. Establish their Coxeter presentation of
type A3, and identify genuine Coxeter length by reduced normal words and a
lower bound along every simple-generator step. Check the unique longest
involution prefix for every nonidentity permutation, including all competitors.
The suffix choices use the same definition with right residuals. Strictly
decreasing Coxeter length makes both residual recursions terminate at identity.
A single qualifying system and element with unequal counts negates the entire
unrestricted equality.

## Falsifier

A purported refutation fails if its group is not proved to be a Coxeter system,
its length is not proved to be Coxeter length, its ancestor hypothesis holds
only on the displayed chains, it replaces maximum length by inclusion
maximality or a minimum factor count, or its recursions do not reach identity.
For the universal equality itself, any fully qualifying system containing an
element with unequal greedy counts is a counterexample.

## Evidence

In one-line image notation and multiplication (uv)(i) = u(v(i)), take w = 2431
in S4. The prefix chain is 2431 = 2143 · 1342 and 1342 = 1324 · 1243,
followed by 1243 itself. The successive factor lengths are 2, 1, 1 and the
prefix count is 3. The suffix chain is 2431 = 2134 · 1432, followed by 2134;
the removed right factor has length 3 and the remaining factor has length 1,
giving count 2. Every displayed product is length additive. The group-wide
unique-maximum certificate is essential, rather than an assumption inferred
from those chains.

The claim is a closed `Prop` and the designated result has literal type
`Not claim`. Kernel checking of the exact candidate, its axiom closure and
nonvacuity is separate from canonical freezing and full repository admission.

## Triage

Tier 1: a recent specialized side assertion, expressly insufficiently tested by
its authors. No extensive prior attack on this exact equality was established.
The prospective exact statement is registered in issue
https://github.com/the-omega-institute/trureturing/issues/17426 . Bounded
source/status qualification found no exact prior resolution; the source note
records both the inspected later originals and the coverage limits. The canonical admission audit is tracked in issue
https://github.com/the-omega-institute/trureturing/issues/17462; its 22 helper audits
remain unfinished (one designated closed result is the sole exception), none is
declared_validated, and no audit retry is part of this delivery.

The orientation mechanism is that removing the commuting initial pair (12)(34)
leaves two further greedy factors, while the right end admits the longer
involution (24) and leaves one. Maximizing the current factor length does not
make the eventual factor count invariant under reversal.

Known source conclusions that survive include the Coxeter-element ancestor
results and their graph-coloring/path interpretations, and the inverse
prefix/suffix correspondence. Conjecture 1.2, asserting the ancestor property
for every finite Coxeter group, and Conjecture 1.3, asserting the finite rank
bound, are separate open questions in the cited source. This witness satisfies
the ancestor hypothesis and both counts obey the A3 rank bound. It does not
refute either conjecture or the Coxeter-element conclusions. No rank
minimality, classification, adjacent-problem credit or priority is asserted.

## ASSUMED-UNVERIFIED

Source fidelity and adequacy of the bounded literature and ownership searches
require independent assessment. Unindexed, differently worded, unpublished and
outside-scope prior resolutions remain unexcluded. The four sibling experiment
artifacts are unread, unverified and unused. The author candidate is separate
from independent prefreeze fidelity, atom-aware freeze, canonical emission,
full immutable-base admission, reviews, required PR-head CI, merge and
subsequent independent dev verification. No solved-problem count follows from
this dossier or a scoped compile alone.
