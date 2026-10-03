---
slug: chervov-2025-cayleypy-conjecture-one-refutation
bibkey: chervov2025cayleypy
doi: 10.48550/arXiv.2509.19162
url: https://arxiv.org/abs/2509.19162v2
triage: theorem
motivation_gids:
  - D5/S0/CayleyGrowth/CayleyPyConjectureOneRefutation.cayleyPy_conjecture1_refuted
---

# CayleyPy Growth Conjecture 1 is false

## Problem

Chervov et al., *CayleyPy Growth* (arXiv:2509.19162v2), Section 3.2,
conjecture that every generator family of `S_n` output by an algorithm of
polynomial complexity in `n` has an eventually linear or quadratic
quasipolynomial Cayley-graph diameter.

## Motivation

The conjecture quantifies over every polynomial-time output family, so a
single explicit family with non-quasipolynomial diameter settles its literal
statement. The earlier repository result treats Conjecture 2's marked-element
distance, which does not imply a diameter counterexample.

## Gap

The bounded literature check read arXiv:2509.19162v2, Section 3.2; the arXiv
API still returned v2 on 2026-09-29. A public-source search of both arXiv
versions, title and identifier queries, Conjecture 1 with diameter and
transposition terms, CayleyPy-4, and accessible citing discussions found no
published resolution in that scope. The Semantic Scholar citation query
returned HTTP 429, so it supplied no citation evidence. This does not
establish exhaustive worldwide priority or exclude an independent proof.

## Route

Let `T_n` be all transpositions of `S_n`. At nonsquare sizes use `T_n`; at
square sizes use every product of at most three elements of `T_n`. The second
set can be output by enumerating lists of zero, one, two, or three pairs of
indices and composing their swaps. There are at most
`1 + C(n,2) + C(n,2)^2 + C(n,2)^3` such lists, and each output permutation
has length `n`. The square test, list enumeration, permutation composition,
and duplicate removal all take polynomial time in `n`. If generators are
required to exclude the identity, omit it from the output; the Cayley graph is
unchanged. Thus this family meets the paper's explicit-output condition.

For the nonsquare graph, a full-support rotation moves all `n` points, while
each transposition moves at most two. Every path to that rotation has length at
least `n/2`, so the diameter is at least `n/2`. For the square graph, Mathlib's
constructive factorization writes each permutation as at most `n`
transpositions. Grouping that list into blocks of at most three gives diameter
at most `ceil(n/3)`.

Suppose the diameter were eventually quasipolynomial with period `p`. Squares
of sufficiently large multiples of `p` and the numbers obtained by adding `p`
are in the same residue class, with the latter lying strictly between
consecutive squares. The constituent polynomial is below `5n/12` on the
square subsequence and above `5n/12` on the nonsquare subsequence. Its
difference from the linear polynomial `5X/12` would then have both signs
arbitrarily far out, impossible for a rational polynomial.

## Falsifier

The refutation would fail if the paper restricted its quantified generator
families beyond polynomial-time explicit output, if the square-size family
could not be output in polynomial time, or if one residue-class polynomial
could maintain the two eventual diameter inequalities. The source wording,
enumeration count, and Lean bounds address these three points.

## Evidence

The canonical Lean source is
`D5/S0/CayleyGrowth/CayleyPyConjectureOneRefutation.lean`. It proves the
transposition lower bound, the triple-product upper bound, the polynomial
sign obstruction, and `CayleyGrowth.cayleyPy_conjecture1_refuted`. The
polynomial-time output count is a source-level complexity argument, outside
the Lean statement.

The frozen module statement identity is
`sha256:42d3e90e37b3c7b79ca0e957e1c2c87f8e4046d897fe13071318fbc9364de61f`.
The Freeze event is
`sha256:73539ed8251121e370dae79647338a6cfbbb0882a1df725d339f9b30f0c100b8`.
The public declarations are general diameter and quasipolynomial statements,
not bounded enumeration, a checker, a numeric reduction, or a certified finite
instance. Their utility classification is `none`.

The Section 3.9 source-bound escape audit is unfinished. Issue #11179 records
the current registration obstacle and missing four-slot evidence for the three
public theorems; it does not certify a registration.

## Triage

Tier 1 external named conjecture. Resolution: `refuted`. The new general
diameter and polynomial-sign arguments provide the `escape-witness` admission
basis; the utility kind is `none`.

## ASSUMED-UNVERIFIED

The result addresses the conjecture's unrestricted polynomial-output class.
It does not settle any restricted natural-generator version.
