---
slug: oeis-a035513-wythoff-column-residue-pairs
bibkey: kimberling2025a035513
doi: null
url: https://oeis.org/A035513
triage: theorem
motivation_gids:
  - D5/S3/Arith/Wythoff/ColumnResiduePairs
---

# Wythoff column residue pairs

## Problem

Clark Kimberling's 4 June 2025 comment on OEIS A035513 states:

> Conjecture: If m >= 2, then {(T(n,1), T(n,2)) mod m} has cardinality m^2.

Here `n>=1` ranges over positive row indices and `phi=(1+sqrt(5))/2`.
The first two columns are
`T(n,1)=floor(floor(n*phi)*phi)` and
`T(n,2)=floor(floor(n*phi)*phi^2)`.
For every integer modulus `m>=2`, their residue image is the full product
`(Z/mZ)^2`. Equivalently, for every `a,b` modulo `m` there is a positive
row with those two residues. The formal statement also includes `m=1`.

## Motivation

This is a tier-one named external conjecture. Issue #12448 fixes the
literal source, full quantifiers, proposed resolution and bounded
prior-work check before the Lean probe. It is a preregistration locator,
not mathematical proof evidence.

## Gap

The checked OEIS revision 223 still calls the assertion a conjecture.
The check reported in #12448 covers the named OEIS entry, Fried's
OEIS-conjecture papers, Adamczewski's *OEIS Open*, relevant arXiv queries,
the DeepMind `formal-conjectures` and Epoch `LeanOpenProblems` inventories,
and this repository. The implementation check additionally found no
`Wythoff` or `A035513` declarations through Loogle, no Lean GitHub code
search hit for `A035513`, and no repository search hit for `Wythoff Lean`.
The OEIS history page was accessible; its whole revision history was not
exhaustively searched. These finite checks do not establish global novelty.

## Route

Put `A=floor(n*phi)`. The irrationality of `n*phi` and the quadratic
identity `phi^2=phi+1` give `floor(A*phi)=A+n-1` and
`floor(A*phi^2)=2*A+n-1` for every positive row. Given residues `a,b`,
take representatives `r` of `2*a-b` and `s` of `b-a`, and consider
`n=r+1+m*k`, `k>=0`. The step `m*phi` has irrational ratio to the circle's
circumference `m`, so its integer orbit is dense. Compactness identifies
the closure of the nonnegative orbit with that of the integer orbit.
Translation by `(r+1)*phi` therefore hits the image of `(s,s+1)`.
Lifting this hit to the real line gives `floor(n*phi)=s+q*m` for an
integer `q`. The two closed formulas then produce `a,b`. The residue
image equals the full finite product, whose cardinality is `m^2`.

## Falsifier

A positive row where either nested-floor identity fails, or a positive
modulus with a residue pair never attained, would contradict the claim.
Checking any finite number of rows or moduli does not prove the universal
statement. A zero or negative row witness would fail the source quantifier.

## Evidence

`D5/S3/Arith/Wythoff/ColumnResiduePairs.lean` defines the array with the
source's two nested floors and subsequent Fibonacci recurrence. Its
single public `result` states both the cardinality and the positive-row
existence assertion for every positive modulus. Kernel, source fidelity,
publication, repository admission and merge are distinct checks.

## Triage

`theorem`; resolution `proved`; admission basis `open-problem-resolution`;
`proof_shape: bind-only`. The proof instantiates pinned Mathlib's golden
ratio, floor, irrational circle rotation, compact-group orbit and finite
cardinality theorems, then closes the algebraic side conditions. No
independent escape witness is claimed.

Proved: the decisive mechanisms are irrational rotation and the two
linear column expressions; their difference is `floor(n*phi)`. The
theorem supplies actual positive row witnesses for every residue pair.

Not separately formalized: consecutive-column pairs are related by the
Fibonacci transition `(u,v) -> (v,u+v)`, which has an integer inverse.
Extending the coverage statement to every adjacent pair is a natural
follow-up to assess on its own. For three or more columns the recurrence
imposes compatibility constraints, so full unconstrained tuple coverage
is a different question. A characterization of compatible tuples and
uniform asymptotic frequencies are unproved here; density alone does not
provide those frequencies. No dependent source claim is identified in
the checked OEIS comment block.

## ASSUMED-UNVERIFIED

The literature check is bounded to the sources listed above. No first-proof
claim is made. Equality with every column of every alternative presentation
of the Wythoff array is not a separate Lean theorem; the first two columns
and their recurrence are the explicit formal object. Source fidelity and
the issue's external literature-search reports remain subject to independent
review. Uniform distribution is not claimed.
