---
slug: gil-liang-odetola-weiner-antidiagonal-traffic
bibkey: gil2026grid
doi: null
url: https://arxiv.org/abs/2609.01562
triage: theorem
motivation_gids:
  - D5/S3/Arith/GoldenResource/ContinuousPrimeMaximum
---

# Gil–Liang–Odetola–Weiner antidiagonal traffic

## Problem

Conjecture 7.4 of arXiv:2609.01562v1 states:

> For every n ≥ 496 and every obstruction B on the antidiagonal x+y=n,
> the maximum of f_B is attained at (1,1) and (n-1,n-1).

Here f_B counts monotone north-east paths from (0,0) to (n,n) avoiding B
and passing through a grid point other than those two endpoints. The
obstruction ranges over all (a,n-a), 0≤a≤n. Existing preregistration:
https://github.com/the-omega-institute/trureturing/issues/8249.

The formal arithmetic proposition is exactly

```text
forall n a : Nat, 496 <= n -> 1 <= a -> 2*a < n ->
  n*(n-2*a+1)/(n-a)*choose(n,a)*choose(n-2,a-1)
    /choose(2*n-2,n-1) < 1
```

The divisions in this expression are rational. The domain includes a=1
and the odd near-central pair (497,248); it is not natural `a<n/2`.
The strict inequality is a sufficient assertion for the verbal conjecture;
neither its converse nor uniqueness of grid maximizers is claimed.

## Motivation

This is a first-tier, externally published 2026 conjecture, already selected
under issue 8249. It asks for a uniform conclusion beyond the source's
finite checks through n=2000. This dossier does not introduce a new target.

The existing `ContinuousPrimeMaximum` result provides a related analytic
pattern: locate a maximum by the derivative signs of a logarithmic
objective. It is methodological motivation, not an imported dependency or
a bound for this binomial ratio. The proof locates the discrete same-parity
peaks and establishes uniform estimates for them.

## Gap

The retained Lean claim is arithmetic only. The full ordinary grid
conclusion also uses the published Section 6 reduction, Propositions 7.1
and 7.2, Equation (2.1), Theorem 5.1 with n≥5, and Lemma 2.2(ii)/(iii).
Their complete domain accounting is in the mathematical Scribe. They are
literature inputs, not Lean-verified grid/path theorems here.

No prior exact resolution was identified in the bounded September 20, 2026
search recorded in `Library/Combinatorics/gil2026grid.md`. This does not certify
worldwide novelty or an exhaustive third-party Lean search.

## Route

The Scribe develops the approved uniform route: low-gap ascent at fixed n,
same-parity fixed-gap peaks, an analytic Stirling and entropy envelope,
decreasing parity envelopes, and the three local base certificates.
The only additional theorem in the module is the private
`uniform_peak_bound`, directly consumed by `result`. The superseded
two-neighbor domination is false at (498,241) and is not used; that pair
does not refute the arithmetic target.

## Falsifier

An admissible rational pair with R(n,a)≥1 would refute the formal claim.
A mismatch in any cited grid reduction, its range or its direction would
invalidate the claimed ordinary grid implication. A prior published exact
resolution would invalidate a priority claim, without invalidating the
arithmetic theorem. Finite computations alone cannot settle this domain.

## Evidence

The source is `D5/S3/Arith/FactorialRatio/GridAntidiagonalTrafficBound.lean`;
the public endpoint is its `result : claim`. The proof contains the exact
rational-to-real normalization and the unbounded reductions. All numerical
bases are local steps in this argument.

`question_answered`: issue 8249's all-parameter strict arithmetic assertion
for Conjecture 7.4. `dominating_theorem_search`:
`not-found-in-searched-scope`; repository, pinned Mathlib and the bounded
public declaration query are identified in the Library note.

| Declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| private uniform_peak_bound | content | The uniform logarithmic envelope bound at every large-gap parity peak, obtained by the live entropy and decreasing-envelope argument. | escape-witness |
| result | content | The all-parameter fixed-gap peak domination and low-gap reduction, combined on the live path with uniform_peak_bound and the k=15 tail. | escape-witness |

Direct frozen project dependencies: none; the module imports Mathlib only.
The `claim` definition specifies the proposition and is not a separate
proof. `computational_content.kind: none`: both theorems establish unbounded
analytic inequalities; neither is an enumeration, checker, numerical
reduction awaiting a numerical premise, or ordinary positive finite
instance. The three local certificates serve the unbounded proof, and are
not separately exported. The other utility fields are
`not-applicable(kind=none)`.

The mathematical Scribe binds `ResolutionKind.Proved` for this problem to
the frozen public declaration
`D5/S3/Arith/FactorialRatio/GridAntidiagonalTrafficBound.result`, with
statement identity
`sha256:f673d96f4a9458dac2934c5347b3871b8fd9419b97cea17345420ddd6e04a1d5`.
This resolves the full strict arithmetic assertion; the complete published
Conjecture 7.4 follows through the literature-audited sufficient implication
described above. The typed binding does not turn the grid/path inputs into
Lean theorems. Required remote CI, merge, main-cache verification and
completion audit remain pending; no new KPI is claimed.

## Triage

`theorem`, first tier. The delivery addresses the complete arithmetic
assertion, rather than a finite interval, asymptotic statement, or
conditional substitute. Its Scribe explains the full ordinary consequence
with the explicitly identified literature inputs.

## ASSUMED-UNVERIFIED

Publication priority beyond the bounded search is ASSUMED-UNVERIFIED.
The unusable general-search response and the nonexhaustive scope of the
public Lean declaration index are recorded in the source note. The
published grid/path inputs have not been formalized in this module.
The remaining integration gates are required before delivery is complete.
