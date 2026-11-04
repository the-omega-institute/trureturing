---
slug: oeis-a381190-trapezohedral-domination-series
bibkey: oeis2026a381190
doi: null
url: https://oeis.org/A381190
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/Domination/TrapezohedralDominationSeries
---

# OEIS A381190 trapezohedral domination series

## Problem

OEIS A381190 is named “Number of connected minimal dominating sets in the n-trapezohedral graph.” Its conjectured formula is

`-2*x^3*(4*x^5 + 8*x^4 + 4*x^3 - 9*x^2 - 8*x - 3)/(x^3 + x^2 - 1)^2`.

The resolved statement is the literal ordinary formal-power-series identity for every integer `n >= 3`. For each `n`, the graph has distinct labelled vertices `alpha`, `beta`, `a_0,...,a_(n-1)`, and `b_0,...,b_(n-1)`, the alternating rim cycle, alpha adjacent to every `a_i`, beta adjacent to every `b_i`, and no other edges. The coefficient counts actual subsets `S` whose closed neighbourhood is the full graph, every proper subset of `S` fails to dominate, and the induced graph on `S` is connected. Minimality ranges over all proper subsets independently of their connectivity; no quotient by rotations, reflections, or other automorphisms is taken. Coefficients below order three are zero.

## Motivation

This is the full revision-16 OEIS conjecture. The exact source statement, quantifiers, boundary conditions, and rational expression are sealed in the preregistration attached to issue [#22452](https://github.com/the-omega-institute/trureturing/issues/22452).

## Gap

The graph source is Egolf and Furst, [arXiv:2502.05031v1](https://arxiv.org/abs/2502.05031v1), Definition 3.6. The general private-neighbour characterization is literature-attested in Mynhardt and Roux, [arXiv:1812.03382v3](https://arxiv.org/abs/1812.03382v3), §§1.1 and Observation 1.1(ii); that background result is not assigned as repository-derived. The repository's closed-private characterization is independently kernel-checked in `TrapezohedralMinimalDomination.minimalDominating_iff_private`.

The bounded source screen checked the OEIS entry, its revision and history surfaces, the primary graph definition, and identifier searches for the exact graph and sequence. The exact source event is authenticated by the immutable preregistration comment on issue #22452 and the sealed event/payload files. The live OEIS retrieval was unavailable in the independent review reads with HTTP 403; these limits leave no exhaustive worldwide absence or priority claim.

## Route

The formal route first represents the labelled graph and proves closed-private witnesses equivalent to inclusion minimality over all proper subsets. Apex classification then shows that every admissible connected subset has exactly one apex and the opposite rim label. A tagged cover equivalence records both apex branches without quotienting multiplicity. Opening the rim at the selected cut gives an ordered cut-cover/path correspondence, and complementing the cover gives the native maximal-independent path family. The head/tail inverse maps yield `M(n+3)=M(n+1)+M(n)` with `M(0)=M(1)=1` and `M(2)=2`. The endpoint/middle inverse maps give the restricted family, including its initial value. Coefficientwise formal-series identities and differentiation then produce the displayed rational expression with the squared denominator.

## Falsifier

An authenticated `n >= 3` with an exact actual labelled-subset count differing from the corresponding coefficient would refute the claim. Agreement for finitely many values, a surrogate path count without the proved subset correspondence, a symmetry quotient, minimum-cardinality domination, connected-only minimality, or eventual equality would not settle it.

## Evidence

- `D5/S3/Combinatorics/Graph/Domination/TrapezohedralMinimalDomination.alphaSet_admissible_iff` proves the fixed-apex admissibility equivalence and the module also contains the closed-private characterization.
- `D5/S3/Combinatorics/Graph/Domination/TrapezohedralApexClassification.exactly_one_apex` and `alpha_reconstruction` prove the apex classification and reconstruction.
- `D5/S3/Combinatorics/Graph/Domination/TrapezohedralTaggedCover.actualTaggedEquiv` gives the two tagged actual branches.
- `D5/S3/Combinatorics/Graph/Domination/PathMaximalIndependentCount.count_recurrence` and `D5/S3/Combinatorics/Graph/Domination/PathEndpointCount.both_count` supply the path-family recurrences and endpoint restriction.
- `D5/S3/Combinatorics/Graph/Domination/TrapezohedralPathEquivalence.actual_count` gives the all-order actual count.
- `D5/S3/Combinatorics/Graph/Domination/TrapezohedralDominationSeries.actual_series` proves the complete literal rational identity.

The endpoint statement IDs are `sha256:54000bdc1e949deaa94cf3f40889d49353f627ac654492c1ed6267215637e9c5` for `actual_series` and `sha256:8fcdbbc3c13b3bf2333f9b538a5a369a56983c335356476bfaab6ec2c465e66c` for `actual_count`. The current scoped report has axiom union `{Classical.choice, Quot.sound, propext}`.

## Triage

### What the settlement shows

- **Proved in Lean:** the graph, closed domination, all-proper-subset minimality, self-private witnesses, and induced connectedness are represented by the labelled definitions and the named characterization and apex theorems above.
- **Proved in Lean:** the two apex branches, ordered cut-cover/path bijection, native path maximal-independent recurrence, endpoint restriction, all-order actual count, and literal rational formal-series identity are the named declarations above.
- **Computed:** the published OEIS data and bounded finite readings are source observations only; they are not used as settlement evidence and do not replace the all-order proof.
- **Open:** the unfinished realization, reconstruction, positivity, intervention, sensitivity, observational-dependence, and binding audits tracked in [issue #22483](https://github.com/the-omega-institute/trureturing/issues/22483) remain unfinished. No `declared_validated` claim is made for those audits.

The decisive mechanism is the exact labelled subset-to-cover-to-path correspondence followed by the two path-family recurrences and coefficientwise differentiation. The proof covers every `n >= 3`, includes the zero prefix below order three, and does not require a convergence or eventual-equality argument. The same route supplies the explicit apex classification and path-family consequences recorded above; neighboring graph domination sequences are not asserted here.

The source's other graph questions and adjacent sequences retain their own statements and status. This settlement changes only the A381190 literal generating-function conjecture; it does not transfer its formula or proof to A370089, A372712, A381794, or any other sequence.

## ASSUMED-UNVERIFIED

The live OEIS endpoint availability and any exhaustive worldwide literature or priority statement remain outside the bounded authenticated source screen. The direct source links and revision-role attribution are recorded above; no world-first or exhaustive novelty claim is made.
