---
bibkey: anholcer2026epistemic
authors: Marcin Anholcer; Maciej Bartkowiak; Bartłomiej Bosek; Jarosław Grytczuk
year: 2026
title: Epistemic fair division of independence structures
doi: null
url: https://arxiv.org/abs/2606.11494v1
claim: "Conjecture 4 asserts goods and chores EF1 existence under heterogeneous matroid constraints with individual chromatic number at most the number of agents."
strata_touched:
  - D5/S3/Combinatorics/Matroids/AnholcerEpistemicEF1Refutation
license: citation-only
triage: anchor
---

# Epistemic fair division under individual matroid constraints

## Verified locator

Source: https://arxiv.org/abs/2606.11494v1

The cited source is arXiv version 1. Its source license is CC BY-NC-ND 4.0;
this note is citation-only and quotes the statements needed for the mathematical correspondence.

## Source statements

Page 21, Conjecture 4: “Let M₁, …, Mₙ be a collection of matroids on the same ground set E satisfying χ(Mᵢ) ⩽ n, for all i = 1, 2, …, n. Suppose that there are n agents with additive valuations v₁, …, vₙ of the set of goods (or chores) E. Then there exists an EF1 partition E = X₁ ∪ ··· ∪ Xₙ such that each set Xᵢ is independent in the matroid Mᵢ, for all i = 1, 2, …, n.”

Page 4: “Throughout, a partition into n bundles means an ordered n-tuple of pairwise disjoint, possibly empty, sets whose union is the relevant ground set.”

Page 5: “For a given independence structure M, we denote by χ(M) the chromatic number of M, that is, the least number of parts in a partition of the ground set E into independent sets.”

Page 4: “In this way, any subset of goods X ⊆ E, called a bundle, gets a value vᵢ(X) = ∑_{gⱼ∈X} vᵢ(gⱼ) given by agent i. Such valuations are called additive.”

Page 4: “For general monotone valuations, we use the existential version: if Xⱼ ≠ ∅, there must exist a good g ∈ Xⱼ such that vᵢ(Xᵢ) ⩾ vᵢ(Xⱼ ∖ {g}); if Xⱼ = ∅, the condition is automatic.”

Page 20: “More formally, the allocation (X₁, …, Xₙ) is EF1 for chores if for every pair i ≠ j, either Xᵢ = ∅, or there exists a chore c ∈ Xᵢ such that vᵢ(Xᵢ ∖ {c}) ⩽ vᵢ(Xⱼ).”

The finite ground and ordered agents are enumerated by Fin m and Fin n.
The positive-agent hypothesis is explicit; m may be zero. Native Mathlib
Matroid and Matroid.Indep retain the actual exchange law, and each matroid's
ground is required to be Set.univ. Additive singleton weights are arbitrary
NNReal values. Empty bundles and deletion from the appropriate bundle are
included. The goods and chores existence assertions have separate allocations.
The explicit additive statement of Conjecture 4 is used; the overview's broader
monotone-valuation description does not weaken this counterexample.

## Refutation and scope

On four items, the capacity-one partitions {0,1}/{2,3} and {1,2}/{3,0}
define two heterogeneous matroids. Each is two-colorable. Every complete feasible
allocation consists of {0,2} and {1,3}, in one of two orders. Identical weights
(3,1,3,1) give values 6 and 2; deleting either high-valued item leaves 3 > 2.
Thus both goods and chores EF1 fail in every feasible allocation.

Dror–Feldman–Segal-Halevi, JAIR 76 (2023), DOI 10.1613/JAIR.1.13779,
Section 8.3, Proposition 1 and Examples 5–6, supplies the earlier complementary-item
obstruction under a common nonmatroid constraint. The two heterogeneous matroids
realize that obstruction through completeness. Their exchange laws alone do not
provide enough freedom for an EF1 complete allocation. Feasibility survives:
the two parity allocations exist. This does not refute the source's common-matroid
Conjectures 1 or 2, either main theorem, or an epistemic EF1 assertion; it does not
independently settle Problem 3 or additional compatibility hypotheses.

## Supplemental computation

Repository: https://github.com/the-omega-institute/trureturing-experiments

Commit: 303ffbbcfe85204772f3485d4c7025c4b3ad6802

Program: docs/reports/anholcer-et-al-epistemic-ef1-matroids/check.py

Command: `python3 docs/reports/anholcer-et-al-epistemic-ef1-matroids/check.py`

SHA-256: ac1642dbebff4e088af5316ca68302de06914a6a8ee0346553bf393507b2def7

The reported exit code is 0, ending in ALL_CHECKS_OK. Exact rational computation
checks ranks 2–8, nine strict parameter pairs per rank, threshold controls, and
all 256 corners of an independent eight-coordinate radius-1/10 perturbation box.
Equal rank two, looplessness, exact chromatic number two and strictly positive
identical valuations do not repair the four-item witness. These additional
restrictions and finite-family checks are computed results; the unbounded family
and full real perturbation region are not Lean-certified by this module.

## Literature boundary

The bounded screen associated with issue #25693 covers the versioned source,
the cited JAIR obstruction, exact-author post-source papers and selected arXiv
full-text hits for heterogeneous matroid EF1. It found no settlement of this
exact conjecture in the screened material. Semantic Scholar and OpenAlex citation
sets were unavailable, and broader full-text pagination was incomplete.
Literature completeness and priority are ASSUMED-UNVERIFIED.
