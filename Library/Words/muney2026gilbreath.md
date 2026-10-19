---
bibkey: muney2026gilbreath
authors: Leila Muney
year: 2026
title: "Holes in Valid-Extension Sets of Finite Gilbreath Sequences"
doi: null
url: https://arxiv.org/html/2606.23721v2
claim: "Section 16(4) asks whether the maximum number of maximal step-two runs in K_S is 2^(n-4) for every n at least five."
strata_touched:
  - D5/S3/Combinatorics/FiniteDifferences/GilbreathExtension
license: arXiv perpetual non-exclusive license
triage: anchor
---

<!-- GID: D5/L/Combinatorics/muney2026gilbreath -->

# Finite Gilbreath extension components

## Verified locator

- Original source: https://arxiv.org/html/2606.23721v2
  (arXiv:2606.23721v2), *Holes in Valid-Extension Sets of Finite Gilbreath Sequences*.
- Question: Section 16(4). The definitions are in Sections 1 and 2;
  the maximal step-two components and the known attaining family are in
  Section 13, including Definition 31 and Theorem 35.

The source is arXiv:2606.23721v2, version of 16 July 2026. Section 16(4)
asks: “Is max_{S∈G_n} #comp(K_S)=2^(n-4) for all n≥5? Verified for n≤10.”
Sections 1 and 2 define the absolute-difference triangle, its all-one positive
left edge, the strictly increasing integer prefixes beginning with (2,3),
and the set of every integer extension preserving the Gilbreath property.
An extension need not preserve strict increase. Section 13 defines components
as maximal runs of common difference two in a finite set of one parity.

The Lean list representation preserves the entire ordered prefix. Source
position a corresponds to list position a minus one; source row b corresponds
to `row s b`. The maximal-run representation uses both endpoints, includes
every intermediate integer of that parity, and excludes the adjacent points
at distance two. The whole proposition demands finiteness of both the full
extension set and its run set, one parity, the universal upper bound, and an
eligible attaining prefix for every natural length at least five. Its
definition is the proposition proved by `GilbreathExtension.result`. The
source-index recurrence agrees with each valid row-list entry; the run bridge
enumerates the finite progression between its endpoints. The uniform upper
bound uses absolute-value preimages of parity-interval covers and the actual
four-entry triangle seed. The known attaining family is proved unconditionally
as a necessary part of the whole result.

Definition 31 and Theorem 35 give Muney's known attaining family V_n:
its first entry is two, entries i=2,...,n-1 are 2^(i-1)+1, and its last
entry is 2^(n-1)-1. This known lower-bound result requires faithful formal
proof if used; it contributes no separate new problem credit. The distinct
maximum-cardinality and uniqueness question, Conjecture 30, has a posted
Shivam Patel solution at MathDB 375513 and is outside this target.

The supplied bounded status evidence covers the complete original v2,
official arXiv feeds containing one and two records, and MathDB searches
containing twenty and seven visible results. No exact component-maximum
resolution was found in those scopes. This is neither worldwide absence nor
a priority claim. No new source acquisition is implied.

The source license is not a code-reuse license. The Lean and Scribe are
independently authored mathematical representations with attribution; no
paper program, external Lean code or expressive exposition is copied.
