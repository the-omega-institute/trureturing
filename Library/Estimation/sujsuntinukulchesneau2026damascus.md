---
bibkey: sujsuntinukulchesneau2026damascus
authors: Chanatip Sujsuntinukul and Christophe Chesneau
year: 2026
title: Variants of the Damascus inequality
doi: 10.1007/s11139-026-01345-1
url: https://arxiv.org/abs/2601.00916v4
claim: Section 5 asks whether the Damascus violation sets are bounded for arbitrary dimension; the paper proves boundedness in dimension three.
strata_touched:
  - D5/S3/Analytic/DamascusViolationSetBoundedness
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.1007/s11139-026-01345-1

Source: https://arxiv.org/abs/2601.00916v4

The version is arXiv:2601.00916v4, 18 March 2026; the journal locator is The Ramanujan Journal 69 (2026), article 68.

## Source definitions

On page 2 the constraint hypersurface is

$$H_m := \{(x_1,\ldots,x_m)\in(0,+\infty)^m : \prod_{j=1}^m x_j=1\}.$$

Section 5, page 13, defines:

> I_n^m := {(x₁, …, x_m) ∈ H_m : Σ_{j=1}^m (x_jⁿ − 1)/(x_j^{n+1} + 1) > 0}. For instance, we know that I_n^2 = ∅ for all n, and (1/2, 3/2, 4/3) ∈ I_n^3 for n ⩾ 5.

The summand in inequality (1), page 2, is $(x_j^n-1)/(x_j^{n+1}+1)$.

## Open question

The final paragraph of Section 5, page 19, asks:

> In addition to the above, it is natural to ask whether analogous structural properties hold for I_n^m when m is arbitrary. Can one prove or disprove that I_n^m (i) stays uniformly away from 1, (ii) is bounded, or (iii) forms an increasing family in n?

It concludes:

> Thus this question, together with question (iii), remains open.

The full boundedness classification is an answer derived in this repository, rather than a proposition stated in the source. The formal statement uses natural numbers m,n ≥ 1 and Fin m for the coordinates, with the usual sup norm and Bornology.IsBounded. All sums and products count each coordinate once. The source's other questions and the scalar supremum characterization are separate from that statement.

## Literature boundary

The preregistration's journal-version and follow-up readings are reported by its search seat. Completeness of that literature search is ASSUMED-UNVERIFIED; this note makes no novelty or publication-readiness assertion.
