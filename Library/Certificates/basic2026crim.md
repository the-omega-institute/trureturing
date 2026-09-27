---
bibkey: basic2026crim
authors: Ina Bašić; Eric Gottlieb; Matjaž Krnc
year: 2026
title: "CRIM: A Natural Game on Integer Partitions"
doi: 10.48550/arXiv.2606.16828
claim: Section 3 defines row deletion and conjugate-row-conjugate column deletion; printed Conjectures 2 and 3 give Sprague–Grundy formulas for square and near-square rectairs.
strata_touched:
  - D5/S0/Certificates/Games/CrimGrundyRefutation
  - D5/S0/Certificates/Games/CrimRectairSquareBoundaryRefutation
license: citation-only
triage: anchor
---

# CRIM and the printed near-square formula

Rendered pages 4, 5, 8 and 18 of https://arxiv.org/pdf/2606.16828v1
were inspected on 2026-09-10. Page 4 defines partitions as decreasing lists
of positive integers; the only partition of zero is the empty list.
Conjugation lists column heights. Section 3 on page 8 deletes an arbitrary
row, or takes the conjugate of a row deletion in the conjugate partition.
Thus zero rows or columns are absent, and remaining parts reattach.

Section 2.2 on page 5 defines R^k_{r,c} = [c^(r-k), c-1, ..., c-k],
for positive r,c and 0 ≤ k < min(r,c). Page 18 prints Conjecture 2:

> Let r and k be integers with 0 ≤ k < r. Then G(R^k_{r,r}) = 0 if r is
> even or k < r − 1; = 1 if r ∈ {3, 5}, r is odd, and k = r − 1; = 2
> otherwise.

The page 5 domain permits r=1 and k=0. At those parameters, the printed
third branch assigns 2 to R^0_{1,1}. Page 18 also prints, for r ≥ 7,
G(R^k_{r,r-1}) = 3 if k = r-2 and r is odd, and 1 otherwise in
Conjecture 3. This note attests the printed assertions and definitions,
not their truth. The formal refutations concern the literal Conjecture 2
boundary and the r ≥ 7 Conjecture 3 formula only; they give no conclusion
about other results, intended claims, or corrected formulas.

The arXiv history lists only v1, submitted 2026-06-15 at 15:09:22 UTC.
The DataCite record also reports version 1, resource type Preprint, with
no related publication identifiers. A bounded title query in Crossref
did not identify a journal version. Broader web queries were obstructed
or returned unrelated results, so no exhaustive literature claim is made.

## Prior unverified posting

Shivam Patel posted a reader calculation on 2026-08-20 at
https://mathdb.com/p/375372/the-sprague-grundy-conjecture-for-near-square-rectairs.
The site labels it “Claimed solved” but explicitly says: “An unverified
posted calculation claims the conjecture is false in both parity cases,
but no independent confirmation was found.” Its reported r=7 calculation
coincides with the separately computed example here. That posting was
not used as a numerical premise. No priority for the counterexample and
no verdict on the posting as a whole are claimed. The formal result
establishes only the computation checked by the Lean kernel.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2606.16828
- URL: https://arxiv.org/abs/2606.16828
- Version and scope: https://arxiv.org/pdf/2606.16828v1, printed pages 4,
  5, 8 and 18; Conjectures 2 and 3 and the partition, rectair and move
  definitions.
