---
bibkey: hegyvari2026consecutivesums
authors: Norbert Hegyvári, Péter Pál Pach, Quanyu Tang
year: 2026
title: "Consecutive sums and Reconstructing Problems"
doi: null
url: https://arxiv.org/abs/2611.30462v1
claim: "Proposition 4.1 reconstructs a positive strictly increasing integer list of length at least three from the multiset of its inclusive consecutive interval sums of length at least two."
strata_touched:
  - D5/S3/Combinatorics/MonotoneIntervalReconstruction
license: CC0-1.0
triage: anchor
---

# Consecutive interval reconstruction

Section 4.1 defines the multiset with one occurrence for each pair of endpoints
and excludes singleton intervals. Proposition 4.1 treats positive strictly
increasing integers. The largest and second-largest observations recover the
first entry; the minimum recovers the second. Removing all known-prefix interval
occurrences with their multiplicities makes the next adjacent sum a residual
minimum. This proof route belongs to Hegyvári, Pach and Tang.

`Omega.MonotoneIntervalReconstruction.list_reconstruct` establishes the proposed
extension to nonnegative nondecreasing real lists, including zeros, equal
entries and repeated sums. Length equality follows from the observation
cardinality and is not an assumption. The extension is a repository derivation;
the cited proposition is not a supplier theorem for its enlarged scope.

The publication reports an O(n²) operation count. The formal result claims only
unique reconstruction and does not certify sorting, deletion, bit complexity,
RAM complexity or a general Turnpike algorithm. The bounded source and library
search does not establish global originality of the extension.

## Verified locator

URL: https://arxiv.org/abs/2611.30462v1

Pinned source: Section 4.1, Proposition 4.1 and its complete proof,
https://arxiv.org/html/2611.30462v1 . No DOI is declared.
