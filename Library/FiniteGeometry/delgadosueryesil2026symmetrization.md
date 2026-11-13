---
bibkey: delgadosueryesil2026symmetrization
authors: Manuel Delgado, Meral Suer, Mehmet Yesil
year: 2026
title: "A Symmetrization for Almost Symmetric Numerical Semigroups"
doi: null
url: https://arxiv.org/abs/2611.14268v1
claim: "Section 5 asks whether the original pseudo-Frobenius row-deletion map is onto all symmetric numerical sets."
strata_touched:
  - D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiRefutation
license: arXiv.org perpetual non-exclusive license
triage: anchor
---

# Original-row symmetrization

Section 2 defines numerical sets as cofinite subsets of the nonnegative integers containing zero, and proper sets as those different from the whole set. Symmetric numerical sets need not be semigroups. The boundary scans zero through the largest gap, going right for membership and up for a gap. Each original gap labels its row by its first-column hook length.

Section 4 and Theorem 4.2 delete precisely the rows originally labelled by pseudo-Frobenius numbers other than the Frobenius number, preserve all retained row lengths, and apply the inverse boundary correspondence. In particular, original gap labels change after deletion. Algorithm 1 is presented as pseudocode for the construction; the row deletion in Theorem 4.2 controls the mathematical definition. No executable interpretation of the malformed extracted GAP punctuation is used.

Section 5 asks whether every symmetric numerical set arises this way. The obstruction is a retained row of length one for every proper numerical semigroup, forcing 1 to be absent from every image. The proper symmetric numerical set with gaps {2,3} contains 1 and hence has no preimage. This concerns all source sizes and uses no finite enumeration. It does not characterize the full image or assert literature priority.

## Verified locator

URL: https://arxiv.org/abs/2611.14268v1

Primary HTML: https://arxiv.org/html/2611.14268v1

Version: arXiv:2611.14268v1. Section 2 supplies the definitions and boundary correspondence; Section 4, Theorem 4.2 supplies the original-row deletion; Section 5 poses surjectivity. The primary HTML identifies the license as the arXiv.org perpetual non-exclusive license. The mathematical definitions and question are attributed to the authors; the obstruction and counterexample are the conclusions of the accompanying Lean module.
