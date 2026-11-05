---
bibkey: bouafia2026treemagnitude
authors: Philippe Bouafia
year: 2026
title: Magnitude and diversity of trees
doi: 10.48550/arXiv.2605.03681
url: https://arxiv.org/abs/2605.03681v1
claim: Algorithm 1 computes the diversity-maximizing measure on weighted trees; the extension to every finite metric space of negative type is posed as an open question.
strata_touched:
  - D5/S3/Geometry/BouafiaNegativeTypeDiversityDeletionRefutation
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.48550/arXiv.2605.03681

Source: https://arxiv.org/abs/2605.03681v1

## Source statements

Page 18, Section 4.1, immediately after Theorem 4, verbatim:

> Does DiversityMaximizingMeasure correctly compute the maximizing-diversity measure of all finite subsets of ℝⁿ? Of all finite metric spaces of negative type?

Page 4, Section 2.2, verbatim:

> A metric space (X,d) is said to be of negative type if (X,√d) admits an isometric embedding into a Hilbert space.

Page 2, introduction, verbatim, with its displayed expression:

> A probability measure μ : X → [0, 1] is said to be diversity-maximizing if it minimizes the quantity
>
> μᵀ Z μ = ∑ₓ,ᵧ∈X e⁻ᵈ⁽ˣ,ʸ⁾ μ(x)μ(y)
>
> which represents the average similarity between two independent samples drawn according to μ.

Page 16, Algorithm 1 initializes the active set to X, extends each inverse solve by zero, keeps strictly positive weights and normalizes by the total weight. Its printed test is “w ≱ 0”. Theorem 4's proof on the same page instead states, verbatim:

> At the end of the repeat loop, the vector w is non-zero and non-negative.

The finite negative-type refutation uses this nonnegative stopping condition. It concerns real-valued finite distances, nonempty spaces, genuine inverses on every visited support and positive normalization. It does not refute the weighted-tree theorem or settle the separate Euclidean-distance question.

## Scope of the finite refutation

The five binary points have Hamming matrix with rows (0,3,2,3,3), (3,0,3,2,4), (2,3,0,3,1), (3,2,3,0,2), (3,4,1,2,0). Scaling by log(20/19) gives a negative-type metric and exponential similarity entries (19/20) raised to those entries. The first inverse solve removes indices 2 and 3. The second solve is nonnegative but its normalized probability has a strictly worse objective than a probability restoring positive mass at index 3. This finite refutation is derived in the repository, rather than attributed to Bouafia. Simultaneous deletion and re-entry as a general failure mechanism are prior art in Huntsman, arXiv:2509.19565v3, Appendix G; no novelty of that mechanism is asserted.

## Computational evidence and limits

The exact family computations are in the private repository the-omega-institute/trureturing-experiments, commit 4251681e070bcb815a745273efdbaf15b373c10c, docs/reports/bouafia-diversity-negative-type/. The check.py SHA-256 is e5ecd757601c16502d86a31e5de5f69daf50eb98a196a8a5c265b77a0e3b9f22. The recorded command is `python3 docs/reports/bouafia-diversity-negative-type/check.py`, exit 0, final line ALL_CHECKS_OK. These are exact arithmetic computations, separate from the fixed-scale Lean proof. Bibliographic completeness remains ASSUMED-UNVERIFIED; the literature screen and source conventions are recorded in issue #25745.
