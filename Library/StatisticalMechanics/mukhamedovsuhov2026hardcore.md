---
bibkey: mukhamedovsuhov2026hardcore
authors: "Farrukh Mukhamedov and Yuri Suhov"
year: 2026
title: "Quasi-Product States and Factor Types for the One-Dimensional Hard-Core Model"
doi: null
url: https://arxiv.org/abs/2606.12458v2
claim: "Lemma 6.1 gives the endpoint-dependent hard-core cylinder weight, and its proof counts all legal transition types."
strata_touched:
  - D5/S3/Combinatorics/Graph/LegalWords/MarkovBlockWeight
license: citation-only
triage: anchor
---

## Verified locator

https://arxiv.org/abs/2606.12458v2

The full text at https://arxiv.org/html/2606.12458v2 states Lemma 6.1 and its transition-count proof.

## Mathematical correspondence

The paper uses transition entries p, q, 1, 0 with p+q=1 and activity q/p^2. For the binary block transition parameter a, set p=1-a and q=a. Apply its cylinder formula to the padded path consisting of the left bit, the block and the right bit. Divide by the positive initial stationary mass. The resulting ordered transition product is a to the power of the right bit times (1-a) to the power of the block length plus one minus both boundary bits, times the activity to the power of the block occupation. Legality includes both boundary seams. This identity does not supply a conditional probability without normalization or an open-endpoint stationary factor.
