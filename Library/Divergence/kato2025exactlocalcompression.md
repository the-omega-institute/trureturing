---
bibkey: kato2025exactlocalcompression
authors: Kohtaro Kato
year: 2025
title: Exact and Local Compression of Quantum Bipartite States
doi: 10.1109/TIT.2025.3562884
url: https://arxiv.org/abs/2309.07434
claim: "Section VI.A, equation (62), gives the exact quantum memory dimension for a classical bipartite state as the number of distinct posterior laws on the marginal support."
strata_touched:
  - D5/S3/Quantum/Recovery/DiagonalRecordCapacity
  - D5/S3/Quantum/Measurements/FiniteLabelRecordDilation
license: citation-only
triage: anchor
---

# Exact local compression of classical correlations

## Verified locator

[Journal record](https://doi.org/10.1109/TIT.2025.3562884) · [arXiv record](https://arxiv.org/abs/2309.07434)

Definition 1 in Section II.B quantifies over quantum encoding and recovery channels after restricting to the marginal support.
Section VI.A, equation (62), counts the distinct conditional laws of the classical bipartite experiment.
[Primary text](https://arxiv.org/pdf/2309.07434v2#page=8)

## Formalization scope

The repository counts vectors of likelihood ratios for a diagonal experiment with a specified reference law.
For a finite family, assigning positive priors to the comparisons and the reference gives a classical bipartite experiment with the same classes on the reference support.
This identifies the relation between the two dimension criteria.
The formal theorem also allows a comparison index type without a finiteness assumption because the vectors are realized on a finite basis.

The count in Section VI.A is for unrestricted encoding and recovery channels on the marginal support.
The finite pure-environment label-record criterion adds per-class rounded memory requirements and a whole-input isometry bound.
