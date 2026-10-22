---
bibkey: litheilharrowchuang2026coherent
authors: Z. Li; E. Theil; A. W. Harrow; I. Chuang
year: 2026
title: "An Exponential Sample-Complexity Advantage for Coherent Quantum Inference"
doi: 10.48550/arXiv.2605.21457
url: https://arxiv.org/abs/2605.21457v2
claim: "Section S3 A conjectures optimality of the purify-and-clone channel for m > n; the one-site loss is equation (S13), with one common target state chosen before the maximum over output sites."
strata_touched:
  - D5/S3/Quantum/Information/LiTheilHarrowChuangPurifyCloneRefutation
license: citation-only
triage: anchor
---

# Coherent quantum inference and random purification

## Verified locator

DOI: https://doi.org/10.48550/arXiv.2605.21457

Source: https://arxiv.org/abs/2605.21457v2

The source text is version 2. Section S1 B, equation (S13), defines the
one-site loss. Section S3 A, pp. 8–9, defines random purification and the
purify-and-clone channel in equations (S34) and (S35).

## Source statements

Section S3 A, p. 9:

> This channel is optimal for m ≤ n (see Ref. [S2]), and we conjecture that it is also optimal for m > n.

Section S3 A, p. 8:

> That is, C(ρ) is the convex hull of all m-tensor powers of purifications of ρ.

The output restriction on p. 8 is the totally symmetric subspace of the
joint system and environment sites. Each one-site marginal retains both
registers. The infidelity is one minus squared Uhlmann fidelity.

## Mathematical scope

The formal statement takes n = 1 and m = 2 and uses the worst-case one-site
risk over all input density states of rank at most r. Its target infimum
ranges over the convex hull of all purifications, with the same target in
both site comparisons. Infima and suprema take values in EReal. The
counterexample uses d = r = 2: the purify-and-clone risk is at least 1/5,
whereas a completely positive trace-preserving channel with totally
symmetric output has risk at most 1/6. This refutes the universal optimality
claim in this reading. The all-site risk, average risk, optimal competitor,
and the family of strict improvements for every d ≥ r ≥ 2 remain open here.

The source's upper bound in Theorem S3.1 does not require equality with the
optimal risk. A strict improvement is compatible with that upper bound.
Prior-art completeness is ASSUMED-UNVERIFIED beyond the literature screen
recorded in issue #19410.
