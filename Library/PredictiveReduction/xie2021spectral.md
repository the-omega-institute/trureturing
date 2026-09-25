---
bibkey: xie2021spectral
authors: Pinchen Xie; Weinan E
year: 2021
title: Coarse-grained spectral projection (CGSP): a deep learning-assisted approach to quantum unitary dynamics
doi: 10.1103/PhysRevB.103.024304
url: https://arxiv.org/abs/2007.09788v2
claim: Coarse spectral components and their phase evolution provide an existing quantum approximation framework with explicit discussion of spectral residuals and useful time scales.
strata_touched:
  - D5/S3/Quantum/Dynamics/HamiltonianEffectCompletionGenerator
license: citation-only
triage: anchor
---

# Spectral width and quantum prediction time

## Source and locator

The arXiv record identifies Physical Review B 103, 024304 (2021), with the DOI above. Version 2 was submitted on 4 November 2020. The parsed PDF was read at equations (6)–(8), which define spectral residual terms, expand the short-time state error, and discuss a simplified diagonal estimate. The paper labels the latter as a rough estimate; this note preserves that limitation. A requested PDF screenshot failed, so no visual-page review is claimed for this paper.

## Connection and boundary

The unified theory's Section 14 keeps finite-time phase differences in an exact matrix integral. That is a related spectral mechanism, not a reuse of CGSP's numerical accuracy claims or a proof that classical posterior compression supplies a physical quantum channel.

The source concerns quantum unitary-state approximation with a learned ansatz. The repository's Gaussian state-risk theorem and its supervised-trajectory variant use different probability models and losses. Their algebraic comparison does not identify these experiments or establish a new universal quantum compression theorem.

No XXZ experiment or neural ansatz from the source was reproduced here.
