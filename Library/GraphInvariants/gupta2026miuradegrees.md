---
bibkey: gupta2026miuradegrees
authors: Chakshu Gupta
year: 2026
title: "One construction for the Miura-ori flip-graph degree sequence"
doi: 10.48550/arXiv.2607.05567
url: https://arxiv.org/abs/2607.05567v3
claim: "Conjecture 8.3 bounds the residual split-count polynomial by total degree d-3; the finite Envelope Lemma and normalized-height finiteness supply the height substrate."
strata_touched:
  - D5/S3/Combinatorics/Geometry/MiuraHeightEnvelope
  - D5/S3/Combinatorics/Geometry/MiuraResidualCount
  - D5/S3/Combinatorics/Geometry/MiuraStripRigidity
license: CC-BY-4.0
triage: anchor
---

# Miura-ori degree sequences and finite height functions

For each split a+b=d with d at least five and 1 at most a at most b, the
residual class consists of normalized integer height functions with absolute
edge differences exactly one, exactly a strict minima and b strict maxima,
and no single boundary side containing every minimum. Conjecture 8.3, with
Lemma 8.2, asks for one rational bivariate polynomial of total degree at most
d-3 counting this class for every m,n at least 2d-1.

The finite envelope expresses each value as an attained minimum of upward
Manhattan cones and an attained maximum of downward cones. The formal source
is Chakshu Gupta's public lab repository, immutable commit
0bf8c67f7f5a2e8d44fb88c19fb80337221bbc11, subtree
math/gupta2026degseq/lean (tree 8beb89d4466cb8551abc92d0405972edc2edf116).
The copied declarations and adaptations are identified in their Lean sources;
full license and attribution are in docs/reports/miura-suppliers/.

The strip rigidity lemma is a consequence of the finite envelope on a
rectangular restriction. A restricted maximum before the exit row is an
ambient maximum when all outward edges above the strip are downhill.
No proof of the complete residual polynomial assertion is provided here.

## Verified locator

DOI: https://doi.org/10.48550/arXiv.2607.05567

Source: https://arxiv.org/abs/2607.05567v3

Conjecture 8.3 and Lemma 8.2 specify the residual polynomial assertion; Section 7 identifies its count as the configurations whose minima do not all lie on one common side.
