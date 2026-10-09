---
bibkey: leanpool2026hermitianeigenvalueperturbation
authors: Jon Crall and LeanPool contributors
year: 2026
title: LeanPool DavisKahan Hermitian eigenvalue perturbation proofs
doi: null
url: https://github.com/LeanPool/lean-pool/blob/bbc67ff1e3ac4fc6a969daf42985a0d8f988d0b8
claim: Courant–Fischer subspace intersection proves the sorted Hermitian eigenvalue perturbation bound; the Euclidean operator norm is at most the dimension times an entrywise bound.
strata_touched:
  - D5/S3/SpectralTopology/HermitianEigenvaluePerturbation
license: Apache-2.0
triage: anchor
---

# Hermitian eigenvalue perturbation

## Verified locator

DOI: null
Source: https://github.com/LeanPool/lean-pool/blob/bbc67ff1e3ac4fc6a969daf42985a0d8f988d0b8

The source units are DavisKahan/ForTauCeti/Analysis/InnerProductSpace/CourantFischer.lean
and DavisKahan/ForTauCeti/Analysis/Matrix/EntrywiseOpNorm.lean. The companion
EntrywiseEigenvalue.lean combines their bounds. All four source units, including BasisSpan.lean, are pinned to this commit.
Their SHA-256 file identities appear in the ported repository module.
The retained LICENSE and NOTICE are in docs/reports/brooks-suppliers/daviskahan-LICENSE.txt
and docs/reports/brooks-suppliers/daviskahan-NOTICE.txt.

For Hermitian complex matrices with decreasingly sorted eigenvalues, each eigenvalue
changes by at most the Euclidean operator norm of the difference. For an n by n
matrix whose entries have norm at most ε, that operator norm is at most n ε.
These bounds do not assert an eigenvector perturbation theorem.
