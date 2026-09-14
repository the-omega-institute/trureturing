---
bibkey: codex2026correlationtax
authors: Codex implementation worker
year: 2026
title: Coherent premeasurement and the correlation-tax identity
doi: null
url: https://github.com/the-omega-institute/trureturing
claim: A repository derivation of coherent-copy marginals, entropy preservation, and the correlation-tax identity.
strata_touched:
  - D5/S3/Quantum/Information/CoherentCopyCorrelationTax
license: citation-only
triage: anchor
---

# Coherent premeasurement

## Verified locator

This entry records the repository derivation at the canonical repository locator:
https://github.com/the-omega-institute/trureturing
The formal source is `D5/S3/Quantum/Information/CoherentCopyCorrelationTax.lean`.
It treats the coherent matrix V rho V*, where V sends each basis vector i to (i,i).
The formal derivation uses the repository's density states, partial traces, entropy,
and relative entropy. The mathematical identity is not claimed to be novel.

The derivation retains all off-diagonal entries on the correlated subspace. Tracing
out either tensor factor removes those coherences, while the entropy of the joint
state equals the input entropy. The construction is distinct from the classical
mixture of records, whose joint entropy already equals the diagonal entropy.
