---
bibkey: rana2016coherence
authors: Swapan Rana, Preeti Parashar, Maciej Lewenstein
year: 2016
title: Trace-distance measure of coherence
doi: 10.1103/PhysRevA.93.012110
url: https://arxiv.org/abs/1511.01854v2
claim: "Conjecture 7. For all states ρ, C_{l1}(ρ) ≥ C_r(ρ)."
strata_touched:
  - D5/S3/Divergence/CoherenceL1RelativeEntropyBound
license: citation-only
triage: anchor
---

# Trace-distance measure of coherence

## Verified locator

DOI: https://doi.org/10.1103/PhysRevA.93.012110

Source: https://arxiv.org/abs/1511.01854v2

Section III.2, printed p. 5, verbatim:

> Conjecture 7. For all states ρ,
>
> C_{l1}(ρ) ≥ C_r(ρ).

Section II, Eq. (3b), p. 2 gives the l1 norm of coherence as the sum of absolute
values of off-diagonal entries. Section III, after Eq. (13), p. 4 states:

> The minimization could be solved analytically [2], leading to
> Cr(ρ) = S(ρdiag)−S(ρ), where S(ρ) = − Tr(ρ log₂ ρ) is the von
> Neuman entropy.

The finite-dimensional state is
positive semidefinite and has unit trace. Singular states are included.

The repository theorem establishes the conjecture for every finite dimension.
Sequential coordinate pinching gives the stronger estimate
Cᵣ(ρ) ≤ 2 ∑k (∑j>k |ρkj|²)^(1/2) ≤ Cₗ₁(ρ).
Literature priority beyond the cited source and the screened follow-ups remains
ASSUMED-UNVERIFIED; this note makes no claim of exhaustive literature coverage.
