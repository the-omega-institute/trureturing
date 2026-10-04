---
bibkey: liwu2026j1j2rings
authors: Zimeng Li; Ning Wu
year: 2026
title: "Exact momentum-space analysis of small spin-1/2 J1-J2 rings"
doi: 10.48550/arXiv.2604.23149
url: https://arxiv.org/abs/2604.23149v1
claim: "The Bloch state whose N/2 down spins occupy successive sites has the largest weight in the HKNN ground state for arbitrary even N."
strata_touched:
  - D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight
license: citation-only
triage: anchor
---

# The block Bloch component of the HKNN state

Zimeng Li and Ning Wu, *Exact momentum-space analysis of small spin-1/2 J1-J2 rings*,
arXiv:2604.23149v1 (2026).

The explicit conjecture after Eq. (47), p. 12, reads:

> Thus, we conjecture that this property holds for arbitrary even number N, i.e., the Bloch state |ξ1,1,...,1(−π)⟩ (there are N/2 − 1 1’s) should have the largest weight in |ψHKNN(N)⟩.

The state in Eq. (6), p. 4, is:

> |ψHKNN⟩ = Σ_{aj<bj and a1<a2<···<aN/2} [a1, b1] · · · [aN/2, bN/2], (6)
>
> where the sum is over all partitions of {1, 2, . . . , N} into pairs without regard to order.

The singlet convention after Eq. (4), p. 3, is:

> [i, j] ≡ | ↑⟩i | ↓⟩j − | ↓⟩i | ↑⟩j is a singlet state on sites i and j.

The normalized Bloch states of Eq. (7), p. 4, are:

> |ξ1(k)⟩ = e^{ik/2}/√6 Σ_{j=0}^{5} e^{ikj} T^j |1, 2⟩, |ξ2(k)⟩ = e^{ik}/√6 Σ_{j=0}^{5} e^{ikj} T^j |1, 3⟩, |ξ3(k)⟩ = e^{i3k/2}/√3 Σ_{j=0}^{2} e^{ikj} T^j |1, 4⟩, (7)

The carrier uses the existing Boolean type Stationing(2m), with N=2m with m>=1 and site index i for paper site i+1.
False is spin up; true is spin down. Each pair is oriented with its smaller
endpoint first, and each pair partition occurs once. The full-period Bloch sum
adds repeated orbit points as amplitudes. Dividing by its Hilbert norm gives
the same ray as the orbit-period sum whenever it is nonzero; the paper excludes
momenta whose Bloch sum vanishes. The weight divides the squared overlap by
both squared Hilbert norms. Momentum t=m is pi, equivalent to -pi.

The mathematical conclusion concerns the explicitly defined vector of Eq. (6).
Its identification as a Hamiltonian ground state is supplied by the source.
The large-N weight gap, the all-N runner-up and the analogous Majumdar-Ghosh
comparison are separate open questions.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2604.23149
- arXiv: https://arxiv.org/abs/2604.23149v1
