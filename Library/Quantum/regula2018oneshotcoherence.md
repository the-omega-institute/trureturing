---
bibkey: regula2018oneshotcoherence
authors: Bartosz Regula, Kun Fang, Xin Wang, Gerardo Adesso
year: 2018
title: One-shot coherence distillation
doi: 10.1103/PhysRevLett.121.010401
url: https://arxiv.org/abs/1711.10512v3
claim: The dual formula for the m-distillation norm maximizes overlap under simultaneous infinity-norm and Euclidean-norm caps, and Theorem 2 evaluates it for pure states.
strata_touched:
  - D5/S3/Quantum/PureState/DistillationProfile
license: citation-only
triage: anchor
---

# Scalar optimization for phase-memory profiles

## Verified locator

Regula, Fang, Wang and Adesso, *Physical Review Letters* 121, 010401 (2018). In arXiv v3, supplement Eq. (S12) on PDF page 8 gives the dual maximization of the absolute overlap with a vector of infinity norm at most 1 and Euclidean norm at most √m. Theorem 2 on PDF page 3 gives the sorted closed form for integer 1 ≤ m ≤ d. Supplement Eq. (S13) on PDF page 8 displays the optimizing vector used in the lower bound. [DOI](https://doi.org/10.1103/PhysRevLett.121.010401) · [ArXiv v3](https://arxiv.org/abs/1711.10512v3) · [Primary PDF, Theorem 2](https://arxiv.org/pdf/1711.10512v3#page=3) · [Primary PDF, Eqs. (S12)–(S13)](https://arxiv.org/pdf/1711.10512v3#page=8)

## Scope

For nonnegative amplitudes tᵢ one may take the dual vector nonnegative. With xᵢ = √dᵢ, Eq. (S12) becomes the maximization of the sum of tᵢ√dᵢ over 0 ≤ dᵢ ≤ 1 and sum dᵢ ≤ m. Its scalar optimum and clipping are prior literature. Theorem 4 and Eq. (16) on PDF page 4 identify the squared norm divided by m with one-shot pure-state coherence-distillation fidelity under MIO, DIO, SIO and IO. The finite phase-memory result uses this scalar optimum in a guessing problem with one common CPTP encoder for an ensemble and one POVM on the resulting memory. The translate-mixture construction supplies that operational step for Fourier characters. [Primary PDF, Theorem 4 and Eq. (16)](https://arxiv.org/pdf/1711.10512v3#page=4)
