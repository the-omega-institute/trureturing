---
bibkey: eldar2003detectors
authors: Yonina C. Eldar, Alexandre Megretski, George C. Verghese
year: 2003
title: Designing optimal quantum detectors via semidefinite programming
doi: 10.1109/TIT.2003.809510
url: https://arxiv.org/abs/quant-ph/0205178
claim: An upper bound for finite minimum-error detection is the trace of an operator that dominates each prior-weighted signal density matrix.
strata_touched:
  - D5/S3/Quantum/PureState/PhaseRecordMemory
license: citation-only
triage: anchor
---

# Dual bounds for finite quantum detection

## Verified locator

In IEEE Transactions on Information Theory 49(4), 1007–1012, Eldar, Megretski and Verghese derive the finite minimum-error discrimination dual. In the arXiv version, Eq. (14) is the trace-gap identity. Eqs. (15)–(18) minimize `Tr X` over Hermitian `X` with `X ⪰ pₓρₓ` for each signal and identify the minimum with optimal success. Eqs. (19)–(20) give complementary slackness, and Eq. (26) bounds optimal effect ranks. [DOI](https://doi.org/10.1109/TIT.2003.809510) · [ArXiv source](https://arxiv.org/abs/quant-ph/0205178)

## Phase-record application

For a flat orthogonal phase matrix of size `N`, let `W` have the normalized phase vectors as its columns. For a positive amplitude profile `t` with sum of squares one and sum `S`, the uniform prior-weighted signal matrix is `diag(t) W`. The square root of its Gram matrix is `W† diag(t) W` and has diagonal `S/N`. The constant-diagonal criterion makes the phase PVM optimal and gives success `g = S²/N`. The criterion for linearly independent signals is in §II, Theorem 1 following Eq. (4) of Sasaki, Kato, Izutsu and Hirota. For the Walsh case, see also the repository’s Eldar–Forney note on Theorem 4 for geometrically uniform ensembles. [Sasaki et al.](https://arxiv.org/abs/quant-ph/9801012) · [Eldar–Forney Library note](eldarforney2001quantumdetection.md)

Kennedy proves uniqueness of the optimal decision POVM on the span of linearly independent pure signals in “Uniqueness of the Optimum Receiver for the M-ary Pure State Problem,” MIT RLE Quarterly Progress Report 113 (April 15, 1974), pp. 129–130. If a channel attains the full-carrier optimum, its pulled-back decoder must be the phase PVM. Applying that decoder to the encoded phase basis tests distinguishes `N` labels perfectly. Nayak’s Theorem 2.4(2) bounds every whole-label decoding probability by the prior mass of the most likely `2^q` labels for a `q`-qubit encoding. For uniformly distributed labels and arbitrary integer dimension `M`, the corresponding bound is `M/N` directly from `ρₓ ⪯ I` and `Σₓ Tr Dₓ = M`. Thus perfect discrimination forces `M ≥ N`. Measuring the phase PVM at the encoder and storing its outcome in `N` orthogonal memory states attains `g`. The threshold is a corollary of these known ingredients. [Kennedy, pp. 129–130](https://hdl.handle.net/1721.1/56461) · [Nayak, Theorem 2.4(2)](https://arxiv.org/abs/quant-ph/9904093)

The formal proof uses `X = (S/N) diag(t)` and proves that its slack against `ρₓ/N` dominates `(S m/N)(I − Pₓ)`, where `m = minᵢ tᵢ` and `Pₓ` projects onto the normalized phase row. Pairing the slack with the encoder’s pulled-back effects gives the explicit penalty `g − g_M ≥ (1 − M/N) S m`. The literature checked for this packet yielded no statement of this quantitative phase-memory penalty for arbitrary CPTP encoders and output POVMs.

An AURIC projective tree downstream of preprocessing is an application of the same bound. Its channel generates the binary flag from the preprocessing output. Pulling the final POVM on the flag and residual register back through that channel preserves the score and gives a POVM on the preprocessing register of dimension `M`. The same `M/N` cap and phase penalty therefore apply even though the flagged output space has dimension `2M`.
