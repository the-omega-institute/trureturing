---
bibkey: song2025tabletop
authors: M. Song, H. Kwon and V. Scarani
year: 2025
title: "Exact and approximate conditions of tabletop reversibility: when is Petz recovery cost-free?"
doi: 10.1088/2058-9565/aea92d
url: https://arxiv.org/abs/2510.26895v1
claim: "Section V, open question 2 asks whether a steady prior always makes the fixed dilation tabletop time-reversible; an explicit qutrit instance refutes this assertion even for a positive definite prior."
strata_touched:
  - D5/S3/Quantum/Information/SongKwonScaraniSteadyPriorReversibility
license: citation-only
triage: anchor
---

# Exact and approximate conditions of tabletop reversibility

M. Song, H. Kwon and V. Scarani, arXiv:2510.26895v1; Quantum Sci. Technol. 11 (2026) 045057. Quotations below refer to the arXiv v1 text.

## Verified locator

DOI: 10.1088/2058-9565/aea92d

Source: https://arxiv.org/abs/2510.26895v1

## Definitions

Equation (1), page 2:

> N(•) = Tr_E[U_SE (• ⊗ ξ_E) U_SE†]

Definition 1, equation (2), page 2:

> N̂_γ^(P)(•) ≡ √γ N†( (1/√N(γ)) • (1/√N(γ)) ) √γ.

Definition 2, equation (3), page 2:

> N̂_ξ′^(T)(•) ≡ Tr_E[U_SE† (• ⊗ ξ′_E) U_SE].

Definition 2, equation (4), page 2: the channel is tabletop time-reversible for a prior γ

> if there exists ξ′ = ξ′_γ such that its Petz recovery map N̂_γ^(P) is given by N̂_γ^(P) = N̂_ξ′^(T)

## Open question

Section V, question 2, page 9:

> In all of the examples we considered, a dynamics appears to be tabletop time-reversible whenever a prior state is a steady state. We do not have a proof that this is true in general, and leave it for a future investigation.

The formal assertion uses arbitrary finite matrix index types S and E, the forward channel Tr_E[U(X ⊗ ξ)U†], its Hilbert–Schmidt adjoint Tr_E[U†(Y ⊗ 1)U(1 ⊗ ξ)], and the Petz formula above. The prior is positive definite and trace one. The environmental state is positive semidefinite and trace one. The reverse uses the same interaction U and allows any positive semidefinite trace-one environmental state ξ′.

## Scope and evidence

The module proves the negative answer for S = E = Fin 3 at the single interaction with exchange coefficient −i. The two reverse transition populations must agree, whereas the Petz populations are 13/51 and 7/39. The continuous Hamiltonian family is outside this Lean result. The positive examples in the source have additional hypotheses.

The numerical experiment is in the-omega-institute/trureturing-experiments, commit 2f862f6a6250e3487932fb4a2b41243a41d57860, file docs/reports/song-kwon-scarani-2025-steady-prior-reversibility/check.py, SHA-256 82b42509dcab4625b08ced9ce46a2cbee2a93850f3892c0e1dc8ce4e4d1a5ce8. Running `python3 /tmp/op-skt2510/check.py` on that exact file exits 0 with ALL_CHECKS_OK. Its continuous-family and random-dilation readings are numerical evidence.

The preregistration is issue [#20652](https://github.com/the-omega-institute/trureturing/issues/20652). Completeness of the literature search and preservation of question 2 in the journal version are ASSUMED-UNVERIFIED. The search recorded there distinguishes fixed-interaction reversal from constructing a different reversible dilation.
