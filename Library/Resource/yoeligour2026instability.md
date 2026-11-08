---
bibkey: yoeligour2026instability
authors: Goni Yoeli and Gilad Gour
year: 2026
title: Instability as a Quantum Resource
doi: 10.48550/arXiv.2602.18323
url: https://arxiv.org/abs/2602.18323v1
claim: "The Open directions question after Eq. (29) asks whether destruction-covariant channels themselves arise as fixed points of an idempotent superchannel."
strata_touched:
  - D5/S3/QuantumChannels/YoeliGourDestructionSuperchannelRefutation
license: citation-only
triage: anchor
---

# Instability as a Quantum Resource

## Verified locator

DOI: 10.48550/arXiv.2602.18323

Source: https://arxiv.org/abs/2602.18323v1

The target is the unnumbered Open directions question on PDF page 5, following Eq. (29) on page 4:

> Moreover, a key open question is whether destruction-covariant channels themselves arise as fixed points of an idempotent superchannel.

The Framework on PDF page 1 specifies the systems and their admissibility:

> The resource theory of instability therefore considers systems as pairs (A, Δᴬ), where A ≅ ℂᵈ and Δᴬ is an idempotent “destruction” channel.

> We assume Δᴬ fixes at least one full-rank state, ensuring the Heisenberg dual Δᴬ* is a faithful conditional expectation (a standard operator-algebraic concept, see Appendix A and [40–46]).

Eq. (1), PDF page 1, defines destruction covariance:

> In instability theory, we take the free operations between systems A and B to be the destruction-covariant channels 𝒩 obeying
>
> 𝒩ᴬ→ᴮ ∘ Δᴬ = Δᴮ ∘ 𝒩ᴬ→ᴮ.

The affirmative assertion uses exact equality of the fixed CPTP set with the destruction-covariant CPTP set, for every pair of nonzero admissible systems. The superchannel acts on the full complex-linear map space and is idempotent there. Complete positivity includes arbitrary auxiliary systems. Full-rank states are positive definite trace-one matrices.

The qutrit refutation uses complete dephasing at both ends. Fixing its destruction-covariant channels forces the superchannel to be identity, which fixes channels that fail destruction covariance. This does not refute the distinct Eq. (29) construction: its fixed channels for complete dephasers are classical channels.

The target is specifically v1. The v2 Open directions passage omits the question. Completeness of the prior-art screen is ASSUMED-UNVERIFIED; the accepted journal manuscript and final Cambridge resource-theory book have not been compared with this question. The source and literature scope are recorded in issue #24013.

The exact finite checks accompanying that issue are in `the-omega-institute/trureturing-experiments`, commit `b44213ea6ad71c525c5482eed0f6bf87ffc99db7`, at `docs/reports/yoeli-gour-destruction-superchannel/check.py` (SHA-256 `3c78372a0bf35b7b8ac9c17fca121bad2fa7319a5f1c0aa04e98093a84068c61`). The command is `python3 docs/reports/yoeli-gour-destruction-superchannel/check.py`; its recorded exit is 0. These finite computations are distinct from the Lean proof.
