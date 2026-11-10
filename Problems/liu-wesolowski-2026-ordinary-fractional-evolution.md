---
slug: liu-wesolowski-2026-ordinary-fractional-evolution
bibkey: liuwesolowskithompsongupira2026fractional
doi: null
url: https://arxiv.org/abs/2610.01940v1
triage: conjecture
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/FractionalEvolutionPhaseObstruction.result
---

# Prescribed fractional evolution with ordinary oracle access

The source is Liu, Wesolowski, Thompson, Gu and Pira, Optimal query complexity for fractional quantum evolution, arXiv:2610.01940v1. Section V asks:

> It is unclear whether the matching upper bound survives without controlled access.

The binding proposition and credited ordinary-query phase pair are in issue [22813](https://github.com/the-omega-institute/trureturing/issues/22813), with the fixed event in [its immutable registration](https://github.com/the-omega-institute/trureturing/issues/22813#issuecomment-6772178931). The proposal belongs to the original research and search seats identified there. Global-phase blindness is established prior art and is not claimed as new.

The exact proposition first quantifies a universal positive real C, then every allowed t, delta, epsilon and positive dimension. It permits every finite nonzero workspace and every natural query count, including zero. Fixed signs and unitary gates precede all U,H. Queries are identity tensor U or its adjoint. The target is the complete initialized output channel of exp(itH) on the half-open branch [delta,2 pi), measured in the existing unhalved reference-stabilized Harrow diamondNorm.

The Lean source contains the original binding definitions and a proposed proof of their literal negation. The phase-pair route uses d=2, t=delta=1/2, epsilon=1/4, and opposite-order diagonal logarithms with entries pi/2 and 3 pi/2. The required final statement is Trureturing.OpenProblems.FractionalEvolutionPhase.result : Not Trureturing.OpenProblems.FractionalEvolutionPhase.claim.

This dossier records no completed settlement, independent theorem review, frozen membership or solved-problem credit. The controlled upper bound and ordinary-query lower bound remain outside the refutation. The bounded prior-source readings supplied with the registration do not constitute exhaustive absence of a prior promised-domain settlement.
