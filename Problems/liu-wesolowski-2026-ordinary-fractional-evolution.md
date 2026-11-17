---
slug: liu-wesolowski-2026-ordinary-fractional-evolution
bibkey: liuwesolowskithompsongupira2026fractional
doi: null
url: https://arxiv.org/abs/2610.01940v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/FractionalEvolutionPhaseObstruction.result
---

# Prescribed fractional evolution with ordinary oracle access

## Problem

The source is Liu, Wesolowski, Thompson, Gu and Pira, Optimal query complexity for fractional quantum evolution, arXiv:2610.01940v1. Section V asks:

> It is unclear whether the matching upper bound survives without controlled access.

This dossier anchors exactly the positive ordinary-query upper-bound statement fixed in issue [22813](https://github.com/the-omega-institute/trureturing/issues/22813) and [its immutable registration](https://github.com/the-omega-institute/trureturing/issues/22813#issuecomment-6772178931). The credited ordinary-query phase pair and the original proposal's attribution are recorded there. Global-phase blindness is established prior art and is not claimed as new.

The exact proposition first quantifies a universal positive real C, then every real 0<t<1, 0<delta<1, 0<epsilon<1/2 and positive natural dimension d. It asserts the existence of natural m,N and a fixed circuit with workspace dimension m+1, at most C delta^-1 log(1/epsilon) queries, and uniform success. Fixed signs and unitary inter-query gates precede all U,H. Each query is identity on the entire workspace tensor U or its adjoint. Success quantifies every Hermitian H and U=exp(iH) whose real spectrum lies in the half-open branch [delta,2 pi). It compares the complete initialized output channels of A_U J and J exp(itH), where J maps psi to workspace basis zero tensor psi, in the existing unhalved reference-stabilized Harrow diamondNorm with error at most epsilon. No workspace output is discarded, and N may be zero.

## Motivation

The controlled-query upper bound motivates the source's question about removing controlled access. The formal motivation is D5/S3/Quantum/QuantumChannels/FractionalEvolutionPhaseObstruction.result, the literal negation of the registered positive statement. This links the ordinary-access question to its precise circuit and spectral-branch conventions.

## Gap

Ordinary access does not supply a controlled oracle call. The registered positive assertion must work uniformly for every promised logarithm while retaining the prescribed fractional branch and full output. The fixed phase-pair refutation closes that assertion; it does not replace the controlled-access theorem or settle every ordinary-access formulation.

## Route

The established proof uses d=2, t=delta=1/2 and epsilon=1/4. The two logarithms are diagonal with entries pi/2 and 3 pi/2 in opposite orders, yielding U=diag(i,-i) and -U; both satisfy the half-open spectral promise. For every finite workspace, every N and every fixed circuit, replacing U by -U multiplies its ordered run by (-1)^N, including adjoint queries. The initialized implementation channels therefore agree.

On the equal-superposition target input with reference basis zero, the two ideal stabilized outputs at t=1/2 are orthogonal pure states. Their unhalved trace-norm separation is two. Uniform success would place the common implementation within one quarter of each target, so the triangle inequality would give two at most one half. The contradiction proves the literal negation without using the query-count bound.

## Falsifier

The positive event would require a universal C and successful circuits for all parameters and all promised U,H in the stated quantifier order. The fixed admissible pair above is its falsifier. A circuit for one oracle, controlled access, a different branch convention or a comparison discarding workspace output does not instantiate that event.

## Evidence

The exact Lean statement is Trureturing.OpenProblems.FractionalEvolutionPhase.result : Not Trureturing.OpenProblems.FractionalEvolutionPhase.claim. The corresponding Scribe result describes the same literal negation and binds this dossier with ResolutionKind.Refuted. The source anchors are Definitions 1-3, the Section V uncontrolled-access paragraph and Appendix B; the verified TeX locator is in Library/QuantumChannels/liuwesolowskithompsongupira2026fractional.md.

The proof reuses the frozen HarrowParallelChernoffExponentRefutation diamondNorm, FiniteTraceDistance trace-norm inequalities and orthogonal-state separation, and FiniteKrausChannel matrix-map operations. Its pinned Mathlib suppliers cover the list fold, matrix exponentials, spectra and positivity. These are reused results, not claims of a new general method.

## Triage

Theorem: the established result refutes exactly the registered universal positive assertion. Its proof_shape is bind-only and its admission_basis is open-problem-resolution under issue 22813. The retained private theorem helpers are consumed on the proof path to the unique public designated result; they carry no separate new-method credit.

Established failed mechanism: ordinary queries identify the sign-related implementation channels, while the prescribed fractional targets in the fixed witness are separated. Increasing the finite query count or workspace does not repair this witness. The source's controlled-query upper bound and ordinary-query lower bound survive as separate source claims outside this refutation; no new proof of either is asserted here.

Unproved neighboring statements: an all-t optimal error floor, a classification of alternative branch promises, and upper bounds under additional access or phase-reference assumptions are not conclusions of this result. Other Section V questions remain outside this dossier's single anchor.

## ASSUMED-UNVERIFIED

The bounded prior-source readings associated with the registration do not establish exhaustive absence of an earlier promised-domain settlement. Uninspected literature remains unverified; no global novelty or priority claim is made. The correspondence to the source uses the exact fixed ordinary-query substitution and branch convention above, and does not assert equivalence with different oracle models or physical access assumptions.
