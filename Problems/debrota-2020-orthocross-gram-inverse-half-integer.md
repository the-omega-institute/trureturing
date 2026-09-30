---
slug: debrota-2020-orthocross-gram-inverse-half-integer
bibkey: debrota2020varieties
doi: 10.1142/S0219749920400055
url: https://arxiv.org/abs/1812.08762v5
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurement/OrthocrossGramHalfInteger.result
---

# The inverse Gram matrix of an orthocross MIC is half-integral

## Problem

J. B. DeBrota, C. A. Fuchs and B. C. Stacey (arXiv:1812.08762, quant-ph;
Int. J. Quantum Inf. 19 (2021) 2040005) study minimal informationally complete
measurements (MICs) and their Gram matrices `G_{ij} = tr(E_i E_j)`. For an
orthonormal basis `{|j⟩}` of `ℂ^d`, the orthocross MIC has elements
`E_α = Ω^{−1/2} Π_α Ω^{−1/2}`, where `Π_α` runs over the `d²` projectors onto
`|j⟩`, `(|j⟩ + |k⟩)/√2` and `(|j⟩ + i|k⟩)/√2` (`j < k`) and `Ω = Σ_α Π_α`. The
paper states:

> Conjecture. For any orthocross MIC, the entries in G^{−1} are integers or
> half-integers.

Issue #11385 fixes the reading: every dimension `d` and every orthonormal
basis (the columns of a unitary `U`), `Ω^{−1/2}` the positive square root of
`Ω⁻¹`, and "integers or half-integers" as `2 (G⁻¹)_{αβ} ∈ ℤ`, with `G`
invertible.

## Motivation

The inverse Gram matrix of a MIC is the matrix that turns the outcome
probabilities of the MIC back into the state, so its entries control the
probabilistic representation of quantum theory that the MIC provides. The
orthocross MICs were introduced by Caves, Fuchs and Schack in their proof of
the quantum de Finetti theorem. The frozen
declaration `D5/S3/Quantum/Measurement/OrthocrossGramHalfInteger.result`
proves the conjecture for every `d` and every orthonormal basis.

## Gap

Issue #11385 preregisters the reading, the route and the literature check. The
conjecture is in arXiv v5 (2020-09-21), after DeBrota's dissertation
(2020-08). INSPIRE lists 30 citing records; the sources of all 26 with arXiv
identifiers were searched, and the two that mention orthocross MICs
(arXiv:1911.07386, which notes that open conjectures remain, and
arXiv:2312.11946, an exercise on the Born matrix) do not address the
conjecture.

These readings are `not-found-in-searched-scope`; they do not establish an
exhaustive worldwide literature search, priority, or the absence of an
independent answer.

## Route

1. `Ω` is the identity plus a positive semidefinite matrix, so it is positive
   definite, `(Ω^{−1/2})² = Ω⁻¹` and `G_{αβ} = tr(Π_α Ω⁻¹ Π_β Ω⁻¹)`; a unitary
   change of basis leaves `G` unchanged.
2. In the standard basis `Ω` has `d` on the diagonal, `(1 − i)/2` above it and
   `(1 + i)/2` below it. The explicit matrices
   `D_T = E_jk + E_kj`, `D_V = i(E_kj − E_jk)` and `D_X = E_jj − E_jj C − C E_jj`
   (`C` the off-diagonal part of `Ω`) satisfy `tr(D_α Π_β) = δ_{αβ}`.
3. The `d²` matrices `D_α` are linearly independent, hence a basis, and every
   `Y` equals `Σ_β tr(Y Π_β) D_β`; therefore `G M = 1` with
   `M_{βγ} = tr(D_β Ω D_γ Ω)`, so `G` is invertible and `G⁻¹ = M`.
4. `(1 − i) Ω` and `(1 − i) D_α` have Gaussian-integer entries and
   `4 = (1 + i) i (1 − i)³`, so every entry of `4 Ω D_γ Ω` is `1 + i` times a
   Gaussian integer.
5. With `Z = Ω D_γ Ω` Hermitian, `M_{T γ} = Z_kj + Z_jk`,
   `M_{V γ} = i Z_jk − i Z_kj` and
   `M_{X γ} = Z_jj − Σ_q (C_jq Z_qj + C_qj Z_jq)`; writing
   `4 Z_pq = (1 + i)(a + bi)`, each `2 M` is an integer.

## Falsifier

Every square root `S` with `S² = Ω⁻¹` gives the same `G`, so the choice of
root does not affect the statement. The statement is specific to the cross
vectors: replacing `e_j + i e_k` by `e_j + ω e_k` (`ω = e^{2πi/3}`) or
`e_j + e_k` by `e_j + 2 e_k` breaks half-integrality numerically, so a reading
with other cross vectors would change the answer.

## Evidence

Floating-point `G⁻¹` for `d = 1, …, 7` and exact values of `M` for
`d = 5, 6, 7` (issue #11385) agree with `2G⁻¹ ∈ ℤ`; the stronger claim that
`G⁻¹` is integral fails for `d = 2, 4, 5, 6`.

The canonical source is
`D5/S3/Quantum/Measurement/OrthocrossGramHalfInteger.lean`. Its public
declarations are `vec`, `weight`, `proj`, `frame`, `mic`, `gram`, `claim` and
`result`. The frozen module state has statement identity
`sha256:b3c80f6c578b5ba7863ac09b6d2fe4a85feba374a392d78d375c9867f9479127`.
The result declaration has statement identity
`sha256:29df7724633883a3e6f8bf6de9fd00488330da5fe1366c3eb8641bd248b0552e`.
The Freeze event is
`sha256:393151d84845e37d659e1c949e5284b42f1ee6a442f7a19885be2e9adc78375c`
and has no project-level frozen prerequisites. The proof uses only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`,
`native_decide`, or new axiom.

## Triage

Tier 1 conjecture from a published quant-ph paper, preregistered in issue
#11385 before any Lean. `theorem`; resolution `proved`. The public theorem has
`proof_shape: content`; its escape witnesses are the dual-basis inverse
formula `G M = 1` and the divisibility of `4 Ω D_γ Ω` by `1 + i` (form (1)).
Its admission basis is `open-problem-resolution`. Utility `none`.

## ASSUMED-UNVERIFIED

The published journal text and DeBrota's dissertation (HTTP 403) were not
read, so it is unverified whether either proves the conjecture. The bounded
literature check does not establish exhaustive worldwide novelty, priority,
or the absence of an independent answer. The Lean kernel does not
authenticate the external source or its version history.
