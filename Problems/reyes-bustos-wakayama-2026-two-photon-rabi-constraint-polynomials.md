---
slug: reyes-bustos-wakayama-2026-two-photon-rabi-constraint-polynomials
bibkey: reyesbustos2026twophotonrabi
doi: 10.48550/arXiv.2609.00750
url: https://arxiv.org/abs/2609.00750v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Dynamics/TwoPhotonRabiConstraintPolynomials.result
---

# The constraint polynomials of the two-photon Rabi model at and beyond the critical coupling

## Problem

Reyes-Bustos and Wakayama define, for the two-photon asymmetric quantum Rabi
model with parity `ρ ∈ {0, 1}`, bias `ε`, `x = (2g)^2` and `y = Δ^2`, the
polynomials

> P_0 = 1, P_1 = y + 2x(4N + 2ρ + 2ε − 1) − 4(1 + ε),
> P_k = (y + 2xk(4N + 2ρ − 2k + 2ε + 1) − 4k(k + ε)) P_{k−1}
>   − 4k(k − 1)(2(N − k + 1) + ρ)(2(N − k + 1) + ρ − 1) x P_{k−2},

(Definition 4.1 of arXiv:2609.00750v1) and state Conjecture 4.5:

> We have P_N^{(N,ρ,ε)}(1, y) = ∏_{n=1}^{N} (y + 2n(2n + 2ρ − 1)). Moreover,
> for x > 1, the polynomial P_N^{(N,ρ,ε)}(x, y) has positive coefficients,
> and therefore, no positive roots for y.

Issue #10148 fixes the readings: `P_k` is a real polynomial in `y` with real
parameters `x` and `ε`; the first statement is taken for every real `ε`; the
second statement is taken for `ε ≥ 0` and means that the coefficients of
`y^0, …, y^N` are all positive and that `P_N^{(N,ρ,ε)}(x, y) ≠ 0` for every
`y > 0`. The source derives its constraint condition
for `ε ≥ 0` and writes `P_N^{(N,ρ,±ε)}` for the two signs, while the
conjecture writes `+ε` only.

## Motivation

`x = 1` is the critical coupling `g = 1/2` where the two-photon model acquires
continuous spectrum, and the absence of positive roots for `x > 1` matches the
absence of Juddian points past the critical coupling. The frozen declaration
`D5/S3/Quantum/Dynamics/TwoPhotonRabiConstraintPolynomials.result` proves both
statements: the product formula for every `N`, `ρ ∈ {0, 1}` and real `ε`, and,
for every `x > 1` and `ε ≥ 0`, the positivity of all coefficients and the
absence of positive roots in `y`.

## Gap

Issue #10148 preregisters the conjecture and its literature check. arXiv lists
only version 1 (2026-09-01) and no journal reference. Semantic Scholar reports
no citing paper. The source leaves "a complete description of this as an open
problem" immediately before the conjecture.

These readings are `not-found-in-searched-scope`; they do not establish an
exhaustive worldwide literature search, priority, or the absence of an
independent proof.

## Route

Part (a). At `x = 1` the bias cancels from the recursion. With
`λ_n = 2n(2n + 2ρ − 1)` and `Q_i = ∏_{n ≤ i} (y + λ_n)`, induction on `k`
shows

`P_k(1, y) = Σ_{i ≤ k} C(k, i) · 4^{k−i} · ∏_{l < k−i} (N − i − 1 − l) · ∏_{l < k−i} (k + 1 − l) · Q_i`.

Since `y Q_i = Q_{i+1} − λ_{i+1} Q_i`, the coefficients must satisfy the
recursion `c(k, i) = c(k−1, i−1) + (a_k − λ_{i+1}) c(k−1, i) − b_k c(k−2, i)`.
Writing `k = i + j + 2` and `N = i + j + r + 2`, this reduces to a polynomial
identity whose defect is `ρ(ρ − 1)(j + 1)(j + 2)`, which vanishes for
`ρ ∈ {0, 1}`. At `k = N` each coefficient with `i < N` contains the factor
`N − N = 0`, so `P_N(1, y) = Q_N`.

Part (b). Let `J(x)` be the symmetric tridiagonal matrix with diagonal
`d_k(x) = 2xk(4N + 2ρ − 2k + 2ε + 1) − 4k(k + ε)` and off-diagonal
`√(b_k x)`, where `b_k = 4k(k − 1)(2(N − k + 1) + ρ)(2(N − k + 1) + ρ − 1) ≥ 0`
for `2 ≤ k ≤ N`. Expanding along the first row gives
`det(y + J_{k+2}) = (y + d_{k+2}) det(y + J_{k+1}) − b_{k+2} x det(y + J_k)`,
so `P_N(x, y) = det(y + J(x)) = ∏ (y + μ_i)` over the eigenvalues `μ_i` of
`J(x)`. By part (a) the eigenvalues of `J(1)` are the numbers `λ_n > 0`, so
`J(1)` is positive definite. For `x ≥ 1` and `ε ≥ 0`,
`J(x) = √x J(1) + D` with `D` diagonal and
`D_k = 2k(√x − 1)(√x(4N + 2ρ − 2k + 2ε + 1) + 2(k + ε)) ≥ 0`. So `J(x)` is
positive definite, every `μ_i > 0`, and every coefficient of `∏ (y + μ_i)`,
an elementary symmetric function of the `μ_i`, is positive; for `y > 0`
every factor `y + μ_i` is positive, so `y` is not a root.

## Falsifier

The second statement fails if negative bias is admitted:
`(N, ρ, ε) = (1, 0, −2)` gives `P_1 = y − 2x + 4`, whose constant term is
negative for `x > 2`; the formal statement therefore takes `ε ≥ 0`. The
proof of part (b) uses `ε ≥ 0` only through `D ≥ 0`; the largest range of
negative bias for which the second statement holds is not determined here.

## Evidence

Symbolic computation confirms the closed form of part (a) for `N ≤ 8` and
`ρ ∈ {0, 1}`, and the product formula with `ε` kept symbolic. In exact
rational arithmetic, part (b) holds in 1488 cases with `N ≤ 12`, random
`ε ≥ 0` and `x > 1`, including `x = 1.001` and `x = 1.000001`. The source's
examples at `x = 1` reproduce, except that the product printed for
`P_5^{(5,1,ε)}(1, y)` is `(y + 2)(y + 12)(y + 30)(y + 56)(y + 90)`, the
product for `ρ = 0`; for `ρ = 1` the product is
`(y + 6)(y + 20)(y + 42)(y + 72)(y + 110)`, as the conjecture predicts.

The canonical source is
`D5/S3/Quantum/Dynamics/TwoPhotonRabiConstraintPolynomials.lean`. Its public
declarations are `constraintPoly`, `claim`, and `result`; `lam`, `qpoly`,
`gco`, `coef`, `dg`, `bb` and `jac` are private non-proposition definitions.
The frozen module state has statement identity
`sha256:3ba374453e4fc4b17e185bb485c7751960bf152d401c74d888b3ee4a7e687249`.
The result declaration has statement identity
`sha256:45f60c302ea623d163ec21194da6a6e4b0cb9af013871348b816e6c07b17f5df`.
The Freeze event is
`sha256:3413e93218c543e704f968df8f26983f2a470a369a34ca002dcba74e14957fdb`
and its project-level frozen prerequisite is the module
`D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant`, whose first-row
expansion `det_sparse_front` gives the tridiagonal determinant recursion. The proof uses only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`,
`native_decide`, or new axiom.

## Triage

Tier 1 external named conjecture, preregistered in issue #10148 before the
probe. `theorem`; resolution `proved` under the reading `ε ≥ 0` for the
second statement. The public theorem has `proof_shape: content`: the closed
form of part (a), the tridiagonal determinant recursion, the positive
definiteness of `J(1)` and the splitting `J(x) = √x J(1) + D` are new
propositions on the live proof path, not instances of pinned lemmas. Its
escape witness is form (2), the public conclusion itself, and its admission
basis is `open-problem-resolution`. Utility `none`: it is a theorem for every
`N`, not a finite computation.

## ASSUMED-UNVERIFIED

Whether the authors intend the second statement for all real `ε` or only for
the sign used in their constraint condition is not stated in the source; the
negative-bias failure above is recorded but not formalized. The bounded
literature check does not establish exhaustive worldwide novelty, priority,
or the absence of an independent proof. The Lean kernel does not authenticate
the external source or its version history.
