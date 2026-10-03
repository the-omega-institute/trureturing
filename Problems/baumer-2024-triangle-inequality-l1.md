---
slug: baumer-2024-triangle-inequality-l1
bibkey: baumer2024trianglelocal
doi: 10.48550/arXiv.2405.08939
url: https://arxiv.org/abs/2405.08939v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/TriangleInequalityL1Refutation.result
---

# A local counterexample to the triangle inequality ineq_l1

## Problem

E. Bäumer, V. Gitton, T. Kriváchy, N. Gisin and R. Renner (arXiv:2405.08939,
quant-ph; Phys. Rev. A 111, 052453 (2025)) build Bell-type inequalities for the
triangle network with four outcomes per party. They penalise asymmetry by

> Δ_l = Σ_{X ∈ {111,112,123}} Σ_{{a,b,c} ∈ I_X} |M_X − p(a,b,c)|^l,
> M_X = (1/|I_X|) Σ_{{a,b,c} ∈ I_X} p(a,b,c),

with `I_X` the outcome triples of type `X` (4, 36 and 24 of them), and from
neural-network estimates they state:

> … getting that approximately s₁₁₁(p) − 0.475 Δ_{l=1}(p) ≤ 0.289 (eq. ineq_l1),
> s₁₁₁(p) − 5.211 Δ_{l=2}(p) ≤ 0.316 (eq. ineq_l2), should both hold for all
> local models.

Issue #11263 fixes the reading. Locality is eq. `trilocal` with the frozen
`IsTriangleLocal`, `s₁₁₁` is the frozen `s111`, and `deltaL1` is `Δ_{l=1}`
summed over the three outcome types. The formal `claim` is eq. `ineq_l1` with
its printed constants for every local `p`; the result refutes it.

## Motivation

The paper notes that on the symmetric subspace, where the penalty vanishes,
`ineq_l1` is the more constraining of its two inequalities, and the same
construction with `l = 2` is used to certify experimental data in
arXiv:2401.15428. The frozen declaration
`D5/S3/Quantum/Entanglement/TriangleInequalityL1Refutation.result` gives a
local distribution with `Δ_{l=1} = 0` and `s₁₁₁ = 11/36`.

## Gap

Issue #11263 preregisters the reading, the route and the literature check. The
paper's own neural-network strategies stay below the bound (`s₁₁₁ ≈ 0.289` with
`Δ₁ ≈ 0.009`, and `0.294` with `Δ₁ ≈ 0.014`). The five citing works with arXiv
sources were read; only arXiv:2401.15428 uses the construction, with `l = 2`
and its own constants, and none reports a violation of `ineq_l1`.

These readings are `not-found-in-searched-scope`; they do not establish an
exhaustive worldwide literature search, priority, or the absence of an
independent answer.

## Route

1. Each source sends one of the 24 orderings of the four outcomes, uniformly;
   every party applies one rule to its two sources in cyclic order.
2. Cutting `[0, 1]` into 24 cells of measure `1/24` turns this into
   deterministic responses on `[0, 1]`; the integral factorises over the cells,
   so `p(a, b, c)` is the number of source triples with outputs `(a, b, c)`
   divided by `13824`.
3. Sixteen kernel-checked counts give 1056, 148 or 178 triples according to
   whether one, two or three outcomes are distinct. So `p` is constant on each
   outcome type, `Δ_{l=1}(p) = 0`, and `s₁₁₁(p) = 11/36 > 0.289`.

## Falsifier

The refutation uses the printed constants; it would not apply to a version of
`ineq_l1` whose right-hand side is at least `11/36 ≈ 0.3056` for distributions
with vanishing penalty, or whose penalty is not zero on distributions constant
on each outcome type.

## Evidence

Exact enumeration (issue #11263) of all `13824` source triples reproduces the
counts, `Δ₁ = Δ₂ = 0` and `s₁₁₁ = 11/36`.

The canonical source is
`D5/S3/Quantum/Entanglement/TriangleInequalityL1Refutation.lean`. Its public
declarations are `outcomeType`, `typeMean`, `deltaL1`, `claim` and `result`.
The frozen module state has statement identity
`sha256:fd7e42df6a4de5a66a590ea4b4de1eea72d566959596f7326c488eb56acd7fdc`.
The result declaration has statement identity
`sha256:c9ca3142e0c50f627b2f93b9f82ca90074542e9d79900134c12c31d11eadec66`.
The Freeze event is
`sha256:dcaf3a282217b6b1558ff7f7cb98ad03b2c90fbc595f6c6e9dfdfcece99ffe6c`.
Its frozen prerequisites are `IsTriangleLocal` and `s111` of
`D5/S3/Quantum/Entanglement/TriangleSymmetricLocalRefutation`. The proof uses
only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no
`sorry`, `native_decide`, or new axiom.

## Triage

Tier 1 external named conjectured inequality, preregistered in issue #11263
before any Lean for this target. `theorem`; resolution `refuted`. The public
theorem has `proof_shape: content`: the reduction of the triangle integral to a
count, the kernel-checked counts and the vanishing penalty are proved in the
module. Its escape witness is form (2), and its admission basis is
`open-problem-resolution`. Utility `kind=certified-instance; basis=refutes`
with typed `claim` and `result`.

## ASSUMED-UNVERIFIED

The published PRA text was not read, so it is unverified whether eq. `ineq_l1`
was edited there. The bounded literature check does not establish exhaustive
worldwide novelty, priority, or the absence of an independent answer. The Lean
kernel does not authenticate the external source or its version history.
