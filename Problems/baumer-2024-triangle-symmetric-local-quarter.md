---
slug: baumer-2024-triangle-symmetric-local-quarter
bibkey: baumer2024trianglelocal
doi: 10.48550/arXiv.2405.08939
url: https://arxiv.org/abs/2405.08939v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/TriangleSymmetricLocalRefutation.result
---

# A fully symmetric triangle-local distribution with p(A = B = C) above 1/4

## Problem

E. Bäumer, V. Gitton, T. Kriváchy, N. Gisin and R. Renner (arXiv:2405.08939,
quant-ph; Phys. Rev. A 111, 052453 (2025)) study classical (local) models in
the triangle network with four outcomes per party. Their best local fully
symmetric construction has `p(A = B = C) = 1/4`, and their conclusion states:

> Open problem. Does there exist a distribution p(A,B,C) that is local in the
> triangle network and fully symmetric such that p(A=B=C) > 1/4?

Issue #11256 fixes the reading. Locality is eq. `trilocal`: sources uniform on
`[0, 1]` and measurable conditional distributions `p_A(a|β,γ)`, `p_B(b|γ,α)`,
`p_C(c|α,β)`. Full symmetry is invariance under every permutation of the
parties and every joint relabelling of the four outcomes. The formal `claim` is
the negative answer, `s₁₁₁(p) ≤ 1/4` for every local fully symmetric `p`; the
result refutes it, so the answer is yes.

## Motivation

Fully symmetric distributions with four outcomes include the distribution of
the Elegant Joint Measurement, the main candidate for noise-robust quantum
nonlocality in the triangle network, and the local value of `p(A = B = C)`
calibrates the Bell-type inequalities used to certify such nonlocality. The
frozen declaration
`D5/S3/Quantum/Entanglement/TriangleSymmetricLocalRefutation.result` gives a
local fully symmetric distribution with `p(A = B = C) = 41/144`.

## Gap

Issue #11256 preregisters the reading, the route and the literature check. The
paper has one arXiv version. INSPIRE lists 6 citing records and OpenAlex one
citing work (2026-09-29); the five with arXiv sources were read and none gives
a local fully symmetric model with `p(A = B = C) > 1/4`. arXiv queries on the
triangle network since 2024-05 found no further answer.

These readings are `not-found-in-searched-scope`; they do not establish an
exhaustive worldwide literature search, priority, or the absence of an
independent answer.

## Route

1. Each source sends one of the 12 ordered pairs `x = (x₁, x₂)` of distinct
   outcomes, uniformly; every party applies `f(x, y) = x₂` if `x₂ ∈ {y₁, y₂}`
   and `x₁` otherwise, with `a = f(β, γ)`, `b = f(γ, α)`, `c = f(α, β)`.
2. Cutting `[0, 1]` into 12 cells of measure `1/12` turns this into
   deterministic responses on `[0, 1]`; the integral factorises over the cells,
   so `p(a, b, c)` is the number of source triples with outputs `(a, b, c)`
   divided by `1728`.
3. A kernel-checked count gives 123, 19 or 23 triples according to whether one,
   two or three outcomes are distinct. This pattern is invariant under outcome
   relabellings and party permutations, and `p(A = B = C) = 492/1728 = 41/144`.

## Falsifier

The answer would change if locality required something the construction lacks,
for instance sources that are not uniform on `[0, 1]`, or if full symmetry were
read as more than invariance under party permutations and joint outcome
relabellings.

## Evidence

Exact enumeration (issue #11256) of all `1728` source triples reproduces the
counts, full symmetry, and `s₁₁₁ = 41/144`; the non-equivariant control rule
`min(x₁, y₁)` is correctly flagged as not relabelling-invariant.

The canonical source is
`D5/S3/Quantum/Entanglement/TriangleSymmetricLocalRefutation.lean`. Its public
declarations are `IsTriangleLocal`, `FullySymmetric`, `s111`, `claim` and
`result`. The frozen module state has statement identity
`sha256:26a81b4ab22f4c2a4d7b9f52ab319384d08eb0dea0b33b5ab91b298667c902cd`.
The result declaration has statement identity
`sha256:ea0c534a0eaff0cb22e5d4563e2746d305896843b175bba67bb27540e7b56630`.
The Freeze event is
`sha256:9fccf9936af1b6d9ac48e55a56909f48f7170b7fbf3980bf2470b9277d26859e`
and has no project-level frozen prerequisites. The proof uses only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`,
`native_decide`, or new axiom.

## Triage

Tier 1 external named open problem, preregistered in issue #11256 before any
Lean. `theorem`; resolution `refuted` (the negative answer is refuted, so the
open problem is answered yes). The public theorem has `proof_shape: content`:
the reduction of the triangle integral to a normalised count and the
kernel-checked count are proved in the module. Its escape witness is form (2),
and its admission basis is `open-problem-resolution`. Utility
`kind=certified-instance; basis=refutes` with typed `claim` and `result`.

## ASSUMED-UNVERIFIED

The published PRA text was not read, so it is unverified whether the open
problem was edited there. The bounded literature check does not establish
exhaustive worldwide novelty, priority, or the absence of an independent
answer. The Lean kernel does not authenticate the external source or its
version history.
