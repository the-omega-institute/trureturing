---
slug: rotundo-schwonnek-2023-extended-mub-norm-refutation
bibkey: rotundo2023entropic
doi: 10.1103/PhysRevResearch.6.033043
url: https://arxiv.org/abs/2303.11382v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/ExtendedMubNormRefutation.result
---

# The extended MUB mixed-norm equality is false

## Problem

Antonio F. Rotundo and René Schwonnek, arXiv:2303.11382v1, Conjecture 1
(Extended MUB regime), states that a doubly stochastic matrix has mixed operator
norm d^(1−lambda−mu) when ((1−mu)/mu)((1−lambda)/lambda) is at least the
square of its second largest singular value. Equation (7) gives the proposed
value for the 1/mu to 1/(1−lambda) norm. Issue #11781 preregistered this
statement, its quantifiers, and the refutation route.

## Motivation

The frozen declaration
`D5/S3/Quantum/Information/ExtendedMubNormRefutation.result` proves that the
spectral condition does not determine the proposed norm. The witness is a
three-dimensional real doubly stochastic matrix, so it also lies in the complex
vector domain used by the source's norm definition.

## Gap

The arXiv statement was open in issue #11781 when preregistered. The journal
version restates the claim as an entropic inequality; this settlement addresses
the arXiv norm statement. A complete classification of matrices for which the
extended MUB equality holds remains open.

## Route

1. Use d = 3, C = I/2 + J/6, mu = lambda = 2/3, and x = (4, 1, 1).
2. Compute that C is doubly stochastic, C* C = I/4 + J/4, and sigma2(C) = 1/2.
   Thus the spectral condition holds with equality.
3. Compute Cx = (3, 3/2, 3/2). The input norm cubed is 100 and the output norm
   cubed is 135/4, so the ratio cubed is 27/80, which is greater than 1/3.
4. The ratio is a member of the ratio set, and the boundedness argument makes it
   a lower bound for the supremum. The proposed value has cube 1/3, so the
   equality fails.

## Falsifier

The refutation would fail if the displayed matrix were not doubly stochastic,
if its second singular value did not satisfy the spectral condition, or if the
computed ratio did not exceed the proposed value. Each condition is discharged
in the kernel-checked `result` proof. Whether additional hypotheses restore an
operator-norm equality is open.

## Evidence

The canonical source is
`D5/S3/Quantum/Information/ExtendedMubNormRefutation.lean`. Its public
surface consists of the definitions needed by the claim, `claim`, and the
settling theorem `result`; the witness definitions are private. The module's
Freeze event is
`sha256:ee3a79912927ac430e6ff2ee6cc77268ac0412de9462cc5a865c6cce4ac1b124`,
and its module statement identity is
`sha256:fc65fa9e9bbf967cf80254c276ea55296ab6dff7ab9f77ad5143ca55edfffc50`.
The result declaration statement identity is
`sha256:8131343d11a56d4c05ecb844ba524c9173493757adf62147d70e467adeb8cfb9`.
The module has no project-level frozen prerequisites and uses only pinned
Mathlib imports. The kernel axiom closure is `propext`, `Classical.choice`,
and `Quot.sound`.

## Triage

Tier 1 quant-ph conjecture, preregistered in issue #11781 before Lean work;
resolution: refuted. The result has `proof_shape: bind-only` and admission
basis `open-problem-resolution`. Utility is
`kind=certified-instance; basis=refutes` with typed `claim` and `result`.

### What the settlement shows

- **Proved by** `D5/S3/Quantum/Information/ExtendedMubNormRefutation.result`:
  the doubly stochastic and spectral hypotheses can hold while the proposed
  mixed norm equality fails.
- **Computed in the same kernel proof**: the witness has sigma2 = 1/2, the
  spectral condition is tight, and its norm-ratio cube is 27/80 > 1/3.
- **Open**: an added structural hypothesis that restores the equality, a sharp
  replacement bound, and the full relation between the arXiv norm claim and
  the journal's entropic reformulation.
- **Effect on dependent results**: arguments that use Conjecture 1 as a general
  norm identity need an additional hypothesis or a separate proof; no other
  source theorem is claimed here.

## ASSUMED-UNVERIFIED

The literature check is bounded to the cited arXiv version, its journal
publication, and the searches recorded for issue #11781; it does not establish
worldwide priority or the absence of an independent answer. The journal's
entropic reformulation is not identified with the refuted norm equality by this
module.
