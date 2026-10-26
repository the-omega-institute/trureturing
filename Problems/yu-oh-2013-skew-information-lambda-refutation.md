---
slug: yu-oh-2013-skew-information-lambda-refutation
bibkey: yu2013skewinformation
doi: null
url: https://arxiv.org/abs/1303.6404v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/SkewInformationLambdaRefutation.result
---

# λ_f = min{1, 1/[4f(0)]} fails for a regular symmetric operator monotone function

## Problem

S. Yu and C. H. Oh, *Robertson-Schrödinger uncertainty relation refined by skew information*, arXiv:1303.6404v1, Appendix 2:

> Numerical  evidences show that  $\lambda_f=1$ whenever $4f(0)\le 1$ and we conjecture that $\lambda_f=\min\{1,1/[4f(0)]\}$ always holds.

Here λ_f is the minimum over x ≥ 0 of F(x) = (1 + x − f(0)(1 − x)²/(2f(x)))/(2f(x)), for f nonnegative on [0, ∞), operator monotone on Hermitian matrices, symmetric (x f(1/x) = f(x)), normalized (f(1) = 1) and regular (f(0) > 0). The definitions are quoted in [the literature note](../Library/QuantumContext/yu2013skewinformation.md).

Issue [#19664](https://github.com/the-omega-institute/trureturing/issues/19664) fixes the reading. For every such f, min{1, 1/(4f(0))} would be the least value of F on [0, ∞). The conjecture is refuted.

## Motivation

The constant λ_f enters the source's refinement of the Robertson-Schrödinger uncertainty relation by f-skew information: a larger λ_f gives a stronger relation. The source proves 1 − f(0) ≤ λ_f ≤ min{1, 1/(4f(0))}, using F(1) = 1 and F(0) = 1/(4f(0)), and shows λ_f = 1 for the Wigner–Yanase–Dyson family. The conjecture asserts that the upper bound is always attained.

## Gap

The literature check before any Lean is recorded in #19664:
- arXiv:1303.6404 has only v1 and no journal reference;
- the search seat reports that the five INSPIRE citing works and three further related papers do not discuss or settle λ_f;
- the repository had no record.

`not-found-in-searched-scope`.

## Route

Let f(x) = (2/9)(1 + x) + (10/3)·x/(11x + 1) + (10/3)·x/(x + 11).
1. **Operator monotonicity.** For a, b > 0, x/(ax + b) = 1/a − (b/a)(ax + b)⁻¹. For positive semidefinite 0 ≤ A ≤ B, (aB + bI)⁻¹ ≤ (aA + bI)⁻¹, so M ↦ M(aM + bI)⁻¹ preserves the order. A positive combination of such terms and of the affine term (2/9)(1 + x) preserves it too.
2. **Admissibility.** f ≥ 0 on [0, ∞), f(1) = 2·(2/9) + (10/3)(1/12) + (10/3)(1/12) = 1, f(0) = 2/9 > 0, and x f(1/x) = f(x) for x > 0.
3. **The witness point.** f(1/4) = 31/54 and F(1/4) = 135/124 − 729/7688 = 7641/7688 < 1. Since 4f(0) = 8/9 ≤ 1, the conjectured value is min{1, 9/8} = 1, which is not a lower bound of F on [0, ∞).

## Falsifier

The refutation would not answer the conjecture if the module's class of functions were larger than the source's, or its λ_f different. The module:
- requires f ≥ 0 on [0, ∞), operator monotonicity on positive semidefinite complex matrices of every finite size (with the matrix functional calculus), symmetry for x > 0, normalization and regularity, as in the source;
- reads λ_f = min_{x ≥ 0} F(x) = m as the statement that m is the least value of F on [0, ∞).

## Evidence

The canonical source is `D5/S3/Quantum/Information/SkewInformationLambdaRefutation.lean` (162 lines).
- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Information/SkewInformationLambdaRefutation.lean.json`, statement `sha256:1c784f6032845c347487b7668d1de8c680cf7c3ad38ddf4e75b3d43ce20aa06d`.

Declaration statements:
- `result`: `sha256:18bd0afc6c656659af73ea6ac5d102628d56e4887996411ea46f06b577165fa6`;
- `claim`: `sha256:4b49a502237a6a903d663504c36efd925403bc04e0875bb7e3e41138b4216352`.

## Triage

Tier 1 conjecture of a 2013 paper, preregistered in issue #19664 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. `utility: kind=certified-instance; basis=refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** the function f above is nonnegative, operator monotone in every finite matrix size, symmetric, normalized and regular, and F_f(1/4) = 7641/7688 < 1 = min{1, 1/(4f(0))}.

**Computed, not formalized** (orchestrator, recorded in #19664): on a grid of [0, 1], min F_f ≈ 0.99238 near x ≈ 0.324. Over 300 random positive semidefinite pairs, f(B) − f(A) stays positive definite.

**Argued, not formalized.**
- *Mechanism.* F(1) = 1 is always a critical point, but it need not be a minimum. Mixing the affine function (1 + x)/2 with Kubo–Ando means that bend sharply near x = 1/11 and x = 11 lowers F between 0 and 1, while keeping f(0) small enough that 4f(0) ≤ 1.
- *Effect on the paper.* The source's statement that λ_f = 1 whenever 4f(0) ≤ 1 fails as well. The proven bounds 1 − f(0) ≤ λ_f ≤ min{1, 1/(4f(0))} remain. The exact value of λ_f for general f stays open; for this f, numerically λ_f ≈ 0.99238.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
