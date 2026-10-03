---
slug: kerenidis-2026-butterfly-lambda-two-relative-design-refutation
bibkey: kerenidis2026scalablequantumml
doi: 10.48550/arXiv.2607.24014
url: https://arxiv.org/abs/2607.24014v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/ButterflyLambdaTwoRelativeDesignRefutation.result
---

# The single-pass butterfly fails the relative exterior-square two-design bound

## Problem

Iordanis Kerenidis, *Scalable Quantum Machine Learning: Trainability,
Expressivity and Efficiency*, arXiv:2607.24014v2, Conjecture 20
(`quantum_v2.tex`, `conj:lambda2_design`), asserts:

> The unitary butterfly W_n at uniformly random parameters is an
> ε-approximate unitary 2-design on U(n) in the antisymmetric 2-particle
> representation Λ² ℂ^n, in the relative (multiplicative) sense, with
> ε = O(1/n).

The displayed assertion is
`(1−ε) Φ₂^(Λ²,Haar) ⪯ Φ₂^(Λ²,W_n) ⪯ (1+ε) Φ₂^(Λ²,Haar)`
as completely positive maps on End(Λ²ℂ^n ⊗ Λ²ℂ^n).
The Library note quotes the complete conjecture, including its separate
fixed-point-space sentence, and the literal circuit definition.
Issue #11543 preregisters the quantified reading: there are a real c and
natural N₀ such that every n=2^K ≥ N₀ admits 0 ≤ ε ≤ c/n satisfying
both inequalities. The circuit has one pass through increasing strides,
with the full phase layer before each disjoint RBS layer.

## Motivation

The frozen declaration
`D5/S3/Quantum/QuantumChannels/ButterflyLambdaTwoRelativeDesignRefutation.result`
proves `¬ claim`. The lower relative bound alone forces ε ≥ 1 in every
dimension 2^K with K ≥ 2, contradicting an O(1/n) error.

## Gap

Issue #11543 classifies the source as tier 1 and records its literature
check: arXiv version history, two Semantic Scholar citing works and
MathDB queries. No settlement was found within that searched scope.
Those readings are orchestrator-reported; they are not a complete
literature or priority claim. The source text and DOI identify the exact
assertion being refuted.

## Route

The mode type `Fin K → Fin 2` is identified with `Fin (2^K)` by
`finFunctionFinEquiv`; bit zero has stride one. The RBS blocks use
Mathlib's `Matrix.planeConformalMatrix` with entries cos θ, sin θ,
−sin θ, cos θ. The phase at mode j is
`exp(i (sum_i φ_i/2 − φ_j))`, retaining the global vacuum phase.
All coordinates are independently uniform on `[0,2π)`.

Factor W=B A, where A is the first layer. Every layer in B preserves
bit zero. An induction on the remaining layer list gives zero entries
between the two bit-zero classes. On rows zero and two, columns zero
and one are proportional, so
`m(W)=W₀₀ W₂₁ − W₀₁ W₂₀=0` for all parameters.

Exterior-square coordinates are two-by-two minors in the ordered basis
`e_i ∧ e_j`. Take the positive rank-one diagonal projector at
`x=(e₀∧e₁)⊗(e₀∧e₁)` and evaluate the twirl at
`u=(e₀∧e₂)⊗(e₀∧e₂)`. The butterfly value is zero. The Haar value
is the integral of |m(U)|⁴: a continuous nonnegative function equal
to one at the permutation swapping modes one and two. Compactness
provides integrability and Haar positivity gives a strictly positive
integral. A completely positive difference maps the input projector
to a positive semidefinite matrix. Its u-diagonal then forces ε ≥ 1.

## Falsifier

The conclusion concerns the literal single-pass increasing-stride
circuit and relative completely positive order on two exterior copies.
An additive norm-error estimate, a repeated-pass circuit or an
independent-halves ensemble is a different assertion. The proof needs
neither the upper relative bound nor the exact Haar integral.

## Evidence

The canonical module's only public theorem is `result : ¬ claim`.
Its private theorem `circuit_minor_zero` supplies the inductive support
argument; Haar positivity and the forced-error inequality are local
proof steps. All other public declarations define the source's circuit,
parameter law, exterior coordinates, moment maps and conjecture.
The result has axiom closure `propext`, `Classical.choice`, `Quot.sound`.
It imports no D5 module and has no frozen D5 prerequisite.

## Triage

Tier 1 external named conjecture preregistered in #11543.
Resolution: Refuted. `proof_shape: content` for `result` and the private
`circuit_minor_zero`; `escape_witness: circuit_minor_zero`;
`admission_basis: open-problem-resolution (#11543; Refuted)`.
Utility: none; the obstruction holds for arbitrary K ≥ 2.

### What the settlement shows

- **Proved in this module:** the selected exterior-square coordinate
  vanishes for every parameter assignment and every K ≥ 2. Later
  layers' preservation of the first bit is the decisive structure.
- **Proved in this module:** the corresponding fourth-power Haar
  integral is positive, and the lower relative CP inequality forces
  ε ≥ 1. The obstruction needs no numerical estimate of that integral.
- **Open extension:** general parameter distributions with the same
  pointwise-zero circuit coordinate. The support calculation indicates
  the same obstruction, but no general-distribution theorem is exported.
- **Open:** the analogous obstruction for arbitrary two-mode blocks
  in the same support pattern. The support argument indicates that
  extension, but this module instantiates the source's RBS gates.
- **Open beyond this settlement:** additive one-copy error bounds,
  repeated passes, the independent-halves ensemble, and the separate
  fixed-point-space dimension statement. None is proved or refuted here.
- **Source dependency consequence:** Theorem 19 (`thm:sharp_rate`)
  assumes the refuted conjecture for the literal butterfly. Its
  conditional sharp-rate argument supplies no unconditional sharp rate
  from that hypothesis. The sharp rate itself remains open here.
  Theorem 16's additive one-copy statement and Theorem 13's
  independent-halves ensemble require separate assessment.

## ASSUMED-UNVERIFIED

Literature absence is bounded by the orchestrator-reported search in
#11543. Lean does not authenticate publication history or mathematical
priority. The exterior representation is encoded by its minors basis;
no exported identification with `exteriorPower.map`, circuit-unitarity
certificate or moment-map integrability theorem is added by this module.
Information-escape registration is paused under CLAUDE.md §3.9.
