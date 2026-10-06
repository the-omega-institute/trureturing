---
slug: dutta-tushar-2026-wigner-distance-self-tensor-superadditivity
bibkey: dutta2026wignerdistance
doi: 10.48550/arXiv.2603.20792
url: https://arxiv.org/abs/2603.20792v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules.resultSelfTensor
---

# Self-tensor superadditivity on the nonpositive Bloch-product branch

## Problem

Soumyojyoti Dutta and Tushar, *A Phase-Space Geometric Measure of Magic in
Qubit Systems*, arXiv:2603.20792v3, printed p. 8, Conjecture 5.7:

> For any qubit state $\rho$ with $s(\rho)\leq0$: $C(\rho\otimes\rho)\geq2C(\rho)$.

The quantities use the fixed Wootters product frame, the convex hull of
Wigner functions of actual Pauli stabilizer states, and the L1 distance.
Issue #11541 preregisters the fully quantified density-matrix statement,
Tier 1 classification and literature reading before the Lean probe.

## Motivation

`D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules.resultSelfTensor` proves
`claimSelfTensor` for all complex two-by-two positive semidefinite matrices of
trace one, with the displayed branch assumptions. The two-qubit free set
includes entangled stabilizers: it is defined through four-element
commuting subgroups of the matrix unitary group with a unique common
normalized eigenray.

## Gap

The source's numerical observation does not prove an identity or inequality
for every density matrix. Lower bounds must hold for the full free
polytope, including its entangled generators. The literature conclusion
in #11541 is not-found-in-searched-scope, not an assertion that every
possible source was searched.

## Route

The existing Mathlib L1 space is `PiLp 1`; `Metric.infDist` is taken over
the image of the free Wigner polytope under `WithLp.toLp 1`. Every
single-qubit Wigner vector has at most one negative coordinate. On the
nonpositive Bloch-product branch, an explicit convex mixture of stabilizer
edge vertices attains error $\|W_\rho\|_1-1$. A sign functional with at
most one negative entry is bounded by one on every two-qubit stabilizer.
Actual subgroup generators reduce this bound to an exact rational
certificate over sixty distinct candidate Wigner vectors. Convexity
extends the bound to the whole free polytope. Product weak duality yields
$C(\rho\otimes\sigma)\geq\|W_\rho\|_1\|W_\sigma\|_1-1$.
The tensor product of the attaining one-qubit mixtures gives the
matching upper estimate for the equatorial equality. Two copies give
$(1+C(\rho))^2-1\geq2C(\rho)$ for the self-tensor inequality.

## Falsifier

A density matrix or pair satisfying the exact branch hypotheses and
violating the displayed conclusion would refute the claim. A change of
phase-point convention or replacing the two-qubit stabilizer polytope by
the product-only polytope changes the problem. A verified earlier
settlement would invalidate the literature admission premise without
changing the kernel-checked theorem.

## Evidence

The settling theorem is `resultSelfTensor : claimSelfTensor`. The only accepted axiom
closure is `propext`, `Classical.choice`, `Quot.sound`. Canonical door
outputs and the verification readings are identified in the delivery PR;
this dossier does not duplicate machine state. The source clauses,
locators and density-matrix interpretation are in
`Library/QuantumStates/dutta2026wignerdistance.md`.

Definition fidelity: `D5.S3.Quantum.Magic.WignerDistanceMinimum.COne_min`
and `CTwo_min` prove for every matrix that the corresponding distance
attains the source's minimum and is no larger than any free candidate.

Information-escape registration is paused under CLAUDE.md §3.9.

## Triage

Tier 1: a named conjecture in the latest version checked in #11541.
The public theorem gives the universal settlement; finite calculations
support the dual bound and do not replace its quantifiers.

### What the settlement shows

- Proved in this module: Conjecture 5.6 by `resultEquatorial` and
  Conjecture 5.7 by `resultSelfTensor`. The decisive mechanisms are the
  attaining local stabilizer mixture and the product sign-functional
  bound on the full two-qubit stabilizer polytope.
- Proved inside the private derivations: `tensor_distance_lower` applies
  to every pair of one-qubit density matrices, without a sign assumption;
  `distance_one_nonpositive` identifies the local distance with
  $\|W_\rho\|_1-1$ and constructs an attaining mixture. These are
  proof-internal facts, not additional public settling declarations.
- Open as a separate public settlement: the full nonpositive-branch
  multiplicativity statement recorded as numerical Observation 5.1(i).
  The local mixture and dual bounds supply its ingredients; this delivery
  does not add a named theorem for that observation.
- Open: the positive Bloch-product branch, its tensor deficit and
  extensions beyond two qubits. The single-qubit norm identity used here
  has an explicit nonpositive-branch hypothesis.
- Proved scope for the source: its two conjectures are established in the
  stated frame. This does not certify all numerical observations or
  protocols in the paper; applications requiring other assumptions retain
  those assumptions.

## ASSUMED-UNVERIFIED

The external literature search and numerical readings in #11541 are
orchestrator-reported inputs. This module does not prove that the
bibliographic search is exhaustive or that the source's physical
interpretation covers every experimental implementation.
