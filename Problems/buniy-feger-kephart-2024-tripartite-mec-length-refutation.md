---
slug: buniy-feger-kephart-2024-tripartite-mec-length-refutation
bibkey: buniy2024maximallyentangledclasses
doi: 10.1142/S0219749924500357
url: https://arxiv.org/abs/2210.07618v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/TripartiteMaximalClassLengthRefutation.result
---

# A maximally entangled (3, 3, 7) state of length 9 refutes the length formula Σ d_i − 2

## Problem

R. V. Buniy, R. P. Feger and T. W. Kephart, *Decoherence and the classes of maximally entangled states*, Int. J. Quantum Inf. 22, 2450035 (2024), arXiv:2210.07618v1, classify tripartite qudit states by algebraic entanglement invariants.
- **The invariants.** For a state v of ℂ^{d₁} ⊗ ℂ^{d₂} ⊗ ℂ^{d₃} with coordinates v_{ijk}, they are (n₁, n₂, n₃, n₁,₂,₃) (Appendix A):
  - n_i, the kernel dimensions of the three flattenings;
  - n₁,₂,₃, the dimension of the space of arrays z with Σ_{j,k} v_{ajk}z_{bjk} = Σ_{i,k} v_{iak}z_{ibk} = Σ_{i,j} v_{ija}z_{ijb} = 0 for all a, b.
- **The class.** A state is maximally entangled when every invariant takes its least value, and these states form the maximally entangled class C_D (Definition II.1).
- **The length.** It is the number of nonzero coordinates, and L_D is the least length in C_D (Eq. (2)).
- **The conjecture.** From exact values of L_D for dimensions up to 5 (Table XII), Conjecture III.4 states "L_(d₁,d₂,d₃) = Σ_{i=1}^{3} d_i − 2 for min(d₁, d₂, d₃) ≥ 3", together with two clauses for d₁ = 2.

The verbatim statements are in [the literature note](../Library/QuantumBounds/buniy2024maximallyentangledclasses.md).

Issue [#16992](https://github.com/the-omega-institute/trureturing/issues/16992) fixes the reading: the lower-bound half of the third clause, i.e. every v ∈ C_D has L(v) ≥ d₁ + d₂ + d₃ − 2 when all d_i ≥ 3. Refuting it refutes the conjecture. It is refuted at D = (3, 3, 7).

## Motivation

The shortest length measures how few product terms a maximally entangled state needs, and the conjectured linear law would describe it for all tripartite qudit systems. The refutation shows that the law, read off from dimensions up to 5, does not extend: unbalanced dimensions admit maximally entangled states with far fewer terms.

## Gap

Issue #16992 records the literature check before any Lean:
- arXiv v1 is the only version. The journal text was not read: the publisher page was not retrieved, and Firecrawl returned HTTP 402. Its agreement with v1 is `ASSUMED-UNVERIFIED`.
- The citing work Buniy–Kephart (arXiv:2412.10728v1) was read in full and contains no statement about shortest lengths.
- The search seat also inspected the invariant papers arXiv:1009.2217v2 and arXiv:1012.2630v2 (seat-reported).
- Zenodo found no related record, and the repository had no entry for the paper.

`not-found-in-searched-scope`.

## Route

Let u at D = (3, 3, 7) be the indicator of the nine coordinates (0,1,0), (0,2,1), (1,0,2), (1,2,3), (2,0,4), (2,1,5), (0,0,6), (1,1,6), (2,2,6). Its seven 3 × 3 slices are the six off-diagonal matrix units and the identity, and L(u) = 9.
1. **The flattenings.** Slice 6 is the identity, so the first two flattenings are injective; the seven slices are linearly independent, so the third is too. Hence n₁ = n₂ = n₃ = 0.
2. **The joint kernel.** For z in the kernel, the third family makes every slice of z diagonal and gives the trace relation z_{00b} + z_{11b} + z_{22b} = 0. The first and second families then kill two diagonal entries of each slice 0–5, the trace relation kills the third, and the first family with a = b kills slice 6. Hence n₁,₂,₃ = 0.
3. **The contradiction.** The invariants are dimensions, so u attains the least value of each and lies in C_{(3,3,7)}; but L(u) = 9 < 11 = 3 + 3 + 7 − 2.

## Falsifier

The refutation would not hold if:
- the module's invariants differed from the source's kernels;
- its class were weaker than simultaneous minimality of all four invariants over every state;
- its length counted something other than nonzero coordinates.

The module defines the four invariants as `Module.finrank ℂ` of the kernels of the three flattenings and of the product of the three contraction families of (A4)–(A6), defines the class by minimality over all of `State d1 d2 d3`, and counts the support of the coordinate function.

## Evidence

The canonical source is `D5/S3/Quantum/Entanglement/TripartiteMaximalClassLengthRefutation.lean` (374 lines).
- It defines `State`, `flat1`, `flat2`, `flat3`, `block1`, `block2`, `block3`, `joint`, `n1`, `n2`, `n3`, `n123`, `InMEC`, `coordSupport`, `length` and `claim`, and proves `result : ¬ claim` at (3, 3, 7).
- It uses pinned Mathlib only: `LinearMap.pi`, `LinearMap.prod`, `LinearMap.ker_eq_bot'`, `finrank_bot` and finite sums over `Fin`.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- `result` is the refutation result of a `refutes` utility, which CLAUDE.md §3.9 exempts from four-slot registration.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Entanglement/TripartiteMaximalClassLengthRefutation.lean.json`, statement `sha256:d3fd4dad62955167168ac5635fd526ca2de64c70bdfa0ebb295958c3968e06e6`.

Declaration statements:
- `result`: `sha256:2ea19d1b2e889d8f3bb365146d17ba61b9c0cd20e81bab7f68f7029be918df00`;
- `claim`: `sha256:63b4e6a4759f4041ff6fa499bc6eb7e1a4f6abdd9a7bc48586163e318b3b7ef4`.

## Triage

Tier 1 conjecture of a 2022 paper (published 2024), preregistered in issue #16992 before any Lean.
`counterexample`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the evaluation lemmas, the support count and the four kernel computations are coordinate extraction and normalization of pinned Mathlib constructions | open-problem-resolution |
| the witness, evaluation, support and kernel helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every other declaration is a definition used by a public statement or a compiler-generated proof on the proof path of `result`. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The utility is `certified-instance` with basis `refutes` the module's `claim`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** at D = (3, 3, 7) the maximally entangled class contains a state of length 9, so L_(3,3,7) ≤ 9 < 11 and the third clause of Conjecture III.4 fails.

**Computed, not formalized** (orchestrator, NumPy and exact SymPy ranks, 15 October 2026):
- The four invariants of random states reproduce the principal invariants of Table XII at every tested D, which corroborates the reading of Eqs. (A1)–(A6) used by the module.
- At (3, 3, 9), the state with the nine 3 × 3 matrix units as its slices (length 9) has invariants (0, 0, 0, 0), as do random states, so L_(3,3,9) ≤ 9. Since n₃ = 0 forces the nine slices to be linearly independent, every state in the class has length at least 9. Hence L_(3,3,9) = 9, against the conjectured 13.
- At (3, 3, 8), random supports find a class member of length 11 < 12.
- At (3, 3, 5) and (3, 3, 6), random supports of length below the conjectured 9 and 10 find no class member.

**Argued, not formalized.**
- The mechanism is the third flattening. When d₃ is close to d₁d₂, slices made of matrix units are already linearly independent and leave no room for the joint kernel, so short states reach the class. Whenever the class has n₁ = n₂ = n₃ = 0 (as for d₁ = d₂ = 3 and d₃ ≤ 9), each flattening of a class member is injective, so its slices along every factor are linearly independent and L_D ≥ max(d₁, d₂, d₃); this bound is attained at (3, 3, 9).
- The conjectured law Σ d_i − 2 fits Table XII, where d₃ ≤ 5 < d₁d₂.

**Open.**
- The exact value of L_(3,3,7) (the bound is 7 ≤ L_(3,3,7) ≤ 9; two structured states of lengths 7 and 8 are not in the class) and of L_(3,3,8).
- A corrected formula for L_D across the range d₃ ≤ d₁d₂, and the qubit clauses of the conjecture.

**Effect on the paper.** Conjecture III.4 fails for min(d₁, d₂, d₃) ≥ 3; the exact values of Table XII and the paper's results on the principal invariant are unaffected.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The journal text of the paper was not compared with arXiv v1. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
