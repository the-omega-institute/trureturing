---
slug: zheng-liu-2024-logical-z-support-refutation
bibkey: zhengliu2024magicdistillationdynamics
doi: 10.22331/q-2025-09-15-1858
url: https://arxiv.org/abs/2412.04402v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/StabilizerLogicalZSupportRefutation.result
---

# Logical Z operators with Z support on every stabilizer coset need not exist

## Problem

Y. Zheng and D. E. Liu, *From Magic State Distillation to Dynamical Systems*, Quantum 9, 1858 (2025), arXiv:2412.04402, model magic state distillation by a stabilizer code as a map of the Bloch ball.

Proposition 3 gives a sufficient condition for z = 0 to be a fixed plane of the map: for every logical operator Z̄_i and every stabilizer element s_j, the product s_j Z̄_i contains a Pauli Z tensor factor. The authors write after Eq. (23): "This condition is satisfied by most known protocols that we have examined and we conjecture it to be generally true for any stabilizer codes by properly choosing the logical Z operators without modifying the stabilizer groups."

The verbatim statements are in [the literature note](../Library/QuantumChannels/zhengliu2024magicdistillationdynamics.md).

Issue [#17951](https://github.com/the-omega-institute/trureturing/issues/17951) fixes the reading. For every stabilizer code with at least one logical qubit, some nontrivial logical Pauli word L has a literal Z factor in every product s·L with s in the stabilizer group. This conjecture is refuted.

## Motivation

The fixed-plane property lets the authors reduce the three-dimensional distillation dynamics to a two-dimensional flow on the equator, the plane of magic states that can be injected directly. The conjecture would make this reduction available for every stabilizer code.

## Gap

Issue #17951 records the literature check before any Lean:
- arXiv v1, v2 and the journal version keep the conjecture;
- the full texts of five citing works (arXiv:2608.14798, 2503.01165, 2607.08508, 2605.06251 and 2512.23799) do not address the condition;
- arXiv searches for the fixed plane return no settlement;
- the repository had no record of the paper.

`not-found-in-searched-scope`.

## Route

1. **Witness.** The five-qubit code with generators XZZXI, IXZZZ, XIXZY and ZXIXY. This is the standard [[5,1,3]] code after the local Clifford SH on qubit 5.
   - The generators commute pairwise and are independent, so the code encodes one qubit.
2. **Classification.** Every word commuting with the four generators lies in one of four cosets of the stabilizer group, with representatives IIIII, XXXXZ, YYYYX and ZZZZY.
3. **Z-free products.** Each nontrivial coset contains a word without a Z factor:
   - XXXXZ·IXZZZ = XIYYI (up to phase);
   - YYYYX itself;
   - ZZZZY·XZZXI = YIIYY.

   Since s ranges over the whole group, every choice of the logical operator fails.

## Falsifier

The refutation would not settle the conjecture if:
- the word model differed from stabilizer codes;
- a Y factor counted as "Pauli Z";
- the claim demanded more than the conjecture implies.

The answers:
- **Phases.** Phases do not change which tensor factors are Z. Commuting independent generators with signs + generate a stabilizer group without −I, and every stabilizer group arises this way up to signs.
- **Y factors.** By the source's Eq. (14), the expectation of a word on ρ(x, y, z)^{⊗n} is ±x^{w_X} y^{w_Y} z^{w_Z}, so only a literal Z produces the factor z of Eq. (23).
- **What the claim demands.** The claim asks for one logical operator, which the conjecture provides for every k ≥ 1.

## Evidence

The canonical source is `D5/S3/Quantum/Information/StabilizerLogicalZSupportRefutation.lean` (112 lines).
- It defines the phase-free word product `wmul`, `Commutes`, `InStabilizer`, `IsStabilizerCode` and `claim`, and proves `result : ¬ claim`.
- It reuses `Pauli` and `anticomm` of `StabilizerPairLocalUnitaryInequivalence` and the letter product of `StabilizerPovmMaximalEntanglementRefutation`.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- The escape registration: `result` is the designated refutation result of the `utility` header and is exempt; the module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Information/StabilizerLogicalZSupportRefutation.lean.json`, statement `sha256:a1be2cdff61598dff23d5ffc64824557d9b4278f258780b74e132f1da942703d`.

Declaration statements:
- `result`: `sha256:48a0aa8a42b76a172d5d1f85d89ddbdb0d375021882ec88b4225ab8527550bb0`;
- `claim`: `sha256:6a656059f122e1f8f11b64994bbd579680a960caf78e95377c24e07d700796db`.

## Triage

Tier 1 conjecture of a 2024 paper, preregistered in issue #17951 before any Lean.
`theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the code checks and the coset classification are decidable finite facts | open-problem-resolution |
| the witness and classification helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every other public declaration is a definition used by a public statement. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Refuted by `result`:** for the five-qubit code above, every nontrivial logical word has a stabilizer translate without a Z factor.

**Computed, not formalized** (orchestrator, exhaustive search over Pauli words, recorded in #17951):
- The witness code has distance 3, so restricting the conjecture to codes of distance at least 3 does not repair it.
- The standard [[5,1,3]] code and the Steane [[7,1,3]] code satisfy the condition with suitable logical words. The failure comes from the local Clifford on qubit 5, which changes the stabilizer group but not the code's distance.
- The smallest counterexample is on two qubits, the code ⟨YZ⟩. No one-qubit code is a counterexample.

**Argued, not formalized.** The condition is a statement about the letters of a fixed stabilizer group, so it is not invariant under local Cliffords: conjugating one qubit by SH maps X to Z, Y to X and Z to Y, and moves Z support between letters. A code that satisfies the condition can therefore lose it under a local basis change on one qubit, which leaves the weights of all words, and hence the distance, unchanged.

**Open.**
- Whether z = 0 itself fails to be a fixed plane for this code under the source's decoding (Eq. (6)). The search seat reports a logical output with z-coordinate −130/653 at the input (3/5, 1/2, 0); this is not rechecked here.
- Which codes admit a local Clifford frame in which the condition holds.

**Effect on the paper.** The reduction to the equatorial flow is justified by Proposition 3 only for codes, in a given Pauli frame, that satisfy the condition. It is not available for every stabilizer code by choosing the logical operators.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Computed, not formalized", "Argued, not formalized" and "Open" are not formalized.
