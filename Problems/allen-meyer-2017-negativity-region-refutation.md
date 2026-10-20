---
slug: allen-meyer-2017-negativity-region-refutation
bibkey: allen2017polynomialmonogamy
doi: 10.1103/PhysRevLett.118.080402
url: https://arxiv.org/abs/1502.04807v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/AllenMeyerNegativityRegionRefutation.result
---

# The Allen–Meyer family does not give the entire three-qutrit negativity region

## Problem

G. W. Allen and D. A. Meyer, *Polynomial Monogamy Relations for Entanglement Negativity* (Phys. Rev. Lett. 118, 080402 (2017); arXiv:1502.04807), study the triples of squared negativities (N²_A|C, N²_A|B, N²_A|BC) of pure three-party states, with N(ρ) = ‖ρ^{T_A}‖₁ − 1.
- **Three qubits.** They describe the achievable region by the states d|000⟩ + a|101⟩ + b|110⟩ + c|111⟩.
- **Qudits.** They generalize these states to the family (13), d|000⟩ + Σ_{j=1}^{D−1} (a|j0j⟩ + b|jj0⟩ + c|jjj⟩).
- **The conjecture.** "we conjecture that it is the entire achievable set of negativities, (N²_A|C, N²_A|B, N²_A|BC), for D > 2 as well".

The verbatim statements are in [the literature note](../Library/QuantumChannels/allen2017polynomialmonogamy.md).

Issue [#18420](https://github.com/the-omega-institute/trureturing/issues/18420) fixes the reading for D = 3: every unit three-qutrit vector has the negativity triple of some normalized family state. The conjecture is refuted.

## Motivation

The achievable region of negativity triples encodes the polynomial monogamy relations of the paper. A family describing the whole region would give those relations for qudits in closed form; the paper derives its 143-term boundary polynomial for D = 3 from the family.

## Gap

Issue #18420 records the literature check before any Lean:
- arXiv v1 and v2 keep the conjecture;
- the citing works found treat the weaker squared-negativity monogamy or other families;
- the repository had no record of the paper.

`not-found-in-searched-scope`.

## Route

Write x, y, z for the negativities N of the AB, AC and A|BC cuts.
1. **Separator over the family.** Write r² = a² + b² + c², u = b² + c² and k = d/r.
   - The Schmidt coefficients give z = 4dr + 2r².
   - A decomposition of the 3 × 3 block into positive semidefinite parts gives y ≤ 2a² + 4ad.
   - For a > 0, a Gram identity gives x ≤ 2u(1 + 2d²/a²). The hypotheses of the next item force a > 0.
   - If z ≥ 14/11 and z − y ≤ 2/209, then 1/7 ≤ k ≤ 3, u ≤ 1/209 and a²/r² ≥ 18/19, which gives x ≤ 5(z − y).
2. **The witness.** ψ = (5|000⟩ + 3|101⟩ + |202⟩ + t|110⟩ + 5t|220⟩)/√(35 + 26t²) at t = 1/100.
   - Its partial transposes split into explicit 1 × 1 and 2 × 2 blocks.
   - Unitary and positive-semidefinite certificates with rational square-root bounds give z ≥ 14/11, z − y ≤ 2/209 and x > 5(z − y).
3. **Conclusion.** No family state has the witness's triple.

## Falsifier

The refutation would not settle the conjecture if the module's negativities, reduced states or family differed from the source's. The module takes:
- the negativity (‖ρ^Γ‖₁ − 1)/2 of `NegativityReductionInclusionRefutation`, which is half the source's N; equality of triples is unaffected, and the partial transpose on either factor has the same trace norm;
- the reduced states as partial traces of the rank-one density;
- the family (13) at D = 3 with a, b, c, d ≥ 0 and d² + 2(a² + b² + c²) = 1.

The squares in the source's triple do not affect equality of triples, because negativities are nonnegative.

## Evidence

The canonical source is `D5/S3/Quantum/Entanglement/AllenMeyerNegativityRegionRefutation.lean` (631 lines).
- **Definitions.** It defines `pairAB`, `pairAC`, `negativityTriple`, `familyState` and `claim`, and proves `result : ¬ claim`.
- **Reuse.** It reuses:
  - the rank-one density of `PureStateHandshake`;
  - the partial trace of `PartialTraceMutualInformation`;
  - the negativity of `NegativityReductionInclusionRefutation`;
  - the trace-norm lemmas of `FiniteTraceDistance`;
  - the swap matrix and the trace-norm isometry lemmas of `ConicalDesignConcurrenceComparability`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Escape registrations.** `result` is the designated refutation result of the `utility` header and is exempt. The module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Entanglement/AllenMeyerNegativityRegionRefutation.lean.json`, statement `sha256:52e2c8faf047223765b2d800f92d899c719e42a7b961245feddccae5631dbe39`.

Declaration statements:
- `result`: `sha256:fcd013b4a79eed678974c5b05fa6d13799a48de5c2942c50a46745925143ddc6`;
- `claim`: `sha256:78c6fa347ae33e896b56f4266278036f294d75e487f474e4f828931974b79caa`.

## Triage

Tier 1 conjecture of a 2017 paper, preregistered in issue #18420 before any Lean.
`theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the Schmidt, positive-semidefinite, Gram and unitary certificates are instances of existing trace-norm lemmas, and the separator and witness bounds are rational arithmetic with square roots | open-problem-resolution |
| `pairAB`, `pairAC`, `negativityTriple`, `familyState`, `claim` | bind-only | none | definitions used by `claim` |
| the certificate, separator and witness helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every declaration is bind-only. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Refuted by `result`:** at t = 1/100 the witness has a negativity triple that no normalized family state of Eq. (13) with D = 3 attains, so the family does not give the entire achievable set.

**Computed, not formalized** (orchestrator, recorded in #18420):
- the witness satisfies the separator's hypotheses and violates its conclusion also at t = 1/200 and 1/1000;
- over 400 000 random family states, the 78 063 meeting the hypotheses all satisfy x ≤ 5(z − y), with largest value of x − 5(z − y) equal to −2.6·10⁻⁷.

**Argued, not formalized.**
- *Mechanism.* In the family (13) the subsystems B and C enter through the same three amplitudes for every level j. The witness gives the two excited levels of A unequal weights (3 and 1 on |j0j⟩, t and 5t on |jj0⟩). Near the boundary z − y → 0, this raises the AB negativity above every family state with the same y and z.
- *Scope.*
  - The refutation is at D = 3. Whether an analogous witness refutes the conjecture for every D > 3 is not determined.
  - The weaker squared-negativity monogamy inequality N²_A|BC ≥ N²_A|B + N²_A|C is not addressed.

**Effect on the paper.** For D = 3 the family (13) gives a subset of the achievable region, not the whole region. So the source's argument no longer justifies its family-derived boundary as a characterization of all three-qutrit triples. The module does not identify a particular polynomial inequality that the witness violates.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The citation listing used was incomplete. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
