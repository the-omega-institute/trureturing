---
slug: basso-maziero-2020-correlated-coherence-monogamy-refutation
bibkey: basso2020correlatedcoherence
doi: 10.1088/1402-4896/abafcb
url: https://arxiv.org/abs/2006.14037v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/CorrelatedCoherenceMonogamyRefutation.result
---

# The l1-norm correlated coherence is not monogamous for tripartite pure states

## Problem

M. L. W. Basso and J. Maziero, *Monogamy and trade-off relations for correlated quantum coherence* (Phys. Scr. 95, 095105 (2020); arXiv:2006.14037), study the coherence contained in correlations.
- **The quantities.** For the l1-norm coherence C in a fixed product basis, the correlated coherence of a bipartite marginal is C^c(ρ_XY) = C(ρ_XY) − C(ρ_X) − C(ρ_Y), and C^c(ρ_A|BC) = C(ρ_ABC) − C(ρ_A) − C(ρ_BC).
- **The known case.** They prove the monogamy relation C^c(ρ_A|BC) ≥ C^c(ρ_AB) + C^c(ρ_AC) under the conditions (22)–(24) and in several examples.
- **The conjecture.** They state it for all pure states: "seems reasonably to conjecture that the monogamy relation C^c_l1(ρ_A|BC) ≥ C^c_l1(ρ_AB) + C^c_l1(ρ_AC) holds for any tripartite pure quantum state".

The verbatim statements are in [the literature note](../Library/QuantumChannels/basso2020correlatedcoherence.md).

Issue [#18402](https://github.com/the-omega-institute/trureturing/issues/18402) fixes the reading. By Eq. (33) the relation says 0 ≤ M, where M = C(ρ_ABC) + C(ρ_A) + C(ρ_B) + C(ρ_C) − C(ρ_AB) − C(ρ_AC) − C(ρ_BC). The conjecture is refuted for three qubits.

## Motivation

A monogamy relation would make correlated coherence a quantity that cannot be freely shared, like entanglement. The source notes that the l1 correlated coherence does not vanish for uncorrelated separable states, which makes monogamy for pure states a natural test.

## Gap

Issue #18402 records the literature check before any Lean:
- arXiv v1 and v2 keep the conjecture;
- the seven works citing the source treat other coherence quantities;
- the repository had no record of the paper.

`not-found-in-searched-scope`.

## Route

Take ψ = w/√49922 with w = (−16, 1, 128, −16, −128, −16, 1, −128) in the order |000⟩, …, |111⟩.
1. **Normalization.** Σ w² = 49922.
2. **The seven coherences.** Each reduced state is a finite sum of products w_u w_v/49922. Multiplied by 49922, the seven l1 coherences are:
   - C_ABC = 138434;
   - C_A = 8416, C_B = C_C = 288;
   - C_AB = C_AC = 48928, C_BC = 50336.
3. **The gap.** M = (138434 + 8416 + 288 + 288 − 48928 − 48928 − 50336)/49922 = −766/49922 = −383/24961 < 0.

## Falsifier

The refutation would not settle the conjecture if:
- the module's coherence differed from the l1 norm of the off-diagonal entries in the product basis;
- its reduced states differed from the partial traces;
- M differed from the difference of Eq. (33).

The module takes:
- the l1 coherence Σ_{i≠j} |ρ_ij|;
- the reduced states of `PurityTimeReversalOverlapMinimum.reducedState` (the partial trace of ψψ† over the qubits outside a set);
- M as the alternating sum of Eq. (33).

The conjecture is stated for all tripartite pure states, so its restriction to three qubits suffices.

## Evidence

The canonical source is `D5/S3/Quantum/Information/CorrelatedCoherenceMonogamyRefutation.lean` (233 lines).
- It defines `l1Coherence`, `monogamyGap` and `claim`, and proves `result : ¬ claim`.
- It reuses the reduced states of `PurityTimeReversalOverlapMinimum`.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- The escape registrations: `result` is the designated refutation result of the `utility` header and is exempt. The module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Information/CorrelatedCoherenceMonogamyRefutation.lean.json`, statement `sha256:ea1c6e618b2b04f9616c41a7ba84ea9d619d5989df673df6a43445869c367921`.

Declaration statements:
- `result`: `sha256:f7fba1dbe009554f89a8b22602d932ff09dd1307e79469300cfd03efdfd1d580`;
- `claim`: `sha256:7593426a030a92b1786c349fdc1e980d82e09afda1030608128de0ef867c652d`.

## Triage

Tier 1 conjecture of a 2020 paper, preregistered in issue #18402 before any Lean.
`theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the normalization, the reduced states and the seven coherences are finite sums, and the comparison is rational arithmetic | open-problem-resolution |
| the witness and summation helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every declaration is bind-only. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Refuted by `result`:** the normalized vector w/√49922 has M = −383/24961 < 0, so C^c_l1(ρ_A|BC) < C^c_l1(ρ_AB) + C^c_l1(ρ_AC).

**Computed, not formalized** (orchestrator, recorded in #18402):
- on a grid of 324 points of the open family v = (−x, z, 1, −x, −1, −x, z, −1), 0 < x < 1/4, 0 < z < x(1 − 4x)/7, every value of M is negative;
- a scan of 20 000 random complex pure states finds no violation.

**Argued, not formalized.**
- *Mechanism.*
  - Write R_S for the sum of |ρ_uv| over pairs of basis indices differing exactly on the coordinates S. Write Δ_T ≥ 0 for the cancellation lost in the partial trace to T.
  - Then M = R_ABC + Δ_AB + Δ_AC + Δ_BC − Δ_A − Δ_B − Δ_C.
  - The source's conditions (22)–(24) make the singleton deficits Δ_A, Δ_B, Δ_C vanish, which gives M ≥ R_ABC ≥ 0.
  - The witness has real amplitudes of mixed sign. Their destructive interference in the one-body marginals makes the singleton deficits outweigh the rest.
- *Scope.* A violation needs such cancellations. A scan of 20 000 random complex pure states found no violation; the size and measure of the set of violating states are not determined. M is continuous in ψ, so the strict violation persists on a neighbourhood of the witness, including complex perturbations of its amplitudes. The weaker trade-off (41) of the source is not addressed.

**Effect on the paper.** The monogamy relation of Theorem 3 needs a condition of the type (22)–(24). It does not hold for all tripartite pure states.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The full text of Gao–Liu–Li–Qiao, IJTP 59, 3635 (2020), was not read. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
