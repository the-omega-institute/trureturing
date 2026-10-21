---
slug: song-et-al-2024-steering-temporal-compatibility-refutation
bibkey: song2024causalclassification
doi: 10.1103/PhysRevLett.133.110202
url: https://arxiv.org/abs/2306.09336v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Contextuality/SteeringTemporalCompatibilityRefutation.result
---

# Steering does not guarantee atemporality

## Problem

M. Song, V. Narasimhachar, B. Regula, T. J. Elliott and M. Gu, *Causal classification of spatiotemporal quantum correlations*, arXiv:2306.09336v2 (Phys. Rev. Lett. 133, 110202), Discussion:

> Some entangled states are not atemporal, so is atemporality a strictly stronger notion of quantum correlations? And if so, is it guaranteed by steering or Bell non-locality?

Here:
- **Temporally compatible from A to B:** R = (id ⊗ Λ)K with K = {ρ_A ⊗ I/2, S} for a quantum channel Λ, the source's Eq. (3). The reverse direction is symmetric.
- **Atemporal:** temporally compatible in neither direction.

The definitions are quoted in [the literature note](../Library/QuantumContext/song2024causalclassification.md).

Issue [#19923](https://github.com/the-omega-institute/trureturing/issues/19923) fixes the reading of the steering clause: every two-qubit density operator that is EPR-steerable in at least one direction would be atemporal. This is refuted. The Bell-nonlocality clause is not addressed.

## Motivation

The source introduces atemporality as a certificate that observed correlations need a common cause: no temporal process, sending one qubit through a channel, reproduces them. It proves that atemporal two-qubit states must be entangled, and that sufficiently strong entanglement guarantees atemporality. It then asks where atemporality sits in the hierarchy of quantum correlations, in particular whether steering already guarantees it.

## Gap

The literature check before any Lean is recorded in #19923:
- the source's v1 and v2 keep the question;
- the search seat screened 13 of the 14 OpenAlex citing works and found no steerable temporally compatible state;
- the repository had no record.

`not-found-in-searched-scope`.

## Route

Let R = (1/10000)[[5391,0,0,1782],[0,3609,1188,0],[0,1188,401,0],[1782,0,0,599]].
1. **Density.** R is a two-qubit density operator: it is a positive combination of two rank-one projections and ρ_A ⊗ I/2, with ρ_A = diag(9/10, 1/10).
2. **Temporal compatibility.** The Pauli channel E(H) = (4183 H + 3787 XHX + 223 YHY + 1807 ZHZ)/10000 is CPTP, and R = (id ⊗ E)K. So R is temporally compatible from A to B and is not atemporal.
3. **Steering.** Bob measures X and Z.
   - With C = diag(1/9, 1) and two symmetric matrices U, V such that C ± U and C ± V are rank-one positive, every local-hidden-state model satisfies Q = tr[U(D_X + D_Z) + V(D_X − D_Z)] ≤ 2 tr(Cρ_A) = 2/5. Here D_x is the difference of Alice's two conditional states for setting x.
   - The quantum assemblage gives Q = 10197/25250 > 2/5, so R is steerable from B to A.

## Falsifier

The counterexample would not answer the question if the module's notions differed from the source's. The module:
- defines temporal compatibility by the source's Eq. (3), with a completely positive trace-preserving map;
- defines atemporality as incompatibility in both directions, matching f = min(→f, ←f);
- defines steerability as the absence of a local-hidden-state model for some finite family of projective measurements on one party.

For finitely many settings, an LHS model is equivalent to a decomposition indexed by deterministic response functions.

## Evidence

The canonical source is `D5/S3/Quantum/Contextuality/SteeringTemporalCompatibilityRefutation.lean` (376 lines).
- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Contextuality/SteeringTemporalCompatibilityRefutation.lean.json`, statement `sha256:58b22f37438506158613fb5a9d771f1cd29e4afe465a806bfe9eec84dcd6963c`.

Declaration statements:
- `result`: `sha256:024b48bc0ccd3f22cbecd9e7fc01bdd29be323f04683540c32b18d63f7b86a3b`;
- `claim`: `sha256:5284daf80732f60c623a16d563c5457494654af93e3adb691964f15b33c883bf`.

## Triage

Tier 1 question of a 2024 paper, preregistered in issue #19923 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. `utility: kind=certified-instance; basis=refutes`. There is no digestion atom.

### What the settlement shows

**Proved in the module:** the state R above is a two-qubit density operator that is temporally compatible from A to B and steerable from B to A. Hence steerability in some direction does not imply atemporality.

**Computed, not formalized** (orchestrator, recorded in #19923):
- *Exact values.* The steering violation is 97/25250.
- *Robustness (SDP).* An LHS model survives at most a mixing fraction 0.9905 with white noise for settings {X, Z}, and 0.9720 for {X, Y, Z}.
- *The other direction.* For the settings {X, Z} and {X, Y, Z} on A, the SDP finds an LHS model, so no steering from A to B is detected with these settings.

**Argued, not formalized.**
- *Mechanism.* Temporal compatibility from A to B asks only that R be the image of K under some channel on B, and K depends on R only through ρ_A. With ρ_A = diag(9/10, 1/10), the Pauli channel E keeps enough X and Z correlation in (id ⊗ E)K for Bob's two measurements to violate the two-setting LHS bound.
- *Scope.* The example is one-way steerable. Whether a state steerable in both directions, or a Bell-nonlocal state, can be temporally compatible is not determined here.
- *Effect on the paper.* Atemporality is not implied by one-way EPR steering. The question remains whether it is implied by two-way steering or by Bell nonlocality.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority; the citing works were screened by the search seat, not by the orchestrator. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
