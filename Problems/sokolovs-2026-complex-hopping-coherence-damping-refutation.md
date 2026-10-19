---
slug: sokolovs-2026-complex-hopping-coherence-damping-refutation
bibkey: sokolovs2026paritysuperselection
doi: null
url: https://arxiv.org/abs/2603.14154v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/SpinChains/ComplexHoppingCoherenceDampingRefutation.result
---

# Complex hopping can increase parity-twisted ground-state coherences

## Problem

A. Sokolovs, *Parity superselection obstructs monogamy of mutual information in free fermions*, arXiv:2603.14154v2, Section 7:

> Theorem~\ref{thm:damping} settles the coherence damping inequality for ground states with real non-positive hopping; whether it extends to systems with complex hopping (e.g., in a magnetic field) or frustrated lattices remains open.

Theorem 1 states |ρ^tw_ij| ≤ ρ^spin_ij = |ρ^spin_ij| for D-parity-changing elements, where ρ^spin is the ordinary partial trace over B and ρ^tw = tr_B[(−1)^{N_B} ρ_ABD]. The verbatim passages are in [the literature note](../Library/QuantumContext/sokolovs2026paritysuperselection.md).

Issue [#19153](https://github.com/the-omega-institute/trureturing/issues/19153) fixes the reading: for number-conserving free-fermion Hamiltonians with complex hopping, the ground state satisfies |ρ^tw_ij| ≤ |ρ^spin_ij| for every D-parity-changing pair and every tripartition into adjacent blocks. It is refuted.

## Motivation

By the source's Proposition 1, the D-parity-changing blocks of the fermionic reduced state are those of ρ^tw. Damping therefore controls the gap between fermionic and spin entropies, which drives the paper's monogamy results.

## Gap

The literature check before any Lean is recorded in #19153:
- arXiv v2 is the latest version;
- OpenAlex finds no record;
- the repository had no record of the paper.

`not-found-in-searched-scope`.

## Route

**The instance.** Four ordered modes, with A = {1}, B = {2}, D = {3} and E = {4}. H = Σ h_jk c_j† c_k with h = (1/50)[[14, −9+16i, −48, −12−12i], [−9−16i, 14, −12+12i, −48], [−48, −12−12i, −14, −16+9i], [−12+12i, −48, −16−9i, −14]].

**The ground state.**
1. h has eigenvalues −3/2, −1/2, 1/2, 3/2, with Gaussian-rational eigenvectors.
2. The Slater determinant of the two negative modes is a ground state of the many-body Hamiltonian, by its diagonalization.

**The comparison.** At the D-parity-changing pair (n_A, n_D) = (0, 1) against (1, 0), |ρ^tw| = 12/25 > 84/625 = |ρ^spin|.

## Falsifier

The refutation would fail if the module's quantities differed from the source's. The module:
- uses occupation-basis matrix elements with Jordan–Wigner annihilators;
- defines the spin trace and the twisted trace exactly as in Section 3, after tracing E;
- takes ground states as normalized minimizers of the energy;
- quantifies over every adjacent tripartition and every D-parity-changing pair.

## Evidence

The canonical source is `D5/S3/Quantum/SpinChains/ComplexHoppingCoherenceDampingRefutation.lean` (348 lines).
- **Proof.** It proves `result : ¬ claim` for the instance above.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Registration.** The refutation `result` is exempt from §3.9 registration, and the module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/SpinChains/ComplexHoppingCoherenceDampingRefutation.lean.json`, statement `sha256:c3b4a4ea839f55a7fa93a4ad0d419d8f783eab105c688ed82fd16dd0f55b3471`.

Declaration statements:
- `result`: `sha256:c2c593e2fa472ff3517be1d576d8c65bc6dbd2bc1f358ec44abea3c7f23d9b96`;
- `claim`: `sha256:6d7ec17d6a1d31b503543ee13815c28e8a69d6c1ceb0fb046b1c406f93a93853`.

## Triage

Tier 1 open question of a 2026 paper, preregistered in issue #19153 before any Lean.
`theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none | open-problem-resolution |
| definitions | bind-only | none | definitions used by `claim` |
| private helpers | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. `utility: kind=certified-instance; basis=refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** with complex hopping, the parity-twisted coherence of a free-fermion ground state can exceed the spin coherence; here the ratio is 12/25 to 84/625, about 3.6.

**Computed, not formalized** (orchestrator, recorded in #19153):
- the many-body ground state is unique, with N = 2;
- the spectral gap is 1/2.

**Argued, not formalized.**
- *Mechanism.* With real non-positive hopping the amplitudes are non-negative, so inserting (−1)^{N_B} can only cancel terms of ρ^spin. Complex hopping allows the B-even and B-odd contributions to have different phases. They then cancel in ρ^spin and add in ρ^tw, so the damping reverses.
- *Scope.* The instance is a connected, flux-carrying four-site free-fermion model. The frustrated-lattice part of the source's question, with real but sign-frustrated hopping, is not addressed here.

**Effect on the paper.** Theorem 1 is unaffected. Its hypothesis of real non-positive hopping cannot be dropped.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
