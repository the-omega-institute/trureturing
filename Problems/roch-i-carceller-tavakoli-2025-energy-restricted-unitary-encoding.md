---
slug: roch-i-carceller-tavakoli-2025-energy-restricted-unitary-encoding
bibkey: rochicarcellertavakoli2025energyentanglement
doi: 10.1088/2058-9565/ae4d80
url: https://arxiv.org/abs/2510.27473v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation.result
---

# Unitary entanglement-assisted encoding beats every unassisted strategy in an energy-restricted four-message task

## Problem

C. Roch i Carceller and A. Tavakoli, *The role of entanglement in energy-restricted communication and randomness generation*, arXiv:2510.27473v1, Quantum Sci. Technol. 11, 025020 (2026), study prepare-and-measure communication whose only restriction is the vacuum component of the message, ⟨0|τ_x^C|0⟩ ≥ 1 − ω (Eq. (3)).
- **Result 4.** For the probabilistic transmission of a bit, unitary encodings of a shared pure entangled state give no advantage over unassisted quantum communication with shared randomness.
- **The question** (§VI, p. 9): "Whether unitary encoding remains resourceless for general tasks is an interesting open problem."

The verbatim statements are in [the literature note](../Library/QuantumChannels/rochicarcellertavakoli2025energyentanglement.md).

Issue [#17895](https://github.com/the-omega-institute/trureturing/issues/17895) fixes the reading:
- resourceless for general tasks means that, for every linear task and every energy 0 ≤ ω < 1/2, each unitary-encoded entanglement-assisted value is matched by an unassisted value;
- at ω ≥ 1/2 the question is settled by dense coding with a maximally entangled pair.

This statement is refuted: unitary encoding is a resource for a four-message task at ω = 288/625.

## Motivation

The source shows that entanglement helps energy-restricted communication only through non-unitary encodings for one bit. D'Avino, Senno, Alimuddin and Acín (arXiv:2510.27559) prove the same for any two-input task with ω < 1/2. The question asks whether the intuition from dense coding fails for every task under an energy restriction, or only for two inputs.

## Gap

Issue #17895 records the literature check before any Lean:
- arXiv v1 is the only version, and the journal version keeps the question;
- the companion arXiv:2510.27559v3 restricts to two inputs, and its theorem builds a common ground state for two encoded states;
- the later arXiv:2608.27357, 2509.06726 and 2608.09667, read in full text, do not treat unitary encoding beyond two inputs;
- Naixu-Guo/quantum-open-problems and the repository had no record.

`not-found-in-searched-scope`.

## Route

1. **Protocol.** Alice and Bob share Ψ = (4/5)|00⟩ + (3/5)|11⟩.
   - Alice encodes x = (u, v) by U_{uv} = Z^u R Z^v, with R = (1/5)[[4, −3], [3, 4]] and Z = diag(1, −1).
   - Every message marginal has vacuum component 337/625, so the energy is ω = 288/625 < 1/2.
   - Bob measures the orthonormal basis m_{uv} = (1/2)(1, −(−1)^v, (−1)^u, (−1)^{u+v}). Each overlap is 49/50, so the average success is 2401/2500.
2. **Pure-state inequality, in every Hilbert space.** For unit vectors ψ and |0⟩ and an effect 0 ≤ E ≤ 1: ⟨ψ, Eψ⟩ − ⟨0, E0⟩ ≤ √(1 − |⟨0|ψ⟩|²).
   - Choose the phase of ψ so that a = ⟨0|ψ⟩ ≥ 0, and put u = ψ + |0⟩ and v = ψ − |0⟩. The difference equals Re⟨u, Ev⟩ and also −Re⟨u, (1 − E)v⟩.
   - Cauchy–Schwarz for the positive forms of E and of 1 − E bounds its square by both ⟨u, Eu⟩⟨v, Ev⟩ and ⟨u, (1 − E)u⟩⟨v, (1 − E)v⟩. Together these give at most ‖u‖‖v‖/2 = √(1 − a²).
3. **Unassisted bound.** A message is an ensemble of unit vectors with weights summing to 1, the ensemble decomposition of its density operator.
   - Sum the pure inequality over the four messages, with Σ_x E_x = 1, and average over the ensembles and the shared randomness.
   - The averaging bound Σ_j w_j √t_j ≤ √(Σ_j w_j t_j), which is Cauchy–Schwarz for the sequences √w_j and √(w_j t_j), then shows that every unassisted strategy at energy ω succeeds with probability at most 1/4 + √ω. The message space has any dimension.
4. **Conclusion.** √(288/625) < 17/25, so every unassisted value is below 93/100 < 2401/2500.

## Falsifier

The refutation would not answer the question if:
- the module's strategies or energies differed from Eqs. (1)–(5);
- its unassisted side omitted shared randomness or mixed messages;
- its task were not a linear task of the source's form.

The module quantifies over every finite task and every 0 ≤ ω < 1/2. Its unassisted strategies have:
- an arbitrary complex Hilbert space for the message, with a unit vacuum vector;
- shared randomness over an arbitrary index type with weights summing to 1;
- messages given by ensembles of unit vectors. Every density operator has such a decomposition (its spectral decomposition), and every ensemble defines one;
- POVMs of positive bounded operators summing to the identity;
- the averaged energy restriction of Eq. (5).

This is the source's QC model, Eqs. (4)–(5), which fixes no message dimension. The unitary strategies are finite-dimensional, which only weakens the claim.

## Evidence

The canonical source is `D5/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation.lean` (506 lines).
- It defines `IsPOVM`, `UnitaryStrategy`, `encoded`, `unitaryProb`, `unitaryVacuum`, `QCStrategy`, `qcProb`, `qcVacuum`, `taskValue` and `claim`, and proves `result : ¬ claim`.
- It reuses frozen finite-dimensional matrix results for the protocol, and Mathlib's inner product spaces and operator order for the unassisted side. No frozen owner is changed.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- The escape registrations: `result` is the designated refutation result of the `utility` header and is exempt. The module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation.lean.json`, statement `sha256:d9e9b1fdef83e9af30768b0a86ded67b0f227ac8114b455b7a22e90443787c58`.

Declaration statements:
- `result`: `sha256:131df8981c442c115d95dbd2b558c08f0b1c26deb2621ffc905a794161ba45dd`;
- `claim`: `sha256:ad777371d7368117ec5e109036a9b372610f2fdc9502481ff97fd5d8572f68e7`.

## Triage

Tier 1 question of a 2025 paper, preregistered in issue #17895 before any Lean. The preregistration revision on #17895 widens the unassisted class to the source's model.
`theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the protocol identities are finite computations, and the bound is an instantiation of Cauchy–Schwarz for positive operators and Hölder's inequality for sums with exponents 2 and 2, followed by normalization | open-problem-resolution |
| the protocol, effect-bound and Jensen helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every other public declaration is a definition used by a public statement. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Refuted by `result`:** at ω = 288/625 < 1/2, a unitary-encoded entanglement-assisted strategy reaches 2401/2500 in four-message discrimination, while every unassisted strategy, with messages in any Hilbert space and arbitrary discrete shared randomness, stays below 93/100.

**Computed, not formalized** (orchestrator, exact, recorded in #17895): the four message marginals (1/625)[[337, ±84], [±84, 288]], Bob's constant marginal diag(16/25, 9/25), and the success matrix with diagonal entries 2401/2500.

**Argued, not formalized.**
- *Mechanism.* With two inputs, the energy restriction forces a common ground state close to both encoded states (the companion paper's proof). With four inputs, a partially entangled state with Schmidt coefficients 4/5 and 3/5 leaves every message marginal below the energy threshold. Meanwhile, four orthogonal sign patterns let Bob read two bits from the joint system, which no low-energy single message can carry as well.
- *Range.* Take the same construction with Ψ = cos t|00⟩ + sin t|11⟩ and R the rotation by t. Each message then has vacuum component cos⁴t + sin⁴t, so ω = sin²(2t)/2, and the success is ((1 + sin 2t)/2)². It beats the bound 1/4 + √ω exactly when sin 2t > 2√2 − 2, that is for 6 − 4√2 ≈ 0.343 < ω < 1/2. The true unassisted optimum may lie below this bound, so the advantage may extend further.

**Open.**
- The smallest ω at which unitary encoding helps in some task, and the optimal unitary value for four-message discrimination at each ω.
- Whether three inputs suffice.

**Effect on the paper.** Result 4 does not extend to general tasks: unitary encoding of a partially entangled state is already a resource for four messages below ω = 1/2.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
