---
slug: li-jiang-2026-fixed-noise-polar-pair-optimality-refutation
bibkey: lijiang2026highrank
doi: null
url: https://arxiv.org/abs/2609.00778v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.result
---

# The polar rank-one encoder of Li–Jiang is not exactly optimal at fixed noise

## Problem

B. Li and L. Jiang, *High-Rank Encoding Can Improve Approximate Quantum Error Correction*, arXiv:2609.00778v1, compare encoders of a logical qudit into two qudits under a family of noise channels N_p (Eqs. (18)–(23)).
- **The pair.** For a unit vector χ, the encoder C_{V_p(χ)} uses the polar isometry V_p(χ) = C_p(χ)[C_p(χ)†C_p(χ)]^{−1/2} with C_p(χ) = Q_p(I ⊗ |χ⟩) (Eq. (S60)), and the decoder is the partial trace tr_S. The supplement shows that this rank-one pair attains the optimal quadratic coefficient of the rank-one gap as p → 0 (Eqs. (S63)–(S64)).
- **The question.** "Exact optimality of this pair at fixed p > 0 remains open" (after Eq. (S64)).

The verbatim statements are in [the literature note](../Library/QuantumChannels/lijiang2026highrank.md).

Issue [#13324](https://github.com/the-omega-institute/trureturing/issues/13324) fixes the reading. For every d ≥ 2, 0 < p < 1 and unit χ, the pair is claimed to be optimal against every pair of completely positive trace-nonincreasing encoder and decoder whose encoder has input-first Choi rank at most one (the source's rank-one class, Eq. (13)), for the entanglement fidelity at τ = I/d. The question is answered negatively.

## Motivation

The polar construction is how the source shows that rank-one encoders achieve the optimal leading-order behaviour near perfect recovery. Whether the same pair is exactly optimal at finite noise decides whether that construction also gives the rank-one optimum, or only its asymptotics.

## Gap

Issue #13324 records the literature check (5 October 2026):
- arXiv v1 is the only version;
- the citing paper Ru–Li–Gao–Jiang (arXiv:2609.40203v1) and a later paper of the authors (arXiv:2609.17439) do not settle the question;
- MathDB, formal-conjectures and the repository's records had no entry.

`not-found-in-searched-scope`.

## Route

Take d = 2, p = 9/13 and χ = |0⟩, in the order (00, 01, 10, 11).
1. **The source pair.** The polar encoder has columns (3|00⟩ − |11⟩)/√10 and |10⟩, evaluated from the positive Gram square root and its inverse.
2. **The competitor.** Replace the first column by (24|00⟩ − 7|11⟩)/25 and keep the second column and the decoder tr_S. Both encoders are isometries, so they are completely positive and trace-preserving with a single Kraus operator.
3. **The fidelities.** An explicit 24-term Kraus family realizes Eq. (23) exactly. The entanglement fidelity of a composite Kraus family is d⁻² Σ |tr K|². The competitor exceeds the source pair by 7(10279 − 3250√10)/260000 > 0, since 10279² − 10·3250² = 32841 > 0.

## Falsifier

The refutation would not hold if:
- the module's noise differed from Eq. (23);
- its polar matrix were not the positive inverse square root of Eq. (S60);
- its feasible class or fidelity were narrower or different from the source's.

The module writes Eq. (23) literally for every code matrix and builds the encoder from `CFC.sqrt` and the matrix inverse. It quantifies over all completely positive trace-nonincreasing pairs with input-first Choi rank at most one. Its fidelity is the overlap of the canonical purification with no output renormalization.

## Evidence

The canonical source is `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.lean` (732 lines).
- It defines `lambda1`–`lambda5`, `sourceQ`, `sourceD`, `sourceB`, `sourceE`, `sourceNoise`, `sourceC`, `sourcePolar`, `matrixAction`, `TraceNonincreasing`, `inputFirstChoi`, `entanglementFidelity` and `claim`, and proves `result : ¬ claim`.
- The decoder is the frozen `PassiveMemoryNonclassicalRefutation.discardMemory`.
- The Kraus fidelity comes from the frozen `MayerZeroFidelityTightness.kraus_survival` with `PeritoTsirelson.max_entangled_trace`.
- Kraus maps come from the frozen `FiniteKrausChannel`. The Choi matrix and `choi_of_kraus` come from `FiniteKrausRepresentation` (Closed, not frozen), under the same namespace.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- `result` is the refutation result of a `refutes` utility, which CLAUDE.md §3.9 exempts from four-slot registration.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.lean.json`, statement `sha256:bc29580ea44e7258e8e8710725ea1a0d9fec7e8061a833ad545012f89b159f8f`.

Declaration statements:
- `result`: `sha256:981776d1c5619da90b259dd5fb6b4a42d1f18251d9e72329a3f55279bb10e05a`;
- `claim`: `sha256:bf23a768dd9abea634ecc480dcf6987a75ec50d7140080485f663c76f3f7cc3e`.

## Triage

Tier 1 question of a 2026 paper, preregistered in issue #13324 before any Lean.
`counterexample`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the noise realization, the Gram square root, the Choi rank bound, the Kraus fidelity and the strict gain are instantiations of frozen D5 and pinned Mathlib results followed by normalization | open-problem-resolution |

Every other declaration is a definition used by a public statement or a compiler-generated proof on the proof path of `result`. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The utility is `certified-instance` with basis `refutes` the module's `claim`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** at d = 2, p = 9/13 and χ = |0⟩, a feasible rank-one pair with the same decoder has strictly larger entanglement fidelity than the source's polar pair, so the pair is not exactly optimal at fixed p > 0.

**Computed, not formalized** (orchestrator, NumPy and SymPy, 14–15 October 2026, built from Eqs. (18)–(23) and (S60)):
- The Kraus family of Eq. (23) is trace-preserving and reproduces the adjoint Choi matrix of Eq. (21).
- At p = 36/37 the competitor with first column (1431|00⟩ − 1040|11⟩)/1769 gains exactly 2426827/81050449900 over the source pair.
- Maximizing over isometric encoders with the decoder tr_S fixed finds a positive gain at every tested p in {0.05, 0.1, 0.3, 0.5, 0.7, 0.9, 36/37}, from 8.7 × 10⁻⁹ to 9.4 × 10⁻⁵. At p = 0.01 the difference is below the optimizer's resolution.

**Argued, not formalized.**
- At p = 36/37, rotating the encoder's first column within the span of |00⟩ and |11⟩ with the decoder fixed changes the fidelity at first order: its derivative at the source pair is −156/45325 in the rotation angle (exact, orchestrator). So there the source pair is not even stationary within the rank-one class, although the source shows it is optimal to quadratic order as p → 0.
- Preregistration #13324 records a closed form λ₂r(2 − s)/(3(1 + r²)) > 0 for such a first-order gain at d = 2, χ = |0⟩ and every 0 < p < 1, with r = √(3(1 − p)/(3 + p)) and s = √(2(1 + r²)). It was derived by the preregistering session and is not re-derived here.

**Open.**
- The exact rank-one optimum F₁^opt(τ, N_p) at fixed p, and whether optimizing the decoder as well changes the optimal encoder.
- Whether the polar pair fails for every d ≥ 2 and every 0 < p < 1; this settlement exhibits one d, one p and one χ.

**Effect on the paper.** The polar pair remains asymptotically optimal to quadratic order (Eqs. (S63)–(S64)); exact optimality at fixed noise fails, so the closed form of the rank-one optimum remains open.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
