---
slug: hertz-lupu-gladstein-heshami-goldberg-2025-loss-purity-log-convexity
bibkey: hertz2025lossbeamsplitters
doi: 10.1007/s40509-026-00402-0
url: https://arxiv.org/abs/2501.02047v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/FockAttenuator/LossPurityLogConvexityRefutation.result
---

# The purity of a state under loss is not always log-convex in the transmission

## Problem

A. Hertz, N. Lupu-Gladstein, K. Heshami and A. Z. Goldberg, *Equalities and inequalities from entanglement, loss, and beam splitters*, arXiv:2501.02047v1, Quantum Stud. Math. Found. **13**, 34 (2026), study the vacuum-environment loss channel ρ_T = Tr₂[B(T)(ρ₁ ⊗ |0⟩⟨0|)B(T)†], with B(T) = exp(arccos(√T)(a₁a₂† − a₁†a₂)).
- They prove that the purity Tr[ρ_T²] is convex in the transmission T.
- Conjecture 7 asserts the stronger "The purity of a state ρ₁ subject to loss is log-convex in T ∈ [0, 1]; ∂² log Tr[ρ_T²]/∂T² ≥ 0", equivalently (26) (P′)² ≤ P·P″ with P(T) = Tr[ρ_T²].
- Appendix B extends it to mixtures of identical two-copy states (Conjecture 19, (B4)).

The verbatim statements are in [the literature note](../Library/QuantumChannels/hertz2025lossbeamsplitters.md).

Issue [#16345](https://github.com/the-omega-institute/trureturing/issues/16345) fixes the reading: for every single-mode state ρ₁, the function T ↦ log Tr[ρ_T²] is convex on [0, 1]. It is refuted.

## Motivation

The source uses Conjecture 7 to extend its loss inequalities beyond 50% loss. Corollary 8 and the corollary following it each carry "If Conjecture 7 is true then this Corollary can be extended to all T", and Appendix C repeats the remark for the second derivatives of lossy states. Log-convexity is also the statement that the order-2 Rényi entropy of a lossy state is concave in T.

## Gap

Issue #16345 records the literature check before any Lean:
- the only arXiv version states Conjectures 7 and 19 as open;
- the three citing works (arXiv:2510.09747, 2506.21831, 2411.03423) do not settle them;
- web and Zenodo searches return no settlement;
- the repository had no entry for the paper.

The published version was not read (publisher authorization step); the search seat reports that it keeps the conjecture.

`not-found-in-searched-scope`.

## Route

1. **The input.** ρ₁ = (1/100)|0⟩⟨0| + (3/4)|1⟩⟨1| + (6/25)|2⟩⟨2|, a finite ensemble of Fock states.
2. **The channel.** The beam splitter acts on |0⟩, |1⟩, |2⟩ with vacuum environment through its Fock expansion, with transmission amplitude √T. The partial trace over the environment, slice by slice, gives the output diag(q₀, q₁, q₂) with
   - q₀ = 1/100 + (3/4)(1 − T) + (6/25)(1 − T)²;
   - q₁ = (3/4)T + (12/25)T(1 − T);
   - q₂ = (6/25)T².
   This is binomial thinning of the photon number.
3. **The purity.** P(T) = Tr[ρ_T²] = (1728T⁴ − 8856T³ + 17529T² − 12300T + 5000)/5000, as a convergent Fock-basis trace with a zero tail.
4. **The contradiction.** Log-convexity on [0, 1] at the midpoint 49/50 of 39/40 and 197/200 would give P(49/50)² ≤ P(39/40)·P(197/200). Exact arithmetic gives P(49/50)² − P(39/40)·P(197/200) = 7296233469022569/15625000000000000000000 > 0.

## Falsifier

The refutation would fail if:
- the source's loss channel differed from the beam splitter with vacuum environment and the second mode traced out;
- its transmission convention were not the amplitude √T (B(T) with arccos √T; T = 1 is no loss);
- Conjecture 7 were restricted to a class of states excluding diagonal three-level Fock mixtures.

The source states it for "a state ρ₁", and every finite ensemble is a state.

## Evidence

The canonical source is `D5/S3/Quantum/QuantumChannels/FockAttenuator/LossPurityLogConvexityRefutation.lean` (349 lines).
- It defines `loss`, `IsPurityCurve` and `claim`, and proves `result : ¬ claim`.
- It reuses:
  - the frozen Fock space, basis and abbreviations (`TransmissivityBetaPriorProbeRefutation`, `PureLossIncompatibility`);
  - `beamSplitter`, `tensor` and `beamUnitary_fock` (`FockAttenuator/BeamSplitter`);
  - `purePartialTrace` (`FockAttenuator/DisplacementCovariance`);
  - `fockPair_apply` (`FiniteFockBeamSplitterNonExtremality`);
  - `finiteDiagonal` (`FockAttenuator/Entropy`);
  - the beam-splitter lemmas `split_zero`, `split_one`, `split_zero_coord`, `split_one_coord` and `vacuum_tensor` of `PureLossIncompatibility`, which this delivery makes public. Their §3.9 registrations are `declared_validated`.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- `result` is a refutation result and is exempt from the §3.9 registration.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/QuantumChannels/FockAttenuator/LossPurityLogConvexityRefutation.lean.json`, statement `sha256:27d9704f3d6b5a4385928e7ee9149fca5bffef8e260944dd6f2ef01da276744c`.

Declaration statements:
- `result`: `sha256:e4a16c45ff71b9e1d515600c9620fd403520de2bd8605f34e4635d87c8685bd8`;
- `claim`: `sha256:cd8705285e6f8dfd0435a088e03a9c06740b5fa196974d3f0b95725e9353d7de`.

## Triage

Tier 1 conjecture of a 2025 paper (published 2026), preregistered in issue #16345 before any Lean.
`theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: the route instantiates the frozen beam-splitter Fock expansions and partial trace, and checks a rational midpoint inequality | open-problem-resolution |
| the slice, partial-trace, output, purity and midpoint helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every other declaration is a definition used by a public statement or a compiler-generated proof on the proof path of `result`. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The utility is `certified-instance` with basis `refutes` of `claim`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** Conjecture 7 is false. There is a state, the finite mixture above, whose purity under loss is not log-convex on [0, 1].

**Established inside the proof.** For the witness, the output of the loss channel is exactly diag(q₀, q₁, q₂) on the whole Fock space, and its purity is the quartic P(T) above.

**Computed, not formalized** (orchestrator, SymPy and exact rational arithmetic, 14 October 2026). The purity of a diagonal input is the collision probability Σ_j q_j² of its binomially thinned photon number, so the question is whether that collision probability stays log-convex along thinning.
- Two-level diagonal inputs p₀|0⟩⟨0| + p₁|1⟩⟨1| satisfy (26) on [0, 1]: P·P″ − P′² = 8T(1 − p₀)³(1 − Tp₁) ≥ 0. Among 20 000 random states on span{|0⟩, |1⟩} with coherences, at random T, no violation occurred (minimum 5·10⁻⁹); this is a sample, not a proof.
- For diagonal three-level inputs, (26) at T = 1 reads
  4(p₀³p₂ − 4p₀²p₁p₂ + 5p₀²p₂² + 2p₀p₁³ − 3p₀p₁²p₂ + 4p₀p₁p₂² + p₀p₂³ − 2p₁²p₂² + 4p₁p₂³ + p₂⁴) ≥ 0.
  Wherever this is negative, (26) fails on an interval ending at T = 1. For p₀ = 0 it equals 4p₂²(p₂² + 4p₁p₂ − 2p₁²), which is negative exactly when p₁/p₂ > 1 + √6/2 ≈ 2.22.
- A simpler counterexample follows: (3/4)|1⟩⟨1| + (1/4)|2⟩⟨2| has P(79/80)² − P(39/40)·P(1) = 940596359849/107374182400000000 > 0.

**Argued, not formalized.** Conjecture 19 is false as well. With Φ = ρ₁ ⊗ ρ₁ and λ = 1 − 2T, (B4) becomes the source's (B1), which is (26) through the purity formula Tr[ρ_T²] = Tr[ρ₁⊗ρ₁ (1 − 2T)^{N−}]. Take λ = −24/25, that is, T = 49/50.

**Open.**
- Whether Conjecture 7 holds for every pure state; the witness is mixed.
- Whether it holds on the range T ≤ 1/2, where the source proves convexity for general states. The witness violates (26) exactly on (T*, 1] with T* ≈ 0.9701, the only root of P·P″ − P′² in [0, 1].

**Effect on the paper.** The suggested extensions of Corollary 8, of the following corollary and of the Appendix C second-derivative expressions "to all T", stated as consequences of Conjecture 7, have no basis. Their proved range T ≤ 1/2, the convexity of the purity, and the modified-parameter log-convexity in ℓ = log(1 − 2T) are not affected.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
