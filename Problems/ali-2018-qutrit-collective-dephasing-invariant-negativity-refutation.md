---
slug: ali-2018-qutrit-collective-dephasing-invariant-negativity-refutation
bibkey: ali2019qutritfreezing
doi: 10.1142/s0217732319501025
url: https://arxiv.org/abs/1810.01123v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Decoherence/QutritCollectiveDephasingInvariantNegativityRefutation.result
---

# Collective dephasing of two qutrits admits nonstationary states with constant positive negativity

## Problem

M. Ali, *Freezing dynamics of entanglement and nonlocality for qutrit-qutrit (3 ⊗ 3) quantum systems*, arXiv:1810.01123v1, published in Mod. Phys. Lett. A 34, 1950102 (2019). The conjecture is in the Conclusions:

> We have found no evidence for time-invariant entanglement for qutrit-qutrit states and based on our results, we conjecture that under current dynamics, this feature of time-invariant entanglement may not exist for qutrit-qutrit systems.

The feature, the Kraus operators of the collective dephasing and the entanglement measure are quoted in [the literature note](../Library/QuantumContext/ali2019qutritfreezing.md).

Issue [#19382](https://github.com/the-omega-institute/trureturing/issues/19382) fixes the reading:
- **Hypotheses:** a rate Γ > 0 and a density matrix ρ₀ whose negativity is positive and constant along Φ_{Γ,t} for all t ≥ 0.
- **Conclusion:** ρ₀ is stationary.

The conjecture is refuted.

## Motivation

In the source the feature means that the state changes at every instant while its entanglement stays constant. It had been observed for qubit-qubit and qubit-qutrit systems under collective dephasing. The source tests the family ρ_{α,β}, which mixes an isotropic state with a decoherence-free maximally entangled state, together with 100 random pure states. Every test shows decaying or freezing negativity. The follow-up arXiv:1905.05462 restates that 3 ⊗ 3 shows no time-invariant entanglement.

## Gap

The literature check before any Lean is recorded in #19382:
- arXiv has only v1;
- OpenAlex lists one citing work, the author's arXiv:1905.05462, which restates the observation;
- three further OpenAlex searches and a Zenodo search found no record;
- the repository had no record of the conjecture.

`not-found-in-searched-scope`.

## Route

Take Γ = 2 and ρ₀ = ¾ |φ⟩⟨φ| + ¼ |χ⟩⟨χ|, with φ = (|01⟩+|10⟩)/√2 and χ = (|00⟩+|11⟩)/√2.
1. **Evolution.** The channel multiplies each entry ρ_{ij} by Σ_k D_k(i) D_k(j). For ρ₀ every entry is unchanged except ρ_{00,11} = ρ_{11,00} = 1/8, which becomes γ⁴/8 because γ² + ω₁ω₂ = γ⁴. Here γ = e^{−t}.
2. **Negativity.** The partial transpose of ρ(t) is A − B, with:
   - A = ¼ u₊u₊ᴴ + ((3+γ⁴)/16) w₊w₊ᴴ + ((3−γ⁴)/16) w₋w₋ᴴ;
   - B = ⅛ u₋u₋ᴴ;
   - u± = |00⟩ ± |11⟩ and w± = |01⟩ ± |10⟩.

   Both parts are positive semidefinite and AB = 0. So ‖ρ(t)^{T_B}‖₁ = Tr A + Tr B = 3/2, and the negativity is 1/4 for every t ≥ 0.
3. **Not stationary.** At t = 1 the (00,11) entry is e^{−4}/8 ≠ 1/8.

## Falsifier

The refutation would fail if the module's dynamics or measure differed from the source's. The module:
- uses the three diagonal Kraus operators of §II with γ = e^{−Γt/2}, ω₁ = √(1−γ²), ω₂ = −γ²√(1−γ²) and ω₃ = (1−γ²)√(1+γ²), in the basis order of §II;
- forms ρ(t) = Σ_k D_kᴴ ρ₀ D_k;
- measures entanglement by the negativity (‖ρ^{T_B}‖₁ − 1)/2. This is the measure of §III, whose maximal value 1 on two qutrits matches the source's plotted values near 0.9985.

## Evidence

The canonical source is `D5/S3/Quantum/Decoherence/QutritCollectiveDephasingInvariantNegativityRefutation.lean` (228 lines).
- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Registration.** The refutation `result` is exempt from §3.9 registration, and the module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Decoherence/QutritCollectiveDephasingInvariantNegativityRefutation.lean.json`, statement `sha256:79eed3b34c5b3152ed78f6e4eafd9a594b8736c6012a2a2c57d29cb403970034`.

Declaration statements:
- `result`: `sha256:bca87a0d735bc3a08eab7e2c92c308e0ebee29e6c0d23e7ed46ac6f9a76f3e43`;
- `claim`: `sha256:aaa082202620b63212f8812189b224767bb053ce9d3a361fb423b06ea5872382`.

## Triage

Tier 1 conjecture of a 2018 paper, preregistered in issue #19382 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. `utility: kind=certified-instance; basis=refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** the conjecture fails for the state above. Its negativity is 1/4 for every t ≥ 0, while the state is not stationary.

**Computed, not formalized** (orchestrator, recorded in #19382):
- for γ ∈ {1, 0.9, 0.5, 0.1, 0} the negativity is 0.25 to twelve digits, and the spectrum moves from (0, 1/4, 3/4) to (1/8, 1/8, 3/4);
- the source's family ρ_{α,β} at α = β = 0.999 reproduces the slow decay from 0.998500541 to 0.998500375.

**Argued, not formalized.**
- *Mechanism.* On the levels {0,1} the dynamics restrict to two-qubit collective dephasing. The witness is the known two-qubit time-invariant example: the decoherence-free Bell state φ shields the decaying Bell state χ. While the weight of φ exceeds 1/2, the decaying coherence moves only positive eigenvalues of the partial transpose. The negative eigenvalue −(2p−1)/2 then stays fixed. The conjecture, stated for the whole 3 ⊗ 3 space, does not exclude states supported on a qubit-qubit corner.
- *Range.* The same argument gives constant negativity (2p−1)/2 for every weight p ∈ (1/2, 1) of φ.
- *Coexistence.* The source also observes freezing dynamics in 3 ⊗ 3, so both features occur for two qutrits. arXiv:1905.05462 (§III) had reported this coincidence only for 2 ⊗ 3.

**Effect on the paper.** The negative statement about time-invariant entanglement for two qutrits does not hold. The observations on ρ_{α,β}, on the random pure states and on freezing are unaffected.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The published journal text was not read; the quotations are from arXiv v1. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
