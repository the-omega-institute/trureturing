---
slug: kotowski-kotowski-2026-one-qubit-simulation-refutation
bibkey: kotowski2026smallancilla
doi: null
url: https://arxiv.org/abs/2606.08784v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/OneQubitAdaptiveSimulationRefutation.result
---

# One ancilla qubit and bounded rounds cannot simulate every channel with constant success

## Problem

M. Kotowski and M. Kotowski, *Randomized simulation of quantum channels using small ancilla*, arXiv:2606.08784v1, Question 6.1:

> Consider the model of simulation with postselection that allows: 1) unitary operations with ancilla; 2) classical randomization; 3) projective measurements; 4) adaptive unitary operations based on measurement results. Can \textit{every} channel $\Phi$ be simulated in this way with success probability $\Omega(1)$ using one additional qubit and $O(1)$ rounds?

The verbatim passages are in [the literature note](../Library/QuantumContext/kotowski2026smallancilla.md).

Issue [#19196](https://github.com/the-omega-institute/trureturing/issues/19196) fixes the reading: universal constants R₀ and q₀ > 0 such that every channel on M_d(ℂ), for every d, has a randomized adaptive protocol on ℂ^d ⊗ ℂ² with at most R₀ projective-measurement stages and success map qΦ with q ≥ q₀. The answer is no.

## Motivation

The paper shows that one ancilla qubit suffices for success probability Ω(1/log d) on unital channels and Ω(1) on broad classes of channels. The question asks whether adaptivity with constant depth removes the dimension dependence for all channels.

## Gap

The literature check before any Lean is recorded in #19196:
- arXiv v1 is the only version;
- OpenAlex finds no record;
- the repository had no record of the paper.

`not-found-in-searched-scope`.

## Route

For n ≥ 2, put m = n² and d = m + 2^m. Index the coordinates by m basis labels and by all sign strings, and let A have rows e_j and s/n. Take Φ_n(X) = Σ_k D_k X D_k with D_k = diag(A_{·,k}), a unital channel.
1. Exact simulation forces every successful Kraus operator to be diag(Av).
2. A nonzero diag(Av) has rank at least 2^{m−1} + 1, which is more than 2d/5. So each projective measurement on ℂ^d ⊗ ℂ² has at most four outcomes with successful descendants, and a seed has at most 2·4^R successful Kraus operators.
3. Each such operator is a contraction, so Σ_j |v_j|² ≤ 2n. Evaluating the simulation on the basis projectors then gives q·n² ≤ 4n·4^R, that is q ≤ 4·4^R/n.
4. Choosing n large defeats every pair (R₀, q₀).

## Falsifier

The refutation would fail if the formal model were narrower than the question's. The model:
- uses protocol trees, where each node applies a unitary on ℂ^d ⊗ ℂ² and then a projective measurement with any finite number of outcomes, with outcome-dependent children, and leaves record success;
- randomizes by finite mixtures of trees, which absorbs mid-protocol randomness;
- takes the Kraus operators of the success map as the branch products compressed between a fixed initial ancilla vector and an orthonormal final ancilla basis.

A final unitary after the last measurement costs one trivial measurement stage, which a universal R₀ absorbs.

## Evidence

The canonical source is `D5/S3/Quantum/QuantumChannels/OneQubitAdaptiveSimulationRefutation.lean` (708 lines).
- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Registration.** The refutation `result` is exempt from §3.9 registration, and the module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/QuantumChannels/OneQubitAdaptiveSimulationRefutation.lean.json`, statement `sha256:562797c114bf7e1c6bf58755f283cc534b847f8bab9d0b68895276b42902a166`.

Declaration statements:
- `result`: `sha256:ecb6420dd4c92f483af3d4017cd9c7677b13ad4d552037ad8bd220d3c531e906`;
- `claim`: `sha256:8c741c57b94afb574aa272024aeb017d13d500ab5932a535949821e30286437f`.

## Triage

Tier 1 open question of a 2026 paper, preregistered in issue #19196 before any Lean.
`theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none | open-problem-resolution |
| definitions | bind-only | none | definitions used by `claim` |

The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. `utility: kind=certified-instance; basis=refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every round budget R and every success probability q₀ > 0, some unital channel cannot be simulated in the model with at most R stages and success at least q₀.

**Argued, not formalized.**
- *Mechanism.* A channel whose Kraus operators are forced to have very large rank cannot be split across few measurement outcomes. With one qubit of ancilla, each measurement has at most four high-rank outcomes, which caps the number of successful Kraus operators at 2·4^R. The contraction budget then caps the success probability.
- *Scope.* The bound does not contradict the paper's Ω(1/log d) theorem for unital channels, which uses more rounds: here d grows like 2^{n²}, so 1/log d is of order 1/n². Whether Ω(1) success is possible with O(log d) rounds, or for other classes of channels, is not addressed.

**Effect on the paper.** The answer to Question 6.1 is negative.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Argued, not formalized" are not formalized.
