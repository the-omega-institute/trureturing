---
slug: toth-pitrik-2026-separable-wasserstein-comparison-refutation
bibkey: toth2026wassersteinfidelities
doi: null
url: https://arxiv.org/abs/2506.14523v6
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/SeparableWassersteinComparisonRefutation.result
---

# The separable modified Wasserstein distance can exceed the De Palma–Trevisan one

## Problem

G. Tóth and J. Pitrik, *Quantum Wasserstein distance and its relation to several types of fidelities*, arXiv:2506.14523v6, Conjecture 1:

> {\bf Conjecture 1.} The following inequality seems to hold $\tilde D_{\rm DPT, sep}(\varrho,\sigma)^2 \le \tilde D_{\rm DPT}(\varrho,\sigma)^2$ if $\varrho$ and $\sigma$ are arbitrary mixed states.

The two squared distances and their modified forms are quoted in [the literature note](../Library/QuantumContext/toth2026wassersteinfidelities.md).

Issue [#19312](https://github.com/the-omega-institute/trureturing/issues/19312) fixes the reading: the inequality for every d, every family of Hermitian observables and all density matrices ρ, σ. It is refuted.

## Motivation

The source proves the inequality when one state is pure and tests 1000 random pairs. If it held, the separable distance could stand in for the De Palma–Trevisan distance in bounds on the modified quantity.

## Gap

The literature check before any Lean is recorded in #19312:
- arXiv v6 is the latest version;
- OpenAlex finds no record;
- the repository had no record of the conjecture.

`not-found-in-searched-scope`.

## Route

The instance is d = 4, N = 3, with ρ = diag(3,3,1,1)/8 and σ = diag(1,1,3,3)/8. The observables are H_1 = [[0,2,0,0],[2,0,0,0],[0,0,0,1],[0,0,1,0]], H_2 = diag(1,−1,2,−2) and H_3 = T/4, where T exchanges the two coordinate blocks.
1. **Separable cross term.** A decomposable witness C_0 − 1 − 2E = A_0 + B_0^Γ, with A_0, B_0 positive and E the block-mixing projector, shows that every separable cross coupling has cost at least 2.
2. **Separable self terms.** Explicit separable self-couplings have cost 17/16.
3. **Quantum terms.** An explicit quantum cross coupling has cost 9/16, and the quantum self terms are nonnegative because the cost operator is positive.

So the modified separable distance is at least 15/16, while the modified De Palma–Trevisan distance is at most 9/16.

## Falsifier

The refutation would fail if the module's distances differed from the source's. The module:
- takes the quantum couplings with marginals ρᵀ and σ and the cost (H_nᵀ ⊗ 1 − 1 ⊗ H_n)², as in the source;
- takes the separable couplings with marginals ρ and σ and the cost (H_n ⊗ 1 − 1 ⊗ H_n)²;
- defines both squared distances as infima, and subtracts the averaged self-distances.

## Evidence

The canonical source is `D5/S3/Quantum/Information/SeparableWassersteinComparisonRefutation.lean` (421 lines).
- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Registration.** The refutation `result` is exempt from §3.9 registration, and the module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Information/SeparableWassersteinComparisonRefutation.lean.json`, statement `sha256:bac42512d4bda6ab82501dea19f6c35e9eed2109394b10e173919afc4e32df8a`.

Declaration statements:
- `result`: `sha256:48a7546eb0210403a0f2bbb510d953c8b12d506720de267d9901beb48a7e5ef0`;
- `claim`: `sha256:ecb52764fa1b5a7f47f83251c2633b287a99536c1961143a8d0dbae408b36187`.

## Triage

Tier 1 conjecture of a 2026 paper, preregistered in issue #19312 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. `utility: kind=certified-instance; basis=refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** Conjecture 1 fails for the instance above.

**Computed, not formalized** (orchestrator, recorded in #19312):
- the SDP values are 0.530 for the quantum cross term and 0.008 for each quantum self term;
- the PPT relaxation gives 2.061 for the separable cross term.

**Argued, not formalized.**
- *Mechanism.* The two states live mostly on complementary blocks. Quantum couplings can move mass coherently between the blocks through Bell-like sector states, at low cost. Separable couplings cannot do this, so the decomposable witness forces a cost of at least 2. The separable self-distances stay near 1 because the observables do not share eigenbases.
- *Scope.* The source's pure-state theorem is unaffected; the failure needs both states mixed.

**Effect on the paper.** Conjecture 1 does not hold for arbitrary mixed states.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
