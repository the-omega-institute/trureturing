---
slug: wolk-guhne-2016-balanced-cut-gradient-bound-refutation
bibkey: wolk2016entanglementwidth
doi: 10.1088/1367-2630/aa5015
url: https://arxiv.org/abs/1507.07226v2
triage: theorem
motivation_gids:
  - D5/S3/QuantumBounds/WidthGradientBalancedCutRefutation.result
---

# The balanced-cut gradient bound of Wölk and Gühne fails for eight qubits

## Problem

S. Wölk and O. Gühne, *Characterizing the width of entanglement*, arXiv:1507.07226v2, New J. Phys. 18 (2016) 123024, Appendix D. The conjecture states that every state of N spins with entanglement only within the subgroups {1, …, N/2} and {N/2+1, …, N} satisfies

> $\langle B^2 \rangle \leq \langle B^2\rangle_- + \frac{\langle B\rangle_\textrm {cl}-\langle B^2\rangle_-}{2N}\,\langle J^2\rangle$

with ⟨B²⟩₋ = 6N. The gradient operator and the reference values are quoted in [the literature note](../Library/QuantumContext/wolk2016entanglementwidth.md). The printed numerator has ⟨B⟩_cl; the preceding sentence and the endpoint values fix it as ⟨B²⟩_cl.

Issue [#19442](https://github.com/the-omega-institute/trureturing/issues/19442) fixes the reading:
- for every even N = 2m ≥ 4 and every density matrix that is separable across the two halves;
- the coefficient of ⟨J²⟩ is (⟨B²⟩_cl − 6N)/(2N).

The conjecture is refuted.

## Motivation

A violation of the bound would certify entanglement across the middle of the chain from two collective measurements: the total spin and a spin component in a magnetic gradient. For N = 4 the source proves the bound by semidefinite programming, and for larger N it supports the conjecture by "first tests with random states".

## Gap

The literature check before any Lean is recorded in #19442:
- arXiv v2 retains the conjecture;
- OpenAlex lists 5 citing works. The search seat checked their full texts, except one subscription paper read only by abstract, and found no proof, refutation or correction;
- Zenodo and the repository had no record.

`not-found-in-searched-scope`.

## Route

Take N = 8. In each half, place singlets on the half-sites (1,4) and (2,3), so the state is Φ = χ ⊗ χ.
1. **Separability.** Φ is a product across the cut, so ρ = |Φ⟩⟨Φ| is separable.
2. **Total spin.** Each singlet has total spin 0, so ⟨J²⟩ = 0.
3. **Gradient.** A singlet on sites k, k′ contributes 3(a_k − a_{k′})² to ⟨B²⟩, with a = (−7, −5, −3, −1, 1, 3, 5, 7). The four pairs contribute 108 + 12 + 108 + 12 = 240.
4. **Bound.** At ⟨J²⟩ = 0 the bound is 6N = 48 < 240.

## Falsifier

The refutation would fail if the module's operators or state class differed from the source's. The module:
- uses the source's weights 2k − N − 1 and the Pauli normalization of J and B;
- represents the two halves as the two tensor factors, with sites 1, …, N/2 on the first factor;
- takes "entanglement only within the subgroups" as separability across this factorization, the frozen `IsSeparable`.

The witness has ⟨J²⟩ = 0, so the refutation does not depend on the coefficient of ⟨J²⟩ and holds for the printed numerator as well.

## Evidence

The canonical source is `D5/S3/QuantumBounds/WidthGradientBalancedCutRefutation.lean` (238 lines).
- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Registration.** The refutation `result` is exempt from §3.9 registration, and the module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/QuantumBounds/WidthGradientBalancedCutRefutation.lean.json`, statement `sha256:971cf5797a738cb444d42cda5a31c61720ca1df3bbd82d68b20f5741a57acbab`.

Declaration statements:
- `result`: `sha256:9f2f5b05f402f7bff631b21aa01d6d34c690925c0c3d3cb1ee947d92bb9bc7b6`;
- `claim`: `sha256:3c5be36ab2b2a0e5de7e4542e03d10016e5a9aab60e5e6130049279ccf73bf58`.

## Triage

Tier 1 conjecture of a 2016 paper, preregistered in issue #19442 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. `utility: kind=certified-instance; basis=refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for N = 8 the bound fails at ⟨J²⟩ = 0, where a state separable across the cut has ⟨B²⟩ = 240 against the bound 48.

**Computed, not formalized** (orchestrator, numpy with the full 256-dimensional operators, recorded in #19442):
- ⟨J²⟩ = 0 and ⟨B²⟩ = 240 for the witness, and ⟨B²⟩ = 48 for the adjacent-singlet state Ψ⁻;
- the search seat's mixed witness violates the bound in the interior, with ⟨J²⟩ = 17/2, ⟨B²⟩ = 790.75 and bound 745.
- Over product states, numerical maximization of ⟨B²⟩ minus the bound reaches about 298 at N = 8, at ⟨J²⟩ ≈ 8.1.

**Argued, not formalized.**
- *Mechanism.* For a product of singlets, ⟨B²⟩ is the sum of 3(a_k − a_{k′})² over the pairs. Adjacent pairing minimizes this sum, while the conjecture names the adjacent-singlet state as the maximizer at ⟨J²⟩ = 0. Within a half of four or more sites, pairing distant spins is still separable across the cut and gives more. For N = 4 each half has only the adjacent pairing, which is why the case N = 4 holds.
- *Repair.* A correct bound at ⟨J²⟩ = 0 must be at least the largest within-half singlet pairing sum, which for N = 8 is at least 240.
- *Effect on N = 6.* For N = 6 the source's Ψ⁻ pairs sites 3 and 4 across the cut, so it is not in the state class of the conjecture there.

**Effect on the paper.** The Appendix D conjecture fails for N = 8, already at zero total spin. The source's proved bound for N = 4 and its nearest-neighbor bounds are unaffected.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The published journal text was not read; the quotations are from arXiv v2. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
