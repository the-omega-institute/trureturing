---
slug: baio-chruscinski-horodecki-messina-sarbicki-2019-fixed-marginal-negativity-refutation
bibkey: baiochruscinskihorodeckimessinasarbicki2019fixedmarginals
doi: 10.1103/PhysRevA.99.062312
url: https://arxiv.org/abs/1904.07650v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/FixedMarginalNegativityRefutation.result
---

# The quasidistillable candidates are not two-qutrit negativity maximizers for fixed marginals

## Problem

G. Baio, D. Chruściński, P. Horodecki, A. Messina and G. Sarbicki, *Bounds on the entanglement of two-qutrit systems from fixed marginals* (Phys. Rev. A 99, 062312 (2019); arXiv:1904.07650), study the largest entanglement of a bipartite state whose marginals are fixed.
- For two qubits the maximum of the negativity N(ρ) = (‖ρ^Γ‖₁ − 1)/2 is attained by an explicit state (12).
- For two qutrits with ordered marginals ρ_A = diag(1−λ₁−λ₂, λ₁, λ₂) and ρ_B = diag(1−μ₁−μ₂, μ₁, μ₂) (Eq. (24)), they maximize the negativity within the circulant family (22). They obtain three quasidistillable states, Eqs. (27)–(29).
- From numerical optimization they conclude: "all the above results strongly support our conjecture that our quasidistillable states (27, 28, 29) are legitimate candidates for two-qutrits MEMS with respect to fixed marginals".

The verbatim statements are in [the literature note](../Library/QuantumChannels/baiochruscinskihorodeckimessinasarbicki2019fixedmarginals.md).

Issue [#18345](https://github.com/the-omega-institute/trureturing/issues/18345) fixes the reading: in the region of Eq. (27), the state (27) maximizes the negativity over all two-qutrit states with the marginals (24). The conjecture is refuted.

## Motivation

A state maximizing entanglement for given marginals gives an upper bound on the entanglement that local measurements alone allow. The two-qubit answer is known, and the conjecture would extend it to two qutrits through an explicit, quasidistillable family.

## Gap

Issue #18345 records the literature check before any Lean:
- arXiv v1 and v2 retain the conjecture;
- the works citing the source cite it for the problem or for two-qubit states;
- the repository had no record of the paper.

`not-found-in-searched-scope`.

## Route

Take λ = (47, 4)/100 and μ = (5, 1)/100, inside the region of Eq. (27): ρ_A = diag(49, 47, 4)/100 and ρ_B = diag(94, 5, 1)/100.
1. **The witness.** With χ = (7|00⟩ + |12⟩ + 2|21⟩)/10, let ρ₀ = χχ† + (45/100)|10⟩⟨10| + (1/100)|11⟩⟨11| and ρ = (99/100)ρ₀ + (1/100)ρ_A ⊗ ρ_B. Then ρ is a density matrix with marginals ρ_A and ρ_B.
2. **Its negativity.** K = O(|01⟩ − |20⟩)/2 + O(7|02⟩ − |10⟩)/50 + O(|11⟩ − |22⟩)/2 is a projector, so W = 1 − 2K is unitary. Then ‖ρ^Γ‖₁ ≥ Re Tr(Wρ^Γ) = 1 + 2 · 8168881/50000000, and N(ρ) ≥ 8168881/50000000 > 7/50.
3. **The candidate.** The state (27) is σ = φφ† + (42/100)|10⟩⟨10| + (3/100)|20⟩⟨20| with φ = (7|00⟩ + √5|11⟩ + |22⟩)/10.
   - Its partial transpose is P − Q with P, Q positive semidefinite, so ‖σ^Γ‖₁ ≤ Tr P + Tr Q.
   - Hence N(σ) ≤ Tr Q = 100159/923000 + √5/100 < 7/50.

## Falsifier

The refutation would not settle the conjecture if:
- the module's negativity differed from Eq. (4);
- its marginals or candidate differed from Eqs. (24), (27) and (30);
- "MEMS with respect to fixed marginals" meant something other than a negativity maximizer.

The module takes:
- the negativity with the trace norm of the partial transpose on the second factor;
- the marginals as the diagonal matrices of Eq. (24), with the ordering and the region of Eq. (27) as hypotheses;
- the candidate entrywise as in (30).

The source defines the two-qubit maximal states by maximizing concurrence or negativity, and Section IV compares the negativity of the candidates with numerical maxima of the negativity.

## Evidence

The canonical source is `D5/S3/Quantum/Entanglement/FixedMarginalNegativityRefutation.lean` (352 lines).
- It defines `orderedMarginal` (used for both marginals), `candidate` and `claim`, and proves `result : ¬ claim`.
- It reuses:
  - the negativity (‖R^Γ‖₁ − 1)/2 of `NegativityReductionInclusionRefutation`, with the partial transpose of `KickedIsingNegativityRefutation`;
  - the trace norm and its variational and triangle lemmas from `FiniteTraceDistance`;
  - `IsDensity` from `StructuredNegativityCoincidenceRefutation`;
  - the partial traces of `PartialTraceMutualInformation`.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- The escape registrations: `result` is the designated refutation result of the `utility` header and is exempt. The module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Entanglement/FixedMarginalNegativityRefutation.lean.json`, statement `sha256:6ff9f0753649dd1fabc166057b13a8a28697412539d3e9d93af03ba7b73b0b57`.

Declaration statements:
- `result`: `sha256:7aadee2510d1ebfdafebf17606f8cc843f7b492fcff1a308493af139d5c7c939`;
- `claim`: `sha256:746d198ce7849cdc78994702a51521857bb1e9bdb718659b9589d6c5b41972d6`.

## Triage

Tier 1 conjecture of a 2019 paper, preregistered in issue #18345 before any Lean.
`theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the marginals, the unitary certificate and the PSD decomposition are finite matrix identities, and the comparison is rational arithmetic with √5 | open-problem-resolution |
| the witness and certificate helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every public declaration is bind-only; the definitions are used by public statements. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Refuted by `result`:** at λ = (47, 4)/100 and μ = (5, 1)/100 the state ρ has the marginals of Eq. (24) and negativity above 7/50, while the candidate (27) has negativity below 7/50.

**Computed, not formalized** (orchestrator, recorded in #18345): N(ρ) ≈ 0.16404, N(σ) ≈ 0.13087 and N(ρ₀) ≈ 0.16625; ρ ≥ (1/250000)·1, so the witness has full rank.

**Argued, not formalized.**
- *Mechanism.* The candidates pair the coherences as |00⟩, |11⟩, |22⟩, a maximally correlated vector, and the maximization in Section III runs only over the family (22) built on such vectors. The witness pairs |00⟩ with |12⟩ and |21⟩, a circulant state outside the family (22). At the chosen marginals this pairing carries more negativity, as the two bounds of the route show.
- *Scope.* The separate conjecture of Section III, that all maximizers are quasidistillable, is not addressed. Nor are the branches (28)–(29).

**Effect on the paper.** The family (22) does not contain the negativity maximizers for all ordered two-qutrit marginals. The candidates (27)–(29) are lower bounds on the maximal negativity, not its value.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
