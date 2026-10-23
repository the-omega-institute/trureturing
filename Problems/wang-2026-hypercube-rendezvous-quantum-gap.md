---
slug: wang-2026-hypercube-rendezvous-quantum-gap
bibkey: wang2026rendezvous
doi: null
url: https://arxiv.org/abs/2610.12949v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/HypercubeRendezvousQuantumGap.result
  - D5/S3/Quantum/Entanglement/RendezvousVectorSystemGap.vector_system_gap
---

# The quantum value of balanced hypercube rendezvous is strictly below its no-signalling value

## Problem

C. Wang, *Quantum-assisted rendezvous on hypercubes: a quantum Bernoulli noise approach*, arXiv:2610.12949v1 (9 October 2026), studies one-step rendezvous on the hypercube {0,1}^d.
- Inputs: Alice and Bob receive vertices σ, τ with |σ △ τ| = 2t, uniformly.
- Outputs: each moves t coordinates, Alice A and Bob B, both t-subsets.
- Winning: they meet, σ △ A = τ △ B, that is A ∩ B = ∅ and A ∪ B = σ △ τ.

Lemma 5.1 gives the no-signalling value ω_NS(d,t) = C(2t,t)/C(d,t). Theorems 5.5 and 6.4 show that for t ≥ 2 and d > 2t no finite-dimensional quantum strategy attains it. §7 asks: "It remains open whether ω_Q(d,t) is then strictly below ω_NS(d,t)", where ω_Q is the supremum over finite-dimensional quantum strategies (Eq. (2.8)). The verbatim statements are in [the literature note](../Library/QuantumBounds/wang2026rendezvous.md).

Issue [#15814](https://github.com/the-omega-institute/trureturing/issues/15814) fixes the reading:
- arbitrary finite-dimensional systems, density matrices and POVMs;
- no-signalling correlations with input-independent marginals;
- both values as suprema;
- the claim ω_Q(d,t) < ω_NS(d,t) for all t ≥ 2 and d > 2t.

## Motivation

Non-attainment by every finite-dimensional strategy does not separate the supremum from the no-signalling value: quantum correlations could approach the no-signalling optimum as the dimension grows. A strict separation needs a bound uniform in the dimension.

## Gap

Issue #15814 records the literature check before any Lean:
- arXiv lists only v1;
- web search on the title and on the question's terms finds only the source;
- related work on quantum rendezvous (arXiv:2311.11817, 2405.14951, 2207.14404) does not state or imply such a bound;
- Ramanathan et al., PRL 117 (2016), concerns exact realisation of single extremal no-signalling boxes, while the optimal face here is not a single vertex;
- Araiza–Junge–Palazuelos (arXiv:2606.21664) bounds the no-signalling–quantum gap from above, not from below;
- Zenodo and Crossref have no matching record;
- the repository had no rendezvous or nonlocal-game value result.

`not-found-in-searched-scope`.

## Route

Write n = C(d,t) and c = C(2t,t).

1. **Vectors.** On operators of the joint system the form ⟨X, Y⟩ = Re Tr(X* Y ρ) is positive semidefinite. With h = I, u_{σ,A} = E_{σ,A} ⊗ I and v_{τ,B} = I ⊗ F_{τ,B}, the joint probabilities are the cross products ⟨u, v⟩. Since 0 ≤ E_S ≤ I gives E_S² ≤ E_S, every set S of outcomes satisfies ‖Σ_S u‖² ≤ ⟨h, Σ_S u⟩. No dilation is needed.
2. **Symmetrisation.** Average over coordinate permutations and translations, as a weighted form on functions from the symmetry group. The averaged system has ⟨h, u⟩ = ⟨h, v⟩ = 1/n, and every winning branch has probability ω/c, with ω the strategy's value.
3. **Gap.** Put δ = 1 − nω/c.
   - On a winning branch u and v are within √(2δ/n).
   - Chains of one-element exchanges move every outcome vector within 2t√(2δ/n) of a vector attached to its meeting vertex.
   - The n t-subsets and one (t−2)-subset are n + 1 meeting vertices; any two of them share a measurement with distinct outcomes. So their vectors are almost orthogonal while each has overlap 1/n with h.
   - Cauchy–Schwarz gives 1 ≤ n²(4t√(2δ) + 2δ), hence δ ≥ κ = 1/(n⁴(4√2·t + 2)²).
4. **Values.** Every finite-dimensional strategy has value at most (c/n)(1 − κ). The no-signalling correlation P(A,B|σ,τ) = 1/n for B = π_{σ△τ}(A) attains c/n; here π_η(A) = η \ A if A ⊆ η and |η| = 2t, and A otherwise.

## Falsifier

The proof would fail if some winning branch or measurement had no symmetric partner, which is why it needs d > 2t: one-exchange pairs must have a common disjoint output, and the (t−2)-subset must exist, which needs t ≥ 2. The brute-force check in #15814 confirms every combinatorial fact for (d,t) ∈ {(5,2), (6,2), (7,2), (7,3), (8,3), (9,3)}.

## Evidence

Two canonical sources.
- `D5/S3/Quantum/Entanglement/RendezvousVectorSystemGap.lean` (321 lines):
  - the vertices `Vertex`, the outputs `Output`, the winning relation `Wins`, the constants `n` and `kappa`;
  - the public theorem `vector_system_gap`, stated for any real space with a positive semidefinite form (`PreInnerProductSpace.Core`).
- `D5/S3/Quantum/Entanglement/HypercubeRendezvousQuantumGap.lean` (882 lines):
  - the definitions `Correlation`, `Promised`, `Inputs`, `value`, `QStrategy`, `QStrategy.prob`, `IsQuantum`, `IsNS`, `QValues`, `NSValues`, `omegaQ`, `omegaNS`;
  - `claim` and `result`.
- The settlement module reuses `RHLinalg.trace_mul_nonneg_of_posSemidef` and Mathlib's Kronecker products, PSD order, `Equiv.Perm.exists_map_finset_eq`, `Finset.exists_equiv_extend_of_card_eq`, `map_sum` and `csSup_le`/`le_csSup`.
- Both modules use only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen states:
- `Golden/Frozen/state/D5/S3/Quantum/Entanglement/RendezvousVectorSystemGap.lean.json`, statement `sha256:363d6bb4d43b549e192042372ae2d0da9ae4c4b3bfdb305d3a1e00427666d401`;
- `Golden/Frozen/state/D5/S3/Quantum/Entanglement/HypercubeRendezvousQuantumGap.lean.json`, statement `sha256:cbfe3c9c42a52ec2dec63f3f6fcebb988668bbad8fff374d68f95b13b225ac6c`.

Declaration statements:
- `vector_system_gap`: `sha256:625f62874ade22674548daf074d78207c19bfbe06ca9ccf2089342d829515bad`;
- `result`: `sha256:2e21b3e22aab0ea34a2c734251179eeb435ba38d1898ca08a9d42a323029ada6`;
- `claim`: `sha256:d1ebaef86c302773682c05a4a030b11cb4678021247e4850a198db2562e2b025`.

## Triage

Tier 1 closing question of a 2026 paper, preregistered in issue #15814 before any Lean.
`theorem`; resolution `proved`.

| module | declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- | --- |
| `RendezvousVectorSystemGap` | `vector_system_gap` | content | the exchange transport, the common-sphere vertex construction and the enlarged-family Gram estimate, all on its live proof path | escape-witness |
| `HypercubeRendezvousQuantumGap` | `result` | content | none claimed | open-problem-resolution |

Every other declaration is a definition used by a public statement, or a private helper on the proof path of its module's public theorem (CLAUDE.md §3.2 「有消费的辅助声明」). The settlement module also owns the generated declarations of the structure `QStrategy`. Utility is `none` for both modules: they prove universal bounds, not computational instances. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for all t ≥ 2 and d > 2t, ω_Q(d,t) < ω_NS(d,t).

**Proved by `vector_system_gap`:** a dimension-free gap for symmetric vector systems. In any real space with a positive semidefinite form, a system satisfying the scaled identities of the averaged strategy has δ ≥ κ(d,t).

**Established inside the proof.**
- Every finite-dimensional quantum strategy has value at most (c/n)(1 − κ(d,t)), with κ(d,t) = 1/(C(d,t)⁴(4√2·t + 2)²), uniformly in the local dimensions.
- c/n is attained by a no-signalling correlation.

**Argued, not formalized.** The bound is far from tight: κ decays like C(d,t)⁻⁴. The argument uses only a Gram matrix of measurement vectors. A correlation in the first level of the NPA hierarchy supplies such vectors, with exact orthogonality, which is stronger than the sub-orthogonality used here. After the same symmetrisation, the bound (c/n)(1 − κ) therefore holds for every first-level correlation. The paper's second question, whether quantum strategies still outperform classical ones for t ≥ 2, is not addressed.

**Open.** The exact value of ω_Q(d,t) for t ≥ 2, and whether it exceeds the classical value.

**Effect on the paper.** The first question of §7 is answered: the quantum value is strictly below the no-signalling value for t ≥ 2 and d > 2t, by an explicit dimension-free margin.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The NPA-level remark in "Argued, not formalized" is not formalized.
