---
slug: zozor-bosyk-portesi-2014-qutrit-overlap-bound-non-optimality
bibkey: zozor2014entropylikeuncertainty
doi: 10.1088/1751-8113/47/49/495302
url: https://arxiv.org/abs/1311.5602v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/QutritOverlapBoundNonOptimality.result
---

# The overlap entropy bound is not c-optimal for qutrits

## Problem

S. Zozor, G. M. Bosyk and M. Portesi, *General entropy-like uncertainty relations in finite dimensions*, arXiv:1311.5602v3, J. Phys. A 47 (2014) 495302, Section 3, after Corollary 2:

> We suspect that  this corollary is also  valid when $N=3$, but we  have not been
> able to prove it yet.

Corollary 2 states that for c > 1/√2 and N = 2 or N ≥ 4 the bound (22), B(c) = min over θ ∈ [0, arccos c] of D(θ) + D(arccos c − θ), is c-optimal. That is, it equals the minimum of the entropy sum over all states and all unitary T ∈ U(N) with c(T) = max |T_ij| = c. The entropies, the overlap and the function D are quoted in [the literature note](../Library/QuantumContext/zozor2014entropylikeuncertainty.md).

Issue [#19610](https://github.com/the-omega-institute/trureturing/issues/19610) fixes the reading for the Tsallis pair of order 2, S₂(p) = 1 − Σ p_i², an admissible pair of the corollary. The suspicion then says that, for every c with 1/√2 < c ≤ 1, some T ∈ U(3) with c(T) = c and some state attain B(c). The suspicion is refuted.

## Motivation

The bound depends only on the overlap c, so its c-optimality decides whether the overlap alone can determine the best entropic uncertainty relation. The source proves it for qubits and, by embedding an optimal qubit pair into a block-diagonal unitary, for every N ≥ 4. In dimension three the complementary block is one-dimensional, its entry has modulus one, and the embedding violates c(T) = c.

## Gap

The literature check before any Lean is recorded in #19610:
- arXiv v1–v3 all keep the suspicion;
- the search seat reports reading 61 citation records and the full texts of the relevant follow-ups, with no settlement of N = 3. A web search by the orchestrator found no settlement either;
- the repository had no record.

`not-found-in-searched-scope`.

## Route

Fix 1/√2 < c < 1 and γ = arccos c, so 0 < γ < π/4.
1. **The bound.** On [0, γ] the floor term equals 1 and D(θ) = ½ sin²2θ. The minimum of D(θ) + D(γ − θ) is 1 − c², attained only at θ = γ/2.
2. **Mixed to pure.** S₂ is concave and the probabilities are linear in ρ, so a mixed state is no better than the best pure state in its spectral decomposition.
3. **Small maxima.** If max p ≤ ½ then S₂(p) ≥ ½ > 1 − c², and likewise for q.
4. **Overlap inequality.** With P = max_i p_i and Q = max_j q_j, Cauchy–Schwarz on the components orthogonal to ψ gives c ≥ |⟨a, b⟩| ≥ √(PQ) − √((1 − P)(1 − Q)) for the maximizing basis vectors a and b. Hence S₂(p) + S₂(q) ≥ 2P(1 − P) + 2Q(1 − Q) ≥ 1 − c².
5. **Equality rigidity.** Equality forces ψ into the span of two A-basis vectors and into the span of two B-basis vectors, and the Cauchy–Schwarz equality makes both planes equal to span(ψ, a). In ℂ³ the remaining A- and B-basis vectors are then both orthogonal to this plane, so their overlap has modulus 1 > c, a contradiction.

So S₂(p) + S₂(q) > 1 − c² = B(c) for every state and every T ∈ U(3) with all |T_ij| ≤ c.

## Falsifier

The refutation would not answer the suspicion if the module's bound, entropies or admissible matrices differed from the source's. The module:
- uses the Tsallis pair λ_A = λ_B = 2, given by h(x) = 1 − x and φ(x) = x² in the source's (h, φ) family, through the frozen linear entropy `threeModeMixing`;
- takes D with the source's floor term and the bound (22) as an infimum over [0, arccos c];
- quantifies over all T ∈ U(3) with all entries of modulus at most c and one of modulus c, and over all density matrices.

The module's q_j = (T ρ T*)_jj uses the transpose of the source's T_ij = ⟨b_j|a_i⟩. Transposition preserves unitarity and c(T).

## Evidence

The canonical source is `D5/S3/Quantum/Information/QutritOverlapBoundNonOptimality.lean` (557 lines).
- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Information/QutritOverlapBoundNonOptimality.lean.json`, statement `sha256:fbe03503b5bae6aec08ca44cc64e86508b1a37fa4800dd8ba4afee2aadb90262`.

Declaration statements:
- `result`: `sha256:6203ed4462e3e4c43949c8bdc59045527c478018c1a62f71a0748ccf7057c7b7`;
- `claim`: `sha256:67a5d8b609b5af26ff13ae8f3c1674e113d8bcb1baf0ee6fee088c752eb0f9db`.

## Triage

Tier 1 question of a 2014 paper, preregistered in issue #19610 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. `utility: kind=certified-instance; basis=refutes`. There is no digestion atom.

### What the settlement shows

**Proved in the module:** the private `strict_overlap_bound`, with `overlapBound_eq`, shows that for every c with 1/√2 < c < 1 no T ∈ U(3) with all |T_ij| ≤ c and no density matrix attain the bound 1 − c². `result` derives ¬ claim from it at c = 3/4, with bound 7/16.

**Computed, not formalized** (orchestrator, scipy, recorded in #19610): at c = 3/4 the smallest value found over 150 starts is 0.443040, above 7/16 = 0.4375.

**Argued, not formalized.**
- *Mechanism.* Equality in the qubit-type bound needs a two-dimensional block shared by both bases. In dimension three the complement of that block is one line, so the remaining basis vectors coincide up to phase and c(T) = 1. The qubit optimum cannot be embedded, and no other configuration reaches it.
- *Scope.* The argument uses only the Tsallis-2 entropy and the strict monotonicity of D on [0, π/4]. It is expected to carry over to other pairs whose D is strictly increasing there, but this is not proved here.
- *Endpoint.* At c = 1 the bound is 0 and is attained by T = I and a basis state, so the suspicion holds at c = 1.

**Effect on the paper.** Corollary 2 cannot be extended to N = 3 for every admissible pair of entropies. The exact c-optimal bound for qutrits remains open; at c = 3/4 the smallest value found, 0.443040, lies above B(3/4) = 7/16.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The published journal text was not read; the quotations are from arXiv v3. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
