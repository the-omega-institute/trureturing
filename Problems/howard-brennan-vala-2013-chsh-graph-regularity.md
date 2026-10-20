---
slug: howard-brennan-vala-2013-chsh-graph-regularity
bibkey: howard2013stabilizercontextuality
doi: 10.3390/e15062340
url: https://arxiv.org/abs/1501.04342v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Contextuality/StabilizerCHSHGraphRegularity.result
---

# The qudit CHSH orthogonality graph is (2d − 1)(d − 1)-regular for every prime d

## Problem

M. Howard, E. Brennan and J. Vala, *Quantum Contextuality with Stabilizer States*, Entropy 15 (2013) 2340–2362, arXiv:1501.04342v1, Section 5:

> Observe that for all $d \in \{2,3,5,7\}$ that we have discussed, we see some structure in the graphs $\Gamma_{\textrm{CHSH}}$ obtained from qudit CHSH inequalities. Whereas it is quite easy to see that all graphs will have order $|\Gamma_{\textrm{CHSH}}|=d^3$, we conjecture based on the examples here that $\Gamma_{\textrm{CHSH}}$ is a $(2d-1)(d-1)$-regular graph.

The operators A_j and B_k, the spectral projectors and their rank-one decomposition, and the graph convention are quoted in [the literature note](../Library/QuantumContext/howard2013stabilizercontextuality.md).

Issue [#19492](https://github.com/the-omega-institute/trureturing/issues/19492) fixes the reading:
- the vertices are the d³ rank-one projectors Π^A_j[a] ⊗ Π^B_k[−jk − a] of the decomposition of the CHSH Bell operator;
- two vertices are adjacent when the product of their projectors vanishes.

The conjecture is proved.

## Motivation

The graph turns the qudit CHSH inequality into a noncontextuality inequality for stabilizer projectors. Its independence number gives the classical bound, and its Lovász number bounds the quantum value. Regularity is the first structural property of the family; the source checks it only for d ≤ 7.

## Gap

The literature check before any Lean is recorded in #19492:
- the arXiv record has only v1;
- OpenAlex lists 26 citing works. The orchestrator checked arXiv:1512.05048, 1501.05319 and 1411.7704, which do not treat the regularity of Γ_CHSH;
- the repository had no record.

`not-found-in-searched-scope`.

## Route

1. **Eigenvectors.** For odd p the Weyl operators A_j and B_k have chirp eigenvectors u(x) = ω^{c x + j·2⁻¹·x(x−1)}/√p, and each spectral projector is |u⟩⟨u|. For p = 2 the eigenvectors of X and Y are explicit.
2. **Overlaps.** Within one basis distinct eigenvectors are orthogonal. Across different bases the squared overlap is 1/p, by the quadratic character-sum identity |Σ_x ω^{Q(x)}|² = p for quadratic Q with nonzero leading coefficient.
3. **Adjacency.** A Kronecker product of rank-one projectors vanishes iff one factor does. So (j,k,a) and (j′,k′,a′) are adjacent iff (j = j′ and a ≠ a′) or (k = k′ and b ≠ b′), where b = −jk − a.
4. **Count.** The two sets have p(p − 1) elements each and intersect in p − 1 elements. So every vertex has (2p − 1)(p − 1) neighbours.
5. **Distinct vertices.** Tr(P(v)P(w)) is the product of the two squared overlaps. It equals 1 only for v = w, so the p³ projectors are distinct.

## Falsifier

The proof would not settle the conjecture if the module's vertex set differed from the source's. The module:
- uses the source's operators: X and Y for d = 2, and A_j = ω^{j(j+1)}XZ^j, B_k = ω^{(2⁻¹)²(k²+2k)}XZ^{2⁻¹k} for odd d;
- uses the normalized spectral projectors of Eq. (Qproj);
- selects for each (j,k) the outcome −jk of A_j ⊗ B_k. The (j,k) term Σ_{n≠0} ω^{njk}(A_j ⊗ B_k)^n of the Bell operator equals p·Π[−jk] − I;
- splits Π[−jk] into rank-one terms by Eq. (SumRank1).

## Evidence

The canonical source is `D5/S3/Quantum/Contextuality/StabilizerCHSHGraphRegularity.lean` (742 lines).
- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Registration.** The §3.9 registration is `Reg/D5/S3/Quantum/Contextuality/StabilizerCHSHGraphRegularity.lean`.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Contextuality/StabilizerCHSHGraphRegularity.lean.json`, statement `sha256:4026e12e64dab621ed497ad74014446d470b4c4b228299b0ae43ebb452d4e53e`.

Declaration statements:
- `result`: `sha256:630686833ad540b45939ef2245fbd5c3c11502df7a852c77b6fd52ddc968842d`;
- `claim`: `sha256:6b5f7992230aea31b282255907e31aaca2a3b862e5acc4f1bf90f061a0c39c8b`.

## Triage

Tier 1 conjecture of a 2013 paper, preregistered in issue #19492 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. `utility: none`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every prime p the p³ vertex projectors are distinct rank-one projectors, and every vertex is orthogonal to exactly (2p − 1)(p − 1) others.

**Computed, not formalized** (orchestrator, numpy, recorded in #19492): for p ∈ {2, 3, 5, 7}, the Bell-operator decomposition holds and the degrees are 3, 10, 36, 78, as in the source.

**Argued, not formalized.**
- *Mechanism.* Alice's p bases and Bob's p bases are each a set of mutually unbiased bases, since all p bases of the Weyl operators X Z^j are pairwise unbiased. Orthogonality therefore only happens inside one basis, so adjacency is a union of two "same basis, different outcome" relations, one per party. The CHSH selection rule b = −jk − a pairs Alice's and Bob's outcomes bijectively for each (j,k), and this bijection makes the intersection of the two relations as small as p − 1.
- *Structure.* For fixed j, Alice's relation makes the p² vertices (j, k, a) a complete p-partite graph, with parts indexed by a. Bob's relation does the same for fixed k, with parts indexed by b. Γ_CHSH is the edge union of these 2p multipartite graphs.
- *Scope.* The argument uses only mutual unbiasedness of the local bases and the bijective selection rule. Any choice of the phases in A_j, B_k that keeps these two properties gives a (2p − 1)(p − 1)-regular graph.

**Effect on the paper.** The regularity conjecture holds for every prime dimension. The remaining parameters of Table 5 (independence number, Lovász number, largest eigenvalue) are not addressed.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The published journal text was not read; the quotations are from arXiv v1. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
