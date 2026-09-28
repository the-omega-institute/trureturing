---
slug: muhlherr-poullot-2026-tripartite-acyclic-orientations
bibkey: muhlherr2026acyclic
doi: null
url: https://arxiv.org/abs/2609.02249v2
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/TripartiteAcyclicOrientations.result
---

# Clause (4) of the Mühlherr–Poullot conjecture on acyclic orientations

## Problem

L. Mühlherr and G. Poullot (arXiv:2609.02249, 2026) conjecture in §3.1:

> Conjecture 1. For the following graphs G, we have ψ(G) ≡ 2 mod 4, and
> consequently G is not AO-Hamiltonian since G has an even number of edges:
> [...]
> (4) The complete tripartite graphs K m,n,p for n, m, p not all odd.

where ψ(G) is the number of acyclic orientations of G. Issue #11156 fixes the
reading: an orientation gives every edge exactly one direction and non-edges
none, acyclic means that the transitive closure has no loop, and K_{m,n,p} has
three nonempty parts of sizes m, n, p with edges exactly between different
parts. Only the congruence of clause (4) is settled; the paper's remark about
the number of edges is not part of the claim.

## Motivation

ψ(G) = T_G(2, 0) is the Tutte polynomial at the q = −1 point of the Potts
model. The paper uses ψ(G) ≡ 2 (mod 4), together with an even number of edges,
to rule out Hamiltonian cycles in the flip graph of acyclic orientations.
`D5/S3/Combinatorics/Graph/TripartiteAcyclicOrientations.result` proves clause
(4), and the proof gives ψ(K_{m,n,p}) ≡ 2 (mod 4) for all m, n, p ≥ 1.

## Gap

Issue #11156 preregisters the proof route and the literature check. The paper
has two versions and reports no change to Conjecture 1. Savage, Squire and West
(1993) proved the bipartite case ψ(K_{m,n}) ≡ 2 (mod 4) and state nothing for
tripartite graphs. Carballosa et al. (arXiv:2303.09021) give counting formulas
for complete multipartite graphs without any statement modulo 4.
`not-found-in-searched-scope`.

## Route

1. Two commuting involutions r, s of a finite set that act without fixed points,
   with r s also without fixed points, have orbits of size 4.
2. For non-adjacent vertices u, v with the same neighbours and an edge avoiding
   both, take r the reversal of all arcs and s the swap of u and v on the
   acyclic orientations. Then ψ(G) is congruent to the number of s-fixed
   acyclic orientations, which correspond bijectively to the acyclic
   orientations of G − v. So ψ(G) ≡ ψ(G − v) (mod 4).
3. In K_{m,n,p}, two vertices of the same part are such twins; removing them
   one at a time ends at the triangle, with ψ(K_3) = 6 ≡ 2 (mod 4).

## Falsifier

The proof would fail if some reversal or swap had a fixed point where step 2
excludes one, or if the correspondence of step 2 were not a bijection.

## Evidence

Exact computation (issue #11156): a brute-force count and the chromatic
polynomial formula agree on small cases, and all 1512 not-all-odd triples with
1 ≤ m, n, p ≤ 12 give ψ ≡ 2 (mod 4), while the perturbed claim ψ ≡ 0 holds for
none.

The canonical source is
`D5/S3/Combinatorics/Graph/TripartiteAcyclicOrientations.lean`. Its public
declarations are `IsOrientation`, `IsAcyclic`, `acyclicOrientationCount`,
`claim`, and `result`. The frozen module state has statement identity
`sha256:d805770b745dcab8d954b1ca08fe975cd968ead0569d8ab7b20158e905161a84`.
The result declaration has statement identity
`sha256:0e8d62573fd046d5d880b9e6ce19654ad753ee806301b7f477de12ac86099d8f`.
The Freeze event is
`sha256:4f4652031ffdef0c4ec6a9a02f0dbecc85cd79fd598aafd94d20285859bc5f8a`.
It has no project-level frozen prerequisite. The proof uses only the standard
axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`,
`native_decide`, or new axiom.

## Triage

Tier 1 external named conjecture (a clause of Conjecture 1 of a 2026 paper),
preregistered in issue #11156 before any Lean. `theorem`; resolution `proved`.
The public theorem has `proof_shape: content`: the Klein lemma, the twin lemma
with its bijection and the induction on the parts are new propositions on its
live path. Admission basis `open-problem-resolution`; utility `none`.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty,
priority, or the absence of an independent proof.
