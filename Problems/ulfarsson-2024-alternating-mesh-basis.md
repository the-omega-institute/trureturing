---
slug: ulfarsson-2024-alternating-mesh-basis
bibkey: ulfarsson2024bisc
doi: 10.48550/arXiv.2411.17778
url: https://arxiv.org/abs/2411.17778v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/MeshPattern/UlfarssonAlternatingMeshBasis.result
---

# Ulfarsson's alternating mesh-pattern basis conjecture

## Problem

H. Ulfarsson, *BiSC: An algorithm for discovering generalized permutation patterns*, arXiv:2411.17778v1, Conjecture 2.4.2, page 8; DOI 10.48550/arXiv.2411.17778. The source is recorded in [ulfarsson2024bisc](../Library/PermutationPatterns/ulfarsson2024bisc.md). The external named problem is preregistered in [#19120](https://github.com/the-omega-institute/trureturing/issues/19120).

> Let A be the union of the alternating subgroups, and let P be a basis of patterns such that A = Av(P). Then P = {(p, {0, …, n} × {0, …, n}) : p ∈ S_n ∖ A for some n}.

The settlement is **Proved** under the literal mesh-pattern conventions in #19120. Every mesh-pattern basis of the even permutations consists exactly of fully shaded odd permutations.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| A mesh pattern is a permutation together with shaded cells | `MeshPattern`, with length `k`, permutation `p`, and shading `R` | Positions are zero-based; cells range from $0$ through $k$ on each axis |
| An occurrence has order-isomorphic selected points and no extra point in a shaded region | `Occurs` | Increasing selected positions, relative value order, and both cell cardinalities are retained |
| $S$ contains permutations of every length | The dependent sum in `Av` and `Alt` | Length zero is included |
| $\operatorname{Av}(P)$ avoids all members of $P$ | `Av` | Universal quantification over the forbidden set |
| $P$ is a basis of $A$ | `IsBasis` | $\operatorname{Av}(P)=A$ and every subset with that avoidance set equals $P$; equality orientation is immaterial |
| $A$ is the union of the alternating subgroups | `Alt` | The sign is $1$ |
| The forbidden patterns are precisely fully shaded odd permutations | `claim` and `result` | $R=\mathrm{univ}$ and sign different from $1$, quantified over every basis $P$ |

Every public definition has the literal body of its binding convention in #19120. The result adds no binder or hypothesis beyond `claim`.

## Motivation

BiSC outputs fully shaded patterns for the alternating subgroups. Conjecture 2.4.2 asks whether a mesh-pattern basis can describe parity using any partial shading.

## Gap

Finite observations do not establish the assertion over all pattern lengths and shadings. A proof must rule out every unshaded cell and identify every forbidden underlying permutation.

## Route

Let $(a,b)$ be an unshaded cell of a pattern of length $k$. Insert two points there, using either order for their values. The original points supply an occurrence in both permutations of length $k+2$. Exchanging the two new positions multiplies the sign by $-1$, so one extension is even. Therefore a pattern forbidden by all even permutations cannot have an unshaded cell.

For a fully shaded pattern, an occurrence must select every point of the containing permutation. The resulting finite order isomorphisms force equality of the dependent length-permutation pair. Hence such a pattern excludes exactly its underlying permutation. Equality of its avoidance class with the even permutations forces precisely the fully shaded odd permutations.

## Falsifier

The construction would fail if an unshaded cell admitted neither even extension, or if a fully shaded pattern occurred in a different underlying permutation. The private lemmas `exists_even_extension` and `full_occurs_iff` rule out these alternatives; the public theorem `result` proves the complete claim.

## Evidence

The kernel-checked statement is `D5.S3.Combinatorics.MeshPattern.UlfarssonAlternatingMeshBasis.result`, in [UlfarssonAlternatingMeshBasis.lean](../D5/S3/Combinatorics/MeshPattern/UlfarssonAlternatingMeshBasis.lean), with its [Blueprint](../Blueprint/D5/S3/Combinatorics/MeshPattern/UlfarssonAlternatingMeshBasis.md). `occurs_insertPair` constructs each occurrence, `insertPair_sign_flip` gives opposite signs, `exists_even_extension` chooses the even extension, and `full_occurs_iff` proves full-shading rigidity. The module imports pinned Mathlib and has no frozen D5 dependencies.

The escape audit for the sole public theorem `result` is unfinished: [#19180](https://github.com/the-omega-institute/trureturing/issues/19180). The inspected enrolled templates do not supply a faithful typed registration without additional source reconstruction, statement bridge, whole-family variation, role and anchor sensitivity, and actual observational dependence on the unrestricted domain of pattern sets. No Reg mirror or `declared_validated` registration is supplied.

### Experiment

[The independent finite checker](https://github.com/the-omega-institute/trureturing-experiments/tree/6789b5a1d1711e63cbc5733667a1317a44615188/docs/reports/ulfarsson-2024-alternating-mesh-basis) is in `the-omega-institute/trureturing-experiments`, commit `6789b5a1d1711e63cbc5733667a1317a44615188`. From that revision, `python3 docs/reports/ulfarsson-2024-alternating-mesh-basis/check.py` exits 0 (`RESULT PASS`). Script SHA-256: `d88c18e25999fb64903f97c5ae25ac10acbf58b9605ef7f8a519a7f20d0c4887`.

The checker tests 2,533 pattern cases with an unshaded cell: all shadings for $k\le2$, and 250 candidate sampled shadings per permutation for $k=3$, excluding fully shaded cases. It chooses the first unshaded cell of each case. In every tested case both insertions contain the pattern and have opposite signs. For $k\le3$ and every containing permutation of length $n\le k+2$, it checks that a fully shaded pattern occurs exactly in its underlying permutation. These finite readings are **computed**; the all-length conclusion comes from the Lean proof.

## Triage

### What the settlement shows

| Item | Status and evidence | Boundary |
| --- | --- | --- |
| Settlement | **Kernel-checked:** `result` proves Conjecture 2.4.2 under the unchanged binding definitions | A basis is quantified as in the source |
| Scope | **Open in this delivery:** Conjecture 2.4.1 concerning the dihedral subgroups | `claim` and `result` concern only the alternating subgroups |
| Mechanism | **Kernel-checked:** `occurs_insertPair` and `insertPair_sign_flip` preserve an occurrence under two opposite-parity insertions; `exists_even_extension` selects an even extension | Every unshaded cell, with no finite length cutoff |
| Minimality | **Proved in prose from the displayed argument:** only $\operatorname{Av}(P)=\mathrm{Alt}$ is needed | In `result`, basis equality supplies each avoidance membership; full-shading rigidity identifies forbidden patterns. No step invokes subset-minimality. The weaker-hypothesis statement is not separately exported |
| Other classes | **Open:** no generalized theorem for other permutation classes is claimed | A corresponding extension property would require its own proof |
| Prior-art eligibility | **Literature reading:** no settlement in the scope recorded in #19120 | Completeness is **ASSUMED-UNVERIFIED** |
| Finite validation | **Computed:** the experiment entry records the 2,533 insertion checks and the full-shading checks for $k\le3$, $n\le k+2$ | This computation alone gives no unrestricted theorem |

Full shading is essential: a partially shaded pattern cannot distinguish parity, whereas a fully shaded pattern pins the complete containing permutation. This explains the fully shaded output of BiSC for the alternating case. The source's numerical observations are consistent with the all-length theorem. Its dihedral conjecture and claims about other permutation sets receive no settlement from this module. No additional source result dependent on Conjecture 2.4.2 is identified by the literature screen in #19120.

### Literature status

The source and literature checks recorded in #19120 cover arXiv:2411.17778v1, Sections 1–2, and its predecessor arXiv:1211.7110v1. The search producer reports OpenAlex work `W4404990126` with zero citing works, the author's BiSC page, and later papers 2609.15642v2, 2604.01143v1 and 2603.16004v1. The Atkinson and Atkinson–Beals results concern classically closed subgroups and do not apply to the even permutations. The orchestrator reports no repository or preregistration owner of this conjecture; earlier mesh-pattern issues #12358 and #12885 address other statements. Semantic Scholar returned HTTP 429. No settlement was found within that recorded scope.

## ASSUMED-UNVERIFIED

Literature completeness and worldwide novelty are **ASSUMED-UNVERIFIED**. The finite experiment does not establish an unrestricted theorem by itself. Conjecture 2.4.1 and extensions to other classes remain open in this delivery. The escape audit is unfinished under #19180 and is not registration evidence.
