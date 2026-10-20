---
bibkey: khesinli2024equivalence
authors: Andrey Boris Khesin, Alexander M. Li
year: 2024
title: Equivalence Classes of Quantum Error-Correcting Codes
doi: 10.48550/arXiv.2406.12083
url: https://arxiv.org/abs/2406.12083v1
claim: Conjecture 7.1 states that connected equivalence classes of normalized [n,k] encoders have sizes divisible by 3^k for positive integers n > k.
strata_touched:
  - D5/S3/Quantum/Codes/KhesinLiEquivalenceClasses
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.48550/arXiv.2406.12083

Source: https://arxiv.org/abs/2406.12083v1

Definition 2.7, p. 6:

> By performing a local complementation about vertex v, all edges connecting two vertices in N(v) are toggled.

Conjecture 6.3, p. 17, lists:

> 1. Local complementing about any vertex of the graph.
> 2. Permuting the output vertices.
> 3. Permuting the input vertices.
> 4. Performing row operations on the adjacency matrix of input to output edges.
> 5. Removing an input-input edge.
> 6. Applying local operations on the output edges.

Section 6, p. 18:

> Operation 4 consists of adding rows of the adjacency matrix between input and output nodes in modulo 2.

Claim 6.4, p. 19:

> To find the distinct encoders in an equivalence class of the set of Clifford codes, it is sufficient to find the distinct encoders in the equivalence class satisfying the following constraints:
>
> - The input-output adjacency matrix is in RREF.
> - The pivot nodes are the lowest-numbered output nodes, and they are ordered to match the order of the input nodes.
> - Local Clifford gates on the free output edges are all removed, leaving only output Z nodes with phase 0.
> - Diagrams with pivot-pivot edges are not included.

Section 7, p. 19:

> The code takes an integer representation, say n, of an encoder graph, performs one operation from Conjecture 6.3 on the encoder graph, then merges the disjoint sets of n and the integer representing the resulting encoder graph.

Section 7, p. 19, describes the normalization:

> To fix this, we first employ operation 5 from Conjecture 6.3 to set all input-input edges to 0.

> Operation 2 is used to put the pivots back into their fixed positions, so they once again correspond to their input vertices.

Conjecture 7.1, p. 20:

> For positive integers n > k, the equivalence classes of [n,k] codes with a single connected component have sizes divisible by 3^k.

The encoder vertices are `Fin k ⊕ Fin n`: inputs are `Sum.inl i`, outputs are `Sum.inr j`. Pivot outputs have indices below `k` and match inputs in order. Graphs have no input-input or pivot-pivot edges; input-pivot edges form the identity matrix. Local Clifford decorations are removed, so operation 6 contributes no graph operation. A normalized step is one of operations 1–5 followed by a finite sequence of operations 2–5, with normalized endpoints. The equivalence closure counts distinct labelled normalized graphs, rather than isomorphism classes. A connected class means that every normalized member is connected, following the restriction used in the source's figures.

The repository proof rotates each input-pivot pair with order three. These rotations commute, and connectedness excludes a zero free-row pair. The resulting free action of `(ZMod 3)^k` partitions every such class into orbits of size `3^k`. The proof does not establish completeness of the equivalence operations in Conjecture 6.3 or formulas for the number of classes. Completeness of the search for later literature settlements is ASSUMED-UNVERIFIED.
