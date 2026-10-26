---
bibkey: guerrero2022laplacianenergies
authors: J. Guerrero
year: 2022
title: Laplacian Energies of Vertices
doi: 10.1016/j.laa.2024.11.016
url: https://arxiv.org/abs/2201.01252v1
claim: "Remark 6 conjectures d_min LE_G(v) ≤ E_G(v) ≤ d_max LE_G(v) for every vertex of a simple connected graph."
strata_touched:
  - D5/S3/Combinatorics/SpectralGraph/GuerreroVertexEnergyDegreeBounds
license: citation-only
triage: anchor
---

# Vertex energy and normalized Laplacian energy

## Verified locator

DOI: 10.1016/j.laa.2024.11.016

Source: https://arxiv.org/abs/2201.01252v1

The quoted text is from arXiv v1. The journal citation is Linear Algebra
Appl. 706 (2025), 124–143; the publisher edition has not been verified.

## Source statements

Page 1: “We will assume that G is simple and connected.”
“L := I − D^{−1/2} A D^{−1/2}, where D is the diagonal degree matrix, D_ii = d_i.”

Page 2: “Given a vertex v_i ∈ V, its energy is defined as E_G(v_i) := |A|_ii.”

Section 4, page 9: “For a connected simple graph G = (V, E) we define the
normalized Laplacian energy of a vertex v_i ∈ V as LE_G(v_i) := φ_i(|L − I|)”,
where φ_i(M) = M_ii.

Remark 6 (Conjecture), page 13: “In Theorem 17 of [6] it is proven that
d_min LE(G) ≤ E(G) ≤ d_max LE(G), where d_min and d_max are the minimum
and maximum degrees of G respectively. According to numerical experiments
the analog result is true for the energy of vertices, that is:
d_min LE_G(v) ≤ E_G(v) ≤ d_max LE_G(v) for all v ∈ V.”

## Encoding and scope

For a real symmetric matrix, `cfc (fun x : ℝ => |x|)` is its spectral
absolute value. The diagonal entry gives vertex energy. The normalized
Laplacian is exactly identity minus the adjacency matrix sandwiched between
diagonal matrices with entries `1 / Real.sqrt (G.degree v)`.
Natural degrees are coerced to real numbers. The witness is
`SimpleGraph.pathGraph 6`, with zero-based vertex `2` corresponding to the
source's vertex 3. Its positive semidefinite square-root certificates refute
the upper inequality. The universal lower inequality and the blow-up family
are outside the Lean conclusion.

Literature completeness is ASSUMED-UNVERIFIED. The bounded literature screen
in issue #19702 found no settlement of the quoted v1 assertion; the journal
version and an exhaustive search of citing works remain unverified.
