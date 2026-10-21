# Vertex energies and the maximum-degree bound

## Abstract

A six-vertex path disproves the upper local comparison between adjacency and normalized Laplacian energies.

**Definition 1.1 (Absolute value of a real symmetric matrix).**

$$\forall V \in \operatorname{Type},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall M \in \operatorname{Matrix}\left(V, V, \operatorname{Real}\right),\; \operatorname{matAbs}\left(M\right) = \operatorname{cfc}\left((\lambda x: \operatorname{Real} \mapsto \left|x\right|), M\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/GuerreroVertexEnergyDegreeBounds.matAbs` (`✓ std3`).

*Citation.* J. Guerrero (2022). *Laplacian Energies of Vertices*. DOI: [10.1016/j.laa.2024.11.016](https://doi.org/10.1016/j.laa.2024.11.016). URL: <https://arxiv.org/abs/2201.01252v1>.

*Commentary.*

Page 2 uses |A| in the sentence: "Given a vertex v_i ∈ V, its energy is defined as E_G(v_i) := |A|_ii." For a real symmetric matrix, cfc (fun x : ℝ => |x|) is its spectral absolute value: an orthonormal eigenbasis replaces every eigenvalue by its absolute value. The formula gives this expression on finite real matrices.

**Definition 1.2 (Adjacency energy of a vertex).**

$$\forall V \in \operatorname{Type},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{DecidableRel}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G\right)\right)] \forall v \in V,\; \operatorname{vertexEnergy}\left(G, v\right) = \operatorname{matAbs}\left(\operatorname{SimpleGraph}.\operatorname{adjMatrix}\left(G, \operatorname{Real}\right)\right)\left(v, v\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/GuerreroVertexEnergyDegreeBounds.vertexEnergy` (`✓ std3`).

*Citation.* J. Guerrero (2022). *Laplacian Energies of Vertices*. DOI: [10.1016/j.laa.2024.11.016](https://doi.org/10.1016/j.laa.2024.11.016). URL: <https://arxiv.org/abs/2201.01252v1>.

*Commentary.*

Page 2: "Given a vertex v_i ∈ V, its energy is defined as E_G(v_i) := |A|_ii." The matrix A is SimpleGraph.adjMatrix G ℝ, and v is the diagonal index. Every finite vertex type and its adjacency decision procedure are quantified.

**Definition 1.3 (Inverse square root of the degree matrix).**

$$\forall V \in \operatorname{Type},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{DecidableRel}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G\right)\right)] \operatorname{degInvSqrt}\left(G\right) = \operatorname{Matrix}.\operatorname{diagonal}\left((\lambda v: V \mapsto \frac{1}{\operatorname{Real}.\operatorname{sqrt}\left((\operatorname{SimpleGraph}.\operatorname{degree}\left(G, v\right): \operatorname{Real})\right)})\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/GuerreroVertexEnergyDegreeBounds.degInvSqrt` (`✓ std3`).

*Citation.* J. Guerrero (2022). *Laplacian Energies of Vertices*. DOI: [10.1016/j.laa.2024.11.016](https://doi.org/10.1016/j.laa.2024.11.016). URL: <https://arxiv.org/abs/2201.01252v1>.

*Commentary.*

Page 1: "L := I − D^{−1/2} A D^{−1/2}, where D is the diagonal degree matrix, D_ii = d_i." The displayed diagonal has entry 1 / √d_v, with the natural degree coerced to ℝ. Real division assigns zero to the reciprocal of zero; the counterexample has positive degree at every vertex.

**Definition 1.4 (Normalized Laplacian).**

$$\forall V \in \operatorname{Type},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{DecidableRel}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G\right)\right)] \operatorname{normLap}\left(G\right) = 1 - \operatorname{degInvSqrt}\left(G\right) \cdot \operatorname{SimpleGraph}.\operatorname{adjMatrix}\left(G, \operatorname{Real}\right) \cdot \operatorname{degInvSqrt}\left(G\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/GuerreroVertexEnergyDegreeBounds.normLap` (`✓ std3`).

*Citation.* J. Guerrero (2022). *Laplacian Energies of Vertices*. DOI: [10.1016/j.laa.2024.11.016](https://doi.org/10.1016/j.laa.2024.11.016). URL: <https://arxiv.org/abs/2201.01252v1>.

*Commentary.*

Page 1: "L := I − D^{−1/2} A D^{−1/2}, where D is the diagonal degree matrix, D_ii = d_i." The identity and products are real matrix operations, with D^{−1/2} given by degInvSqrt.

**Definition 1.5 (Normalized Laplacian energy of a vertex).**

$$\forall V \in \operatorname{Type},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{DecidableRel}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G\right)\right)] \forall v \in V,\; \operatorname{normLapVertexEnergy}\left(G, v\right) = \operatorname{matAbs}\left((\operatorname{normLap}\left(G\right) - 1)\right)\left(v, v\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/GuerreroVertexEnergyDegreeBounds.normLapVertexEnergy` (`✓ std3`).

*Citation.* J. Guerrero (2022). *Laplacian Energies of Vertices*. DOI: [10.1016/j.laa.2024.11.016](https://doi.org/10.1016/j.laa.2024.11.016). URL: <https://arxiv.org/abs/2201.01252v1>.

*Commentary.*

Section 4, page 9: "For a connected simple graph G = (V, E) we define the normalized Laplacian energy of a vertex v_i ∈ V as LE_G(v_i) := φ_i(|L − I|)". Here φ_i(M) = M_ii, so the expression is the corresponding diagonal of matAbs (normLap G − 1).

**Definition 1.6 (Remark 6 (Conjecture)).**

$$\operatorname{claim} = (\forall V \in \operatorname{Type},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{DecidableRel}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G\right)\right)] \operatorname{SimpleGraph}.\operatorname{Connected}\left(G\right) \Rightarrow (\forall v \in V,\; (\operatorname{SimpleGraph}.\operatorname{minDegree}\left(G\right): \operatorname{Real}) \cdot \operatorname{normLapVertexEnergy}\left(G, v\right) \le \operatorname{vertexEnergy}\left(G, v\right) \land \operatorname{vertexEnergy}\left(G, v\right) \le (\operatorname{SimpleGraph}.\operatorname{maxDegree}\left(G\right): \operatorname{Real}) \cdot \operatorname{normLapVertexEnergy}\left(G, v\right)))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/GuerreroVertexEnergyDegreeBounds.claim` (`✓ std3`).

*Citation.* J. Guerrero (2022). *Laplacian Energies of Vertices*. DOI: [10.1016/j.laa.2024.11.016](https://doi.org/10.1016/j.laa.2024.11.016). URL: <https://arxiv.org/abs/2201.01252v1>.

*Commentary.*

Remark 6 (Conjecture), page 13: "In Theorem 17 of [6] it is proven that d_min LE(G) ≤ E(G) ≤ d_max LE(G), where d_min and d_max are the minimum and maximum degrees of G respectively. According to numerical experiments the analog result is true for the energy of vertices, that is: d_min LE_G(v) ≤ E_G(v) ≤ d_max LE_G(v) for all v ∈ V." Page 1 states: "We will assume that G is simple and connected." The proposition quantifies both inequalities over every vertex of every finite simple connected graph, using minDegree and maxDegree coerced to ℝ.

**Theorem 1.7 (Refutation on the six-vertex path).**

$$\neg (\forall V \in \operatorname{Type},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{DecidableRel}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G\right)\right)] \operatorname{SimpleGraph}.\operatorname{Connected}\left(G\right) \Rightarrow (\forall v \in V,\; (\operatorname{SimpleGraph}.\operatorname{minDegree}\left(G\right): \operatorname{Real}) \cdot \operatorname{normLapVertexEnergy}\left(G, v\right) \le \operatorname{vertexEnergy}\left(G, v\right) \land \operatorname{vertexEnergy}\left(G, v\right) \le (\operatorname{SimpleGraph}.\operatorname{maxDegree}\left(G\right): \operatorname{Real}) \cdot \operatorname{normLapVertexEnergy}\left(G, v\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/GuerreroVertexEnergyDegreeBounds.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Guerrero (2022). *Laplacian Energies of Vertices*. DOI: [10.1016/j.laa.2024.11.016](https://doi.org/10.1016/j.laa.2024.11.016). URL: <https://arxiv.org/abs/2201.01252v1>.

*Commentary.*

At zero-based vertex 2 of SimpleGraph.pathGraph 6 the adjacency energy is (7 + 4b − 2b²)/7, where 1 < b < 4/3 and b³ + b² − 2b − 1 = 0. Positive semidefinite square-root certificates identify this value and the normalized Laplacian energy (4 + √5)/10. The adjacency energy exceeds 5/4, whereas twice the normalized energy is below 5/4. The maximum degree is two. Thus the upper inequality fails. This proves no universal assertion about the lower inequality or about blow-ups. Literature completeness is ASSUMED-UNVERIFIED: the statement compared here is arXiv v1; the publisher edition and an exhaustive search of citing works have not been verified.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/GuerreroVertexEnergyDegreeBounds.claim`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/GuerreroVertexEnergyDegreeBounds.degInvSqrt`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/GuerreroVertexEnergyDegreeBounds.matAbs`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/GuerreroVertexEnergyDegreeBounds.normLap`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/GuerreroVertexEnergyDegreeBounds.normLapVertexEnergy`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/GuerreroVertexEnergyDegreeBounds.result`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/GuerreroVertexEnergyDegreeBounds.vertexEnergy`
