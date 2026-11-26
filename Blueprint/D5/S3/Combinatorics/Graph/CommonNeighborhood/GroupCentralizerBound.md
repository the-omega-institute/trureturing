# Centralizer bounds for the commuting graph of a finite group

## Abstract

Centralizer and least-prime common-neighbourhood energy bounds for the commuting graph of every finite nonabelian group.

**Theorem 1.1 (Centralizer and least-prime bounds).**

$$\forall G \in \operatorname{Type},\; [\operatorname{Group}\left(G\right)][\operatorname{Fintype}\left(G\right)]\left(\exists a \in G,\; \exists b \in G,\; a \cdot b \ne b \cdot a\right) \Rightarrow \left(\left(1 \le z \land \left((p^{2} - 1) \cdot z \le n \land \left(z + 2 \le n \land \left(3 \le n \land z \mid n\right)\right)\right)\right) \land \left(\operatorname{graphEnergy}\left(\operatorname{commutingGraph}\left(G\right), \operatorname{MatrixKind}.\operatorname{commonNeighbour}\right) \le 2 \cdot \sum_{x: \operatorname{Vertex}\left(G\right)} \operatorname{max}\left(\operatorname{Fintype}.\operatorname{card}\left(\operatorname{Subgroup}.\operatorname{centralizer}\left(\{x\}\right)\right) - z - 2, 0\right) \land \left(2 \cdot \sum_{x: \operatorname{Vertex}\left(G\right)} \operatorname{max}\left(\operatorname{Fintype}.\operatorname{card}\left(\operatorname{Subgroup}.\operatorname{centralizer}\left(\{x\}\right)\right) - z - 2, 0\right) \le n \cdot \operatorname{max}\left(\frac{2 \cdot (n + z)}{p} - 2 \cdot z - 4, 0\right) \land \left(n \cdot \operatorname{max}\left(\frac{2 \cdot (n + z)}{p} - 2 \cdot z - 4, 0\right) \le 2 \cdot n \cdot (\frac{n + z}{p} - z - 1) \land \left(n \cdot \operatorname{max}\left(\frac{2 \cdot (n + z)}{p} - 2 \cdot z - 4, 0\right) \le n \cdot \operatorname{max}\left(n - z - 4, 0\right) \land \left(n \cdot \operatorname{max}\left(n - z - 4, 0\right) \le n \cdot (n - z - 2) \land n \cdot (n - z - 2) < 2 \cdot (n - 1) \cdot (n - 2)\right)\right)\right)\right)\right)\right), n = \operatorname{Fintype}.\operatorname{card}\left(\operatorname{Vertex}\left(G\right)\right), z = \operatorname{Fintype}.\operatorname{card}\left(\operatorname{Subgroup}.\operatorname{center}\left(G\right)\right), p = \operatorname{Nat}.\operatorname{minFac}\left(\operatorname{Fintype}.\operatorname{card}\left(G\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CommonNeighborhood/GroupCentralizerBound.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Proofs of Nath–Fasfous–Das–Shang's commuting and surface conjectures, and a sharp form of Tak–Dutta–Nath's clique theorem*. DOI: [10.5281/zenodo.24398996](https://doi.org/10.5281/zenodo.24398996). URL: <https://doi.org/10.5281/zenodo.24398996>.

*Commentary.*

For every finite group G with two elements whose products differ, write z for the order of its center, n for the number of noncentral elements, C(x) for the centralizer of x and p for the least prime dividing |G|; in the displayed formula the real quantities n, z, p and the centralizer orders are the casts of these natural numbers. Then z is at least 1, n is at least (p^2-1)z, n is at least z+2 and at least 3, and z divides n. The common-neighbourhood energy of the commuting graph on the individual noncentral elements (Vertex(G) and commutingGraph(G) of the noncentral commuting-graph module, graphEnergy of the cyclic-extension module) is at most twice the sum over noncentral x of max(|C(x)|-z-2,0), and that is at most n max(2(n+z)/p-2z-4,0). This last quantity is at most 2n((n+z)/p-z-1), and also at most n max(n-z-4,0), which is at most n(n-z-2), strictly below the complete-graph value 2(n-1)(n-2).

The per-vertex sum and the bound 2n((n+z)/p-z-1) are Corollary 4 of Ma and Zhang, Zenodo DOI 10.5281/zenodo.24398996, and the strict bound n(n-z-2) < 2(n-1)(n-2) with n at least z+2 at least 3 is their Theorem 2. The repository sharpens the least-prime form to n max(2(n+z)/p-2z-4,0) and adds n at least (p^2-1)z and z dividing n. The ring analogue is RingNoncentralBound.

For a noncentral x, the center, x itself and the graph neighbours of x are disjoint inside the centralizer C(x), so deg(x)+z+1 is at most |C(x)|; this inequality is the noncentral commuting-graph module's degree_and_center_le_centralizer. C(x) is a proper subgroup, so its index is a divisor of |G| exceeding one, hence at least p, and p|C(x)| is at most |G| = n+z. The center is a proper subgroup of C(x) whose index is likewise at least p, so p^2 z is at most |G| and n is at least (p^2-1)z; Lagrange also gives z dividing |G| and hence n. The neighbourhood-clique bound and the degree inequality give the per-vertex energy bound; the remaining steps use p at least 2 and |C(x)| at least z+1, and 2(n-1)(n-2)-n(n-z-2) = (n-2)^2+nz is positive.

The hypotheses are needed as follows. Without two non-commuting elements the vertex type is empty and n at least z+2 fails. Finiteness is needed for the orders and the spectrum. The quaternion group and the extraspecial groups of order p^3 attain p^2 z = |G|; in the symmetric group on three letters and the quaternion group the least-prime bound is 0, which equals the energy. These examples are not compiled.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/CommonNeighborhood/GroupCentralizerBound.result`
- Dependency: [D5/S3/Combinatorics/Graph/CommonNeighborhood/NeighbourhoodCliqueBound](NeighbourhoodCliqueBound.md)
