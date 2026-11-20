# Distance multiplicity for a universal-clique family

## Abstract

A native width-two cograph family attains the ordinary distance multiplicity bound at unbounded orders.

Open Problem 14.2(ii) has a characterization clause and an explicit infinite-family clause. The results here give the explicit family and classify its parameters at the fixed shift s − 2. The survey states the question on p. 22 and the bound as Theorem 6.4 on p. 14. See `D5/L/QuadraticForms/mannamandaltura2026cographdistance`.

**Definition 1.1 (Native vertex carrier).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Cographs/UniversalCliqueCographDistance.Vertex`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/Cographs/UniversalCliqueCographDistance.Vertex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Acknowledgement.* Santanu Mandal and Pallabi Manna (2026). *The Distance Laplacian and Distance Signless Laplacian Spectra of C-Graphs*. DOI: [10.48550/arXiv.2610.08599](https://doi.org/10.48550/arXiv.2610.08599). URL: <https://arxiv.org/abs/2610.08599v1>.

*Commentary.*

For natural r, s and b the vertices are Fin r ⊕ ((Fin s ⊕ Fin s) ⊕ Fin b). The four summands are the hub clique, the two bipartite parts and the isolates.

**Definition 1.2 (Universal-clique join).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Cographs/UniversalCliqueCographDistance.graph`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/Cographs/UniversalCliqueCographDistance.graph` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Acknowledgement.* Santanu Mandal and Pallabi Manna (2026). *The Distance Laplacian and Distance Signless Laplacian Spectra of C-Graphs*. DOI: [10.48550/arXiv.2610.08599](https://doi.org/10.48550/arXiv.2610.08599). URL: <https://arxiv.org/abs/2610.08599v1>.

*Commentary.*

On Vertex(r,s,b), the graph is the join of K_r with the disjoint union of K_{s,s} and b isolates. The join is the complement of the disjoint sum of the two complements.

**Theorem 1.3 (Connectedness).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Cographs/UniversalCliqueCographDistance.connected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Cographs/UniversalCliqueCographDistance.connected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Acknowledgement.* Santanu Mandal and Pallabi Manna (2026). *The Distance Laplacian and Distance Signless Laplacian Spectra of C-Graphs*. DOI: [10.48550/arXiv.2610.08599](https://doi.org/10.48550/arXiv.2610.08599). URL: <https://arxiv.org/abs/2610.08599v1>.

*Commentary.*

For r > 0 the first hub is universal, so the native graph is connected.

**Theorem 1.4 (Ordinary shortest-path distances).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Cographs/UniversalCliqueCographDistance.distance`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Cographs/UniversalCliqueCographDistance.distance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Acknowledgement.* Santanu Mandal and Pallabi Manna (2026). *The Distance Laplacian and Distance Signless Laplacian Spectra of C-Graphs*. DOI: [10.48550/arXiv.2610.08599](https://doi.org/10.48550/arXiv.2610.08599). URL: <https://arxiv.org/abs/2610.08599v1>.

*Commentary.*

For r > 0 and all vertices u and v, dist(u,v) is zero when u=v, one for an edge and two for distinct nonadjacent vertices. A hub supplies the intermediate vertex.

**Theorem 1.5 (Induced four-vertex path exclusion).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Cographs/UniversalCliqueCographDistance.induced_path_excluded`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Cographs/UniversalCliqueCographDistance.induced_path_excluded` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Acknowledgement.* Santanu Mandal and Pallabi Manna (2026). *The Distance Laplacian and Distance Signless Laplacian Spectra of C-Graphs*. DOI: [10.48550/arXiv.2610.08599](https://doi.org/10.48550/arXiv.2610.08599). URL: <https://arxiv.org/abs/2610.08599v1>.

*Commentary.*

For all natural r, s and b the native graph has no induced P4. Nonedges at positions 0 and 2, and 1 and 3, exclude the hub vertices. A putative path cannot use an isolate. Alternation across the two bipartite parts makes the endpoints adjacent.

**Theorem 1.6 (Two vicinal chains).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Cographs/UniversalCliqueCographDistance.two_chain_cover`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Cographs/UniversalCliqueCographDistance.two_chain_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Acknowledgement.* Santanu Mandal and Pallabi Manna (2026). *The Distance Laplacian and Distance Signless Laplacian Spectra of C-Graphs*. DOI: [10.48550/arXiv.2610.08599](https://doi.org/10.48550/arXiv.2610.08599). URL: <https://arxiv.org/abs/2610.08599v1>.

*Commentary.*

For every r, s and b put the right part in one chain and all other vertices in the other. Vertices of a fixed independent part have the same open neighborhood. Isolates are below all vertices and hubs are above all vertices for N(u) ⊆ N[v].

**Theorem 1.7 (An opposite-part antichain).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Cographs/UniversalCliqueCographDistance.incomparable_parts`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Cographs/UniversalCliqueCographDistance.incomparable_parts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Acknowledgement.* Santanu Mandal and Pallabi Manna (2026). *The Distance Laplacian and Distance Signless Laplacian Spectra of C-Graphs*. DOI: [10.48550/arXiv.2610.08599](https://doi.org/10.48550/arXiv.2610.08599). URL: <https://arxiv.org/abs/2610.08599v1>.

*Commentary.*

For s ≥ 2 every left vertex and every right vertex are incomparable in both directions. A second vertex in each part supplies the required neighborhood obstruction.

**Theorem 1.8 (Exact vicinal width).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Cographs/UniversalCliqueCographDistance.width`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Cographs/UniversalCliqueCographDistance.width` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Acknowledgement.* Santanu Mandal and Pallabi Manna (2026). *The Distance Laplacian and Distance Signless Laplacian Spectra of C-Graphs*. DOI: [10.48550/arXiv.2610.08599](https://doi.org/10.48550/arXiv.2610.08599). URL: <https://arxiv.org/abs/2610.08599v1>.

*Commentary.*

For s ≥ 2 the minimum vicinal chain-cover size is two in the existing extended-natural width. The exhibited cover gives the upper bound. The two incomparable vertices must receive distinct chain labels.

**Definition 1.9 (Real ordinary distance matrix).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Cographs/UniversalCliqueCographDistance.distanceMatrix`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/Cographs/UniversalCliqueCographDistance.distanceMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Acknowledgement.* Santanu Mandal and Pallabi Manna (2026). *The Distance Laplacian and Distance Signless Laplacian Spectra of C-Graphs*. DOI: [10.48550/arXiv.2610.08599](https://doi.org/10.48550/arXiv.2610.08599). URL: <https://arxiv.org/abs/2610.08599v1>.

*Commentary.*

The (u,v) entry is the real cast of SimpleGraph.dist on graph(r,s,b).

**Definition 1.10 (Fixed shifted distance matrix).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Cographs/UniversalCliqueCographDistance.shiftedDistance`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/Cographs/UniversalCliqueCographDistance.shiftedDistance` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Acknowledgement.* Santanu Mandal and Pallabi Manna (2026). *The Distance Laplacian and Distance Signless Laplacian Spectra of C-Graphs*. DOI: [10.48550/arXiv.2610.08599](https://doi.org/10.48550/arXiv.2610.08599). URL: <https://arxiv.org/abs/2610.08599v1>.

*Commentary.*

Subtract ((s : ℝ) − 2) times the identity from distanceMatrix(r,s,b).

**Definition 1.11 (Real shifted kernel).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Cographs/UniversalCliqueCographDistance.shiftedKernel`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/Cographs/UniversalCliqueCographDistance.shiftedKernel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Acknowledgement.* Santanu Mandal and Pallabi Manna (2026). *The Distance Laplacian and Distance Signless Laplacian Spectra of C-Graphs*. DOI: [10.48550/arXiv.2610.08599](https://doi.org/10.48550/arXiv.2610.08599). URL: <https://arxiv.org/abs/2610.08599v1>.

*Commentary.*

Take the linear-map kernel of shiftedDistance(r,s,b) on real vertex functions. This is the eigenspace at s − 2.

**Theorem 1.12 (Exact multiplicity at s − 2).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Cographs/UniversalCliqueCographDistance.shiftedKernel_finrank`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Cographs/UniversalCliqueCographDistance.shiftedKernel_finrank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Acknowledgement.* Santanu Mandal and Pallabi Manna (2026). *The Distance Laplacian and Distance Signless Laplacian Spectra of C-Graphs*. DOI: [10.48550/arXiv.2610.08599](https://doi.org/10.48550/arXiv.2610.08599). URL: <https://arxiv.org/abs/2610.08599v1>.

*Commentary.*

For r > 0, s ≥ 2 and b > 0 the real kernel dimension is two if b(r − 2(s − 1)) = s(s − 1) in the integers and one otherwise. In particular r=1 always gives one. Row differences force constancy in the four cells. Every kernel vector has coordinates (−((s+2b)/r)z, p, z−p, z) with (rb−(s−1)(s+2b))z=0. The two parameters are recoverable from their left and isolate coordinates, giving a linear equivalence with ℝ × ℝ in the zero-residual case and with ℝ otherwise. The dimension counts the full eigenspace of the real symmetric distance matrix.

**Theorem 1.13 (Positive-divisor parameterization).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Cographs/UniversalCliqueCographDistance.parameter_iff_divisor`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Cographs/UniversalCliqueCographDistance.parameter_iff_divisor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Acknowledgement.* Santanu Mandal and Pallabi Manna (2026). *The Distance Laplacian and Distance Signless Laplacian Spectra of C-Graphs*. DOI: [10.48550/arXiv.2610.08599](https://doi.org/10.48550/arXiv.2610.08599). URL: <https://arxiv.org/abs/2610.08599v1>.

*Commentary.*

For s ≥ 2 and b > 0 the integer equality holds exactly when there is a positive natural divisor d of s(s−1) such that r=2(s−1)+d and b=s(s−1)/d. Positivity of s(s−1) forces the integer difference r−2(s−1) to be positive. Its natural value gives the divisor, and exact division recovers b.

**Theorem 1.14 (An explicit extremal graph at each s ≥ 2).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Cographs/UniversalCliqueCographDistance.family`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Cographs/UniversalCliqueCographDistance.family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*. URL: <https://arxiv.org/pdf/2611.06981v1#page=22>.

*Acknowledgement.* Santanu Mandal and Pallabi Manna (2026). *The Distance Laplacian and Distance Signless Laplacian Spectra of C-Graphs*. DOI: [10.48550/arXiv.2610.08599](https://doi.org/10.48550/arXiv.2610.08599). URL: <https://arxiv.org/abs/2610.08599v1>.

*Commentary.*

Choose the divisor s−1, so r=3(s−1) and b=s. The graph has order 6s−3, is connected and induced-P4-free, and has vicinal width two. The real shift s−2 is distinct from −1 and −2, belongs to the ordinary distance spectrum, and has real eigenspace dimension two.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Cographs/UniversalCliqueCographDistance.Vertex`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Cographs/UniversalCliqueCographDistance.connected`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Cographs/UniversalCliqueCographDistance.distance`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Cographs/UniversalCliqueCographDistance.distanceMatrix`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Cographs/UniversalCliqueCographDistance.family`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Cographs/UniversalCliqueCographDistance.graph`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Cographs/UniversalCliqueCographDistance.incomparable_parts`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Cographs/UniversalCliqueCographDistance.induced_path_excluded`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Cographs/UniversalCliqueCographDistance.parameter_iff_divisor`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Cographs/UniversalCliqueCographDistance.shiftedDistance`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Cographs/UniversalCliqueCographDistance.shiftedKernel`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Cographs/UniversalCliqueCographDistance.shiftedKernel_finrank`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Cographs/UniversalCliqueCographDistance.two_chain_cover`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Cographs/UniversalCliqueCographDistance.width`
- Dependency: [D5/S3/Combinatorics/SpectralGraph/MandalMannaDQDilworthRefutation](../MandalMannaDQDilworthRefutation.md)
