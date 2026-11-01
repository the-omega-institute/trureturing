# Complete maximal noncrossing carrier

## Abstract

Licensed exact polygon Catalan supplier

The count-only transplant is from AxiomMath/ClusterAlgebras revision a9174706bce3bcb0fa342b4614f98ef2acb7f91c. Complete license, authors, source spans and hashes, metadata adaptations and receiver-pinned retirement condition are in docs/reports/licenses/cluster-algebras-polygon-third-party.md. This supplies reused enumeration to PolygonConditionalCounts; it supplies no new escape content, actual ear contraction, fan positivity or flip conclusion.

All interval endpoints are integers. pair(i,j) is an ordered integer pair, two(p,q) is its two-element finite set, Ioo(a,b) is the finite open integer interval, and toNat is Int.toNat. Sides(a,b)=intervalSides(a,b), D(a,b)=intervalDiagonals(a,b), Seg(a,b,S)=intervalSegments(a,b,S)=S union Sides(a,b). I(a,b,S)=IsIntervalTriangulation(a,b,S): S subset D(a,b), pairwise noninterleaving, and each missing diagonal in D(a,b) interleaves an S member. tau(a,b)=intervalTriangulationCount(a,b). L(a,b) is the subtype of all S satisfying I(a,b,S), and W(a,b) is the dependent sum over k in Set.Ioo(a,b) of L(a,k) times L(k,b). For an element of W, apex is its integer k, left and right are its two interval triangulations, and val takes the entire underlying finite set.

For polygons, symPair(u,v) is the unordered pair in Sym2(ZMod(m)); Symtwo denotes Sym2. DiagonalSet(m) is the set of all internal diagonals, PolygonTriSet(m) the set of all finite original chord sets satisfying ClusterAlgebras.IsTriangulation, and A(m) the subtype of that entire set. IntervalTriSet(a,b) is the set of all interval triangulations. BijOn includes injection, surjection and mapping into the displayed sets. ENatcard is extended cardinality; coeENat and intCast are the indicated casts. catalanNumber is definitionally Mathlib catalan. The consumer's carrier is identical on whole chord sets, preserving all diagonal, crossing, noncrossing and maximality fields.

**Theorem 1.1 (catalanNumber_zero).**

$$(\operatorname{catalanNumber}\left(0\right) = 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.catalanNumber_zero` (`✓ std3`). ∎

*Citation.* Ashvin A. Swaminathan and Alexey Sorokin (2026). *ClusterAlgebras: interval and polygon triangulation enumeration*. URL: <https://github.com/AxiomMath/ClusterAlgebras/tree/a9174706bce3bcb0fa342b4614f98ef2acb7f91c>.

*Commentary.*

Exact licensed source support consumed by the complete polygon-count proof. Its source proof body is unchanged.

**Theorem 1.2 (catalanNumber_succ).**

$$\forall N \in Nat,\; (\operatorname{catalanNumber}\left((N + 1)\right) = \sum _{i\in \operatorname{range}\left((N + 1)\right)} ((\operatorname{catalanNumber}\left(i\right) \cdot \operatorname{catalanNumber}\left((N - i)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.catalanNumber_succ` (`✓ std3`). ∎

*Citation.* Ashvin A. Swaminathan and Alexey Sorokin (2026). *ClusterAlgebras: interval and polygon triangulation enumeration*. URL: <https://github.com/AxiomMath/ClusterAlgebras/tree/a9174706bce3bcb0fa342b4614f98ef2acb7f91c>.

*Commentary.*

Exact licensed source support consumed by the complete polygon-count proof. Its source proof body is unchanged.

**Theorem 1.3 (Interleave.symm).**

$$\forall p \in \operatorname{Prod}\left(\mathbb{Z}, \mathbb{Z}\right),\; \forall q \in \operatorname{Prod}\left(\mathbb{Z}, \mathbb{Z}\right),\; (\operatorname{Interleave}\left(p, q\right) \implies \operatorname{Interleave}\left(q, p\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.symm` (`✓ std3`). ∎

*Citation.* Ashvin A. Swaminathan and Alexey Sorokin (2026). *ClusterAlgebras: interval and polygon triangulation enumeration*. URL: <https://github.com/AxiomMath/ClusterAlgebras/tree/a9174706bce3bcb0fa342b4614f98ef2acb7f91c>.

*Commentary.*

Exact licensed source support consumed by the complete polygon-count proof. Its source proof body is unchanged.

**Theorem 1.4 (mem_intervalTriangulations).**

$$\forall a \in \mathbb{Z},\; \forall b \in \mathbb{Z},\; \forall S \in \operatorname{Finset}\left(\operatorname{Prod}\left(\mathbb{Z}, \mathbb{Z}\right)\right),\; ((S \in \operatorname{intervalTriangulations}\left(a, b\right)) \iff \operatorname{I}\left(a, b, S\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.mem_intervalTriangulations` (`✓ std3`). ∎

*Citation.* Ashvin A. Swaminathan and Alexey Sorokin (2026). *ClusterAlgebras: interval and polygon triangulation enumeration*. URL: <https://github.com/AxiomMath/ClusterAlgebras/tree/a9174706bce3bcb0fa342b4614f98ef2acb7f91c>.

*Commentary.*

Exact licensed source support consumed by the complete polygon-count proof. Its source proof body is unchanged.

**Theorem 1.5 (mk_mem_intervalDiagonals_iff).**

$$\forall a \in \mathbb{Z},\; \forall b \in \mathbb{Z},\; \forall i \in \mathbb{Z},\; \forall j \in \mathbb{Z},\; ((\operatorname{pair}\left(i, j\right) \in \operatorname{D}\left(a, b\right)) \iff ((a \leq i) \land ((j \leq b) \land (((i + 2) \leq j) \land \neg (((i = a) \land (j = b)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.mk_mem_intervalDiagonals_iff` (`✓ std3`). ∎

*Citation.* Ashvin A. Swaminathan and Alexey Sorokin (2026). *ClusterAlgebras: interval and polygon triangulation enumeration*. URL: <https://github.com/AxiomMath/ClusterAlgebras/tree/a9174706bce3bcb0fa342b4614f98ef2acb7f91c>.

*Commentary.*

Exact licensed source support consumed by the complete polygon-count proof. Its source proof body is unchanged.

**Theorem 1.6 (mk_mem_intervalSides_iff).**

$$\forall a \in \mathbb{Z},\; \forall b \in \mathbb{Z},\; \forall i \in \mathbb{Z},\; \forall j \in \mathbb{Z},\; ((\operatorname{pair}\left(i, j\right) \in \operatorname{Sides}\left(a, b\right)) \iff (((i = a) \land (j = b)) \lor ((a \leq i) \land ((i < b) \land (j = (i + 1))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.mk_mem_intervalSides_iff` (`✓ std3`). ∎

*Citation.* Ashvin A. Swaminathan and Alexey Sorokin (2026). *ClusterAlgebras: interval and polygon triangulation enumeration*. URL: <https://github.com/AxiomMath/ClusterAlgebras/tree/a9174706bce3bcb0fa342b4614f98ef2acb7f91c>.

*Commentary.*

Exact licensed source support consumed by the complete polygon-count proof. Its source proof body is unchanged.

**Theorem 1.7 (not_interleave_of_mem_intervalSides).**

$$\forall a \in \mathbb{Z},\; \forall b \in \mathbb{Z},\; \forall i \in \mathbb{Z},\; \forall j \in \mathbb{Z},\; \forall k \in \mathbb{Z},\; \forall l \in \mathbb{Z},\; ((\operatorname{pair}\left(i, j\right) \in \operatorname{Sides}\left(a, b\right)) \implies ((a \leq k) \implies ((l \leq b) \implies \neg (\operatorname{Interleave}\left(\operatorname{pair}\left(i, j\right), \operatorname{pair}\left(k, l\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.not_interleave_of_mem_intervalSides` (`✓ std3`). ∎

*Citation.* Ashvin A. Swaminathan and Alexey Sorokin (2026). *ClusterAlgebras: interval and polygon triangulation enumeration*. URL: <https://github.com/AxiomMath/ClusterAlgebras/tree/a9174706bce3bcb0fa342b4614f98ef2acb7f91c>.

*Commentary.*

Exact licensed source support consumed by the complete polygon-count proof. Its source proof body is unchanged.

**Theorem 1.8 (IsIntervalTriangulation.bounds_of_mem_intervalSegments).**

$$\forall a \in \mathbb{Z},\; \forall b \in \mathbb{Z},\; \forall S \in \operatorname{Finset}\left(\operatorname{Prod}\left(\mathbb{Z}, \mathbb{Z}\right)\right),\; ((a < b) \implies (\operatorname{I}\left(a, b, S\right) \implies (\forall i \in \mathbb{Z},\; \forall j \in \mathbb{Z},\; ((\operatorname{pair}\left(i, j\right) \in \operatorname{Seg}\left(a, b, S\right)) \implies ((a \leq i) \land ((i < j) \land (j \leq b)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.bounds_of_mem_intervalSegments` (`✓ std3`). ∎

*Citation.* Ashvin A. Swaminathan and Alexey Sorokin (2026). *ClusterAlgebras: interval and polygon triangulation enumeration*. URL: <https://github.com/AxiomMath/ClusterAlgebras/tree/a9174706bce3bcb0fa342b4614f98ef2acb7f91c>.

*Commentary.*

Exact licensed source support consumed by the complete polygon-count proof. Its source proof body is unchanged.

**Theorem 1.9 (IsIntervalTriangulation.not_interleave).**

$$\forall a \in \mathbb{Z},\; \forall b \in \mathbb{Z},\; \forall S \in \operatorname{Finset}\left(\operatorname{Prod}\left(\mathbb{Z}, \mathbb{Z}\right)\right),\; ((a < b) \implies (\operatorname{I}\left(a, b, S\right) \implies (\forall p \in \operatorname{Prod}\left(\mathbb{Z}, \mathbb{Z}\right),\; \forall q \in \operatorname{Prod}\left(\mathbb{Z}, \mathbb{Z}\right),\; ((p \in \operatorname{Seg}\left(a, b, S\right)) \implies ((q \in \operatorname{Seg}\left(a, b, S\right)) \implies \neg (\operatorname{Interleave}\left(p, q\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.not_interleave` (`✓ std3`). ∎

*Citation.* Ashvin A. Swaminathan and Alexey Sorokin (2026). *ClusterAlgebras: interval and polygon triangulation enumeration*. URL: <https://github.com/AxiomMath/ClusterAlgebras/tree/a9174706bce3bcb0fa342b4614f98ef2acb7f91c>.

*Commentary.*

Exact licensed source support consumed by the complete polygon-count proof. Its source proof body is unchanged.

**Theorem 1.10 (IsIntervalTriangulation.exists_interleave).**

$$\forall a \in \mathbb{Z},\; \forall b \in \mathbb{Z},\; \forall S \in \operatorname{Finset}\left(\operatorname{Prod}\left(\mathbb{Z}, \mathbb{Z}\right)\right),\; ((a < b) \implies (\operatorname{I}\left(a, b, S\right) \implies (\forall i \in \mathbb{Z},\; \forall j \in \mathbb{Z},\; ((a \leq i) \implies ((i < j) \implies ((j \leq b) \implies (\neg ((\operatorname{pair}\left(i, j\right) \in \operatorname{Seg}\left(a, b, S\right))) \implies (\exists q \in \operatorname{Prod}\left(\mathbb{Z}, \mathbb{Z}\right),\; ((q \in S) \land \operatorname{Interleave}\left(\operatorname{pair}\left(i, j\right), q\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.exists_interleave` (`✓ std3`). ∎

*Citation.* Ashvin A. Swaminathan and Alexey Sorokin (2026). *ClusterAlgebras: interval and polygon triangulation enumeration*. URL: <https://github.com/AxiomMath/ClusterAlgebras/tree/a9174706bce3bcb0fa342b4614f98ef2acb7f91c>.

*Commentary.*

Exact licensed source support consumed by the complete polygon-count proof. Its source proof body is unchanged.

**Theorem 1.11 (IsIntervalTriangulation.existsUnique_apex).**

$$\forall a \in \mathbb{Z},\; \forall b \in \mathbb{Z},\; \forall S \in \operatorname{Finset}\left(\operatorname{Prod}\left(\mathbb{Z}, \mathbb{Z}\right)\right),\; ((a < b) \implies (\operatorname{I}\left(a, b, S\right) \implies (\forall i \in \mathbb{Z},\; \forall k \in \mathbb{Z},\; (((i + 2) \leq k) \implies ((\operatorname{pair}\left(i, k\right) \in \operatorname{Seg}\left(a, b, S\right)) \implies (\exists j \in \mathbb{Z},\; (((i < j) \land ((j < k) \land ((\operatorname{pair}\left(i, j\right) \in \operatorname{Seg}\left(a, b, S\right)) \land (\operatorname{pair}\left(j, k\right) \in \operatorname{Seg}\left(a, b, S\right))))) \land (\forall z \in \mathbb{Z},\; (((i < z) \land ((z < k) \land ((\operatorname{pair}\left(i, z\right) \in \operatorname{Seg}\left(a, b, S\right)) \land (\operatorname{pair}\left(z, k\right) \in \operatorname{Seg}\left(a, b, S\right))))) \implies (z = j))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.existsUnique_apex` (`✓ std3`). ∎

*Citation.* Ashvin A. Swaminathan and Alexey Sorokin (2026). *ClusterAlgebras: interval and polygon triangulation enumeration*. URL: <https://github.com/AxiomMath/ClusterAlgebras/tree/a9174706bce3bcb0fa342b4614f98ef2acb7f91c>.

*Commentary.*

Exact licensed source support consumed by the complete polygon-count proof. Its source proof body is unchanged.

**Theorem 1.12 (IsIntervalTriangulation.le_or_le_of_apex).**

$$\forall a \in \mathbb{Z},\; \forall b \in \mathbb{Z},\; \forall S \in \operatorname{Finset}\left(\operatorname{Prod}\left(\mathbb{Z}, \mathbb{Z}\right)\right),\; ((a < b) \implies (\operatorname{I}\left(a, b, S\right) \implies (\forall k \in \mathbb{Z},\; ((\operatorname{pair}\left(a, k\right) \in \operatorname{Seg}\left(a, b, S\right)) \implies ((\operatorname{pair}\left(k, b\right) \in \operatorname{Seg}\left(a, b, S\right)) \implies (\forall i \in \mathbb{Z},\; \forall j \in \mathbb{Z},\; ((\operatorname{pair}\left(i, j\right) \in S) \implies ((j \leq k) \lor (k \leq i)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.le_or_le_of_apex` (`✓ std3`). ∎

*Citation.* Ashvin A. Swaminathan and Alexey Sorokin (2026). *ClusterAlgebras: interval and polygon triangulation enumeration*. URL: <https://github.com/AxiomMath/ClusterAlgebras/tree/a9174706bce3bcb0fa342b4614f98ef2acb7f91c>.

*Commentary.*

Exact licensed source support consumed by the complete polygon-count proof. Its source proof body is unchanged.

**Theorem 1.13 (IsIntervalTriangulation.eq_union_of_apex).**

$$\forall a \in \mathbb{Z},\; \forall b \in \mathbb{Z},\; \forall S \in \operatorname{Finset}\left(\operatorname{Prod}\left(\mathbb{Z}, \mathbb{Z}\right)\right),\; ((a < b) \implies (\operatorname{I}\left(a, b, S\right) \implies (\forall k \in \mathbb{Z},\; ((a < k) \implies ((k < b) \implies ((\operatorname{pair}\left(a, k\right) \in \operatorname{Seg}\left(a, b, S\right)) \implies ((\operatorname{pair}\left(k, b\right) \in \operatorname{Seg}\left(a, b, S\right)) \implies (S = \operatorname{union}\left(\operatorname{union}\left(\operatorname{inter}\left(S, \operatorname{D}\left(a, k\right)\right), \operatorname{inter}\left(S, \operatorname{D}\left(k, b\right)\right)\right), \operatorname{inter}\left(\operatorname{two}\left(\operatorname{pair}\left(a, k\right), \operatorname{pair}\left(k, b\right)\right), \operatorname{D}\left(a, b\right)\right)\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.eq_union_of_apex` (`✓ std3`). ∎

*Citation.* Ashvin A. Swaminathan and Alexey Sorokin (2026). *ClusterAlgebras: interval and polygon triangulation enumeration*. URL: <https://github.com/AxiomMath/ClusterAlgebras/tree/a9174706bce3bcb0fa342b4614f98ef2acb7f91c>.

*Commentary.*

Exact licensed source support consumed by the complete polygon-count proof. Its source proof body is unchanged.

**Theorem 1.14 (IsIntervalTriangulation.inter_left_of_apex).**

$$\forall a \in \mathbb{Z},\; \forall b \in \mathbb{Z},\; \forall S \in \operatorname{Finset}\left(\operatorname{Prod}\left(\mathbb{Z}, \mathbb{Z}\right)\right),\; ((a < b) \implies (\operatorname{I}\left(a, b, S\right) \implies (\forall k \in \mathbb{Z},\; ((k < b) \implies ((\operatorname{pair}\left(a, k\right) \in \operatorname{Seg}\left(a, b, S\right)) \implies ((\operatorname{pair}\left(k, b\right) \in \operatorname{Seg}\left(a, b, S\right)) \implies \operatorname{I}\left(a, k, \operatorname{inter}\left(S, \operatorname{D}\left(a, k\right)\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.inter_left_of_apex` (`✓ std3`). ∎

*Citation.* Ashvin A. Swaminathan and Alexey Sorokin (2026). *ClusterAlgebras: interval and polygon triangulation enumeration*. URL: <https://github.com/AxiomMath/ClusterAlgebras/tree/a9174706bce3bcb0fa342b4614f98ef2acb7f91c>.

*Commentary.*

Exact licensed source support consumed by the complete polygon-count proof. Its source proof body is unchanged.

**Theorem 1.15 (IsIntervalTriangulation.inter_right_of_apex).**

$$\forall a \in \mathbb{Z},\; \forall b \in \mathbb{Z},\; \forall S \in \operatorname{Finset}\left(\operatorname{Prod}\left(\mathbb{Z}, \mathbb{Z}\right)\right),\; ((a < b) \implies (\operatorname{I}\left(a, b, S\right) \implies (\forall k \in \mathbb{Z},\; ((a < k) \implies ((\operatorname{pair}\left(a, k\right) \in \operatorname{Seg}\left(a, b, S\right)) \implies ((\operatorname{pair}\left(k, b\right) \in \operatorname{Seg}\left(a, b, S\right)) \implies \operatorname{I}\left(k, b, \operatorname{inter}\left(S, \operatorname{D}\left(k, b\right)\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.inter_right_of_apex` (`✓ std3`). ∎

*Citation.* Ashvin A. Swaminathan and Alexey Sorokin (2026). *ClusterAlgebras: interval and polygon triangulation enumeration*. URL: <https://github.com/AxiomMath/ClusterAlgebras/tree/a9174706bce3bcb0fa342b4614f98ef2acb7f91c>.

*Commentary.*

Exact licensed source support consumed by the complete polygon-count proof. Its source proof body is unchanged.

**Theorem 1.16 (mk_mem_union_intervalDiagonals_iff).**

$$\forall a \in \mathbb{Z},\; \forall b \in \mathbb{Z},\; \forall k \in \mathbb{Z},\; \forall Sone \in \operatorname{Finset}\left(\operatorname{Prod}\left(\mathbb{Z}, \mathbb{Z}\right)\right),\; \forall Stwo \in \operatorname{Finset}\left(\operatorname{Prod}\left(\mathbb{Z}, \mathbb{Z}\right)\right),\; \forall i \in \mathbb{Z},\; \forall j \in \mathbb{Z},\; ((\operatorname{pair}\left(i, j\right) \in \operatorname{union}\left(\operatorname{union}\left(Sone, Stwo\right), \operatorname{inter}\left(\operatorname{two}\left(\operatorname{pair}\left(a, k\right), \operatorname{pair}\left(k, b\right)\right), \operatorname{D}\left(a, b\right)\right)\right)) \iff ((\operatorname{pair}\left(i, j\right) \in Sone) \lor ((\operatorname{pair}\left(i, j\right) \in Stwo) \lor ((((i = a) \land (j = k)) \lor ((i = k) \land (j = b))) \land (\operatorname{pair}\left(i, j\right) \in \operatorname{D}\left(a, b\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.mk_mem_union_intervalDiagonals_iff` (`✓ std3`). ∎

*Citation.* Ashvin A. Swaminathan and Alexey Sorokin (2026). *ClusterAlgebras: interval and polygon triangulation enumeration*. URL: <https://github.com/AxiomMath/ClusterAlgebras/tree/a9174706bce3bcb0fa342b4614f98ef2acb7f91c>.

*Commentary.*

Exact licensed source support consumed by the complete polygon-count proof. Its source proof body is unchanged.

**Theorem 1.17 (IsIntervalTriangulation.union).**

$$\forall a \in \mathbb{Z},\; \forall b \in \mathbb{Z},\; \forall k \in \mathbb{Z},\; \forall Sone \in \operatorname{Finset}\left(\operatorname{Prod}\left(\mathbb{Z}, \mathbb{Z}\right)\right),\; \forall Stwo \in \operatorname{Finset}\left(\operatorname{Prod}\left(\mathbb{Z}, \mathbb{Z}\right)\right),\; ((a < k) \implies ((k < b) \implies (\operatorname{I}\left(a, k, Sone\right) \implies (\operatorname{I}\left(k, b, Stwo\right) \implies \operatorname{I}\left(a, b, \operatorname{union}\left(\operatorname{union}\left(Sone, Stwo\right), \operatorname{inter}\left(\operatorname{two}\left(\operatorname{pair}\left(a, k\right), \operatorname{pair}\left(k, b\right)\right), \operatorname{D}\left(a, b\right)\right)\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.union` (`✓ std3`). ∎

*Citation.* Ashvin A. Swaminathan and Alexey Sorokin (2026). *ClusterAlgebras: interval and polygon triangulation enumeration*. URL: <https://github.com/AxiomMath/ClusterAlgebras/tree/a9174706bce3bcb0fa342b4614f98ef2acb7f91c>.

*Commentary.*

Exact licensed source support consumed by the complete polygon-count proof. Its source proof body is unchanged.

**Theorem 1.18 (union_inter_intervalDiagonals_left).**

$$\forall a \in \mathbb{Z},\; \forall b \in \mathbb{Z},\; \forall k \in \mathbb{Z},\; \forall Sone \in \operatorname{Finset}\left(\operatorname{Prod}\left(\mathbb{Z}, \mathbb{Z}\right)\right),\; \forall Stwo \in \operatorname{Finset}\left(\operatorname{Prod}\left(\mathbb{Z}, \mathbb{Z}\right)\right),\; (\operatorname{I}\left(a, k, Sone\right) \implies (\operatorname{I}\left(k, b, Stwo\right) \implies (\operatorname{inter}\left(\operatorname{union}\left(\operatorname{union}\left(Sone, Stwo\right), \operatorname{inter}\left(\operatorname{two}\left(\operatorname{pair}\left(a, k\right), \operatorname{pair}\left(k, b\right)\right), \operatorname{D}\left(a, b\right)\right)\right), \operatorname{D}\left(a, k\right)\right) = Sone)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.union_inter_intervalDiagonals_left` (`✓ std3`). ∎

*Citation.* Ashvin A. Swaminathan and Alexey Sorokin (2026). *ClusterAlgebras: interval and polygon triangulation enumeration*. URL: <https://github.com/AxiomMath/ClusterAlgebras/tree/a9174706bce3bcb0fa342b4614f98ef2acb7f91c>.

*Commentary.*

Exact licensed source support consumed by the complete polygon-count proof. Its source proof body is unchanged.

**Theorem 1.19 (union_inter_intervalDiagonals_right).**

$$\forall a \in \mathbb{Z},\; \forall b \in \mathbb{Z},\; \forall k \in \mathbb{Z},\; \forall Sone \in \operatorname{Finset}\left(\operatorname{Prod}\left(\mathbb{Z}, \mathbb{Z}\right)\right),\; \forall Stwo \in \operatorname{Finset}\left(\operatorname{Prod}\left(\mathbb{Z}, \mathbb{Z}\right)\right),\; ((a < k) \implies (\operatorname{I}\left(a, k, Sone\right) \implies (\operatorname{I}\left(k, b, Stwo\right) \implies (\operatorname{inter}\left(\operatorname{union}\left(\operatorname{union}\left(Sone, Stwo\right), \operatorname{inter}\left(\operatorname{two}\left(\operatorname{pair}\left(a, k\right), \operatorname{pair}\left(k, b\right)\right), \operatorname{D}\left(a, b\right)\right)\right), \operatorname{D}\left(k, b\right)\right) = Stwo))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.union_inter_intervalDiagonals_right` (`✓ std3`). ∎

*Citation.* Ashvin A. Swaminathan and Alexey Sorokin (2026). *ClusterAlgebras: interval and polygon triangulation enumeration*. URL: <https://github.com/AxiomMath/ClusterAlgebras/tree/a9174706bce3bcb0fa342b4614f98ef2acb7f91c>.

*Commentary.*

Exact licensed source support consumed by the complete polygon-count proof. Its source proof body is unchanged.

**Theorem 1.20 (union_apex_mem_intervalSegments).**

$$\forall a \in \mathbb{Z},\; \forall b \in \mathbb{Z},\; \forall k \in \mathbb{Z},\; \forall Sone \in \operatorname{Finset}\left(\operatorname{Prod}\left(\mathbb{Z}, \mathbb{Z}\right)\right),\; \forall Stwo \in \operatorname{Finset}\left(\operatorname{Prod}\left(\mathbb{Z}, \mathbb{Z}\right)\right),\; ((a < k) \implies ((k < b) \implies ((\operatorname{pair}\left(a, k\right) \in \operatorname{Seg}\left(a, b, \operatorname{union}\left(\operatorname{union}\left(Sone, Stwo\right), \operatorname{inter}\left(\operatorname{two}\left(\operatorname{pair}\left(a, k\right), \operatorname{pair}\left(k, b\right)\right), \operatorname{D}\left(a, b\right)\right)\right)\right)) \land (\operatorname{pair}\left(k, b\right) \in \operatorname{Seg}\left(a, b, \operatorname{union}\left(\operatorname{union}\left(Sone, Stwo\right), \operatorname{inter}\left(\operatorname{two}\left(\operatorname{pair}\left(a, k\right), \operatorname{pair}\left(k, b\right)\right), \operatorname{D}\left(a, b\right)\right)\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.union_apex_mem_intervalSegments` (`✓ std3`). ∎

*Citation.* Ashvin A. Swaminathan and Alexey Sorokin (2026). *ClusterAlgebras: interval and polygon triangulation enumeration*. URL: <https://github.com/AxiomMath/ClusterAlgebras/tree/a9174706bce3bcb0fa342b4614f98ef2acb7f91c>.

*Commentary.*

Exact licensed source support consumed by the complete polygon-count proof. Its source proof body is unchanged.

**Theorem 1.21 (exists_equiv_intervalTriangulation).**

$$\forall a \in \mathbb{Z},\; \forall b \in \mathbb{Z},\; (((a + 2) \leq b) \implies (\exists e \in \operatorname{Equiv}\left(\operatorname{L}\left(a, b\right), \operatorname{W}\left(a, b\right)\right),\; \forall S \in \operatorname{L}\left(a, b\right),\; ((\operatorname{pair}\left(a, \operatorname{apex}\left(\operatorname{app}\left(e, S\right)\right)\right) \in \operatorname{Seg}\left(a, b, \operatorname{val}\left(S\right)\right)) \land ((\operatorname{pair}\left(\operatorname{apex}\left(\operatorname{app}\left(e, S\right)\right), b\right) \in \operatorname{Seg}\left(a, b, \operatorname{val}\left(S\right)\right)) \land ((\operatorname{val}\left(\operatorname{left}\left(\operatorname{app}\left(e, S\right)\right)\right) = \operatorname{inter}\left(\operatorname{val}\left(S\right), \operatorname{D}\left(a, \operatorname{apex}\left(\operatorname{app}\left(e, S\right)\right)\right)\right)) \land (\operatorname{val}\left(\operatorname{right}\left(\operatorname{app}\left(e, S\right)\right)\right) = \operatorname{inter}\left(\operatorname{val}\left(S\right), \operatorname{D}\left(\operatorname{apex}\left(\operatorname{app}\left(e, S\right)\right), b\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.exists_equiv_intervalTriangulation` (`✓ std3`). ∎

*Citation.* Ashvin A. Swaminathan and Alexey Sorokin (2026). *ClusterAlgebras: interval and polygon triangulation enumeration*. URL: <https://github.com/AxiomMath/ClusterAlgebras/tree/a9174706bce3bcb0fa342b4614f98ef2acb7f91c>.

*Commentary.*

Exact licensed source support consumed by the complete polygon-count proof. Its source proof body is unchanged.

**Theorem 1.22 (card_subtype_isIntervalTriangulation).**

$$\forall a \in \mathbb{Z},\; \forall b \in \mathbb{Z},\; (\operatorname{Fintypecard}\left(\operatorname{L}\left(a, b\right)\right) = \operatorname{tau}\left(a, b\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.card_subtype_isIntervalTriangulation` (`✓ std3`). ∎

*Citation.* Ashvin A. Swaminathan and Alexey Sorokin (2026). *ClusterAlgebras: interval and polygon triangulation enumeration*. URL: <https://github.com/AxiomMath/ClusterAlgebras/tree/a9174706bce3bcb0fa342b4614f98ef2acb7f91c>.

*Commentary.*

Exact licensed source support consumed by the complete polygon-count proof. Its source proof body is unchanged.

**Theorem 1.23 (intervalTriangulationCount_eq_sum).**

$$\forall a \in \mathbb{Z},\; \forall b \in \mathbb{Z},\; (((a + 2) \leq b) \implies (\operatorname{tau}\left(a, b\right) = \sum _{k\in \operatorname{Ioo}\left(a, b\right)} ((\operatorname{tau}\left(a, k\right) \cdot \operatorname{tau}\left(k, b\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.intervalTriangulationCount_eq_sum` (`✓ std3`). ∎

*Citation.* Ashvin A. Swaminathan and Alexey Sorokin (2026). *ClusterAlgebras: interval and polygon triangulation enumeration*. URL: <https://github.com/AxiomMath/ClusterAlgebras/tree/a9174706bce3bcb0fa342b4614f98ef2acb7f91c>.

*Commentary.*

Exact licensed source support consumed by the complete polygon-count proof. Its source proof body is unchanged.

**Theorem 1.24 (intervalTriangulationCount_self_add_one).**

$$\forall a \in \mathbb{Z},\; (\operatorname{tau}\left(a, (a + 1)\right) = 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.intervalTriangulationCount_self_add_one` (`✓ std3`). ∎

*Citation.* Ashvin A. Swaminathan and Alexey Sorokin (2026). *ClusterAlgebras: interval and polygon triangulation enumeration*. URL: <https://github.com/AxiomMath/ClusterAlgebras/tree/a9174706bce3bcb0fa342b4614f98ef2acb7f91c>.

*Commentary.*

Exact licensed source support consumed by the complete polygon-count proof. Its source proof body is unchanged.

**Theorem 1.25 (intervalTriangulationCount_eq_catalanNumber).**

$$\forall a \in \mathbb{Z},\; \forall b \in \mathbb{Z},\; ((a < b) \implies (\operatorname{tau}\left(a, b\right) = \operatorname{catalanNumber}\left(\operatorname{toNat}\left(((b - a) - 1)\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.intervalTriangulationCount_eq_catalanNumber` (`✓ std3`). ∎

*Citation.* Ashvin A. Swaminathan and Alexey Sorokin (2026). *ClusterAlgebras: interval and polygon triangulation enumeration*. URL: <https://github.com/AxiomMath/ClusterAlgebras/tree/a9174706bce3bcb0fa342b4614f98ef2acb7f91c>.

*Commentary.*

Exact licensed source support consumed by the complete polygon-count proof. Its source proof body is unchanged.

**Theorem 1.26 (basePosSeg_mk).**

$$\forall m \in Nat,\; \forall c \in \operatorname{ZMod}\left(m\right),\; \forall u \in \operatorname{ZMod}\left(m\right),\; \forall v \in \operatorname{ZMod}\left(m\right),\; (\operatorname{basePosSeg}\left(c, \operatorname{symPair}\left(u, v\right)\right) = \operatorname{pair}\left(\operatorname{min}\left(\operatorname{basePos}\left(c, u\right), \operatorname{basePos}\left(c, v\right)\right), \operatorname{max}\left(\operatorname{basePos}\left(c, u\right), \operatorname{basePos}\left(c, v\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.basePosSeg_mk` (`✓ std3`). ∎

*Citation.* Ashvin A. Swaminathan and Alexey Sorokin (2026). *ClusterAlgebras: interval and polygon triangulation enumeration*. URL: <https://github.com/AxiomMath/ClusterAlgebras/tree/a9174706bce3bcb0fa342b4614f98ef2acb7f91c>.

*Commentary.*

Exact licensed source support consumed by the complete polygon-count proof. Its source proof body is unchanged.

**Theorem 1.27 (basePos_nonneg).**

$$\forall m \in Nat,\; \forall c \in \operatorname{ZMod}\left(m\right),\; \forall v \in \operatorname{ZMod}\left(m\right),\; (0 \leq \operatorname{basePos}\left(c, v\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.basePos_nonneg` (`✓ std3`). ∎

*Citation.* Ashvin A. Swaminathan and Alexey Sorokin (2026). *ClusterAlgebras: interval and polygon triangulation enumeration*. URL: <https://github.com/AxiomMath/ClusterAlgebras/tree/a9174706bce3bcb0fa342b4614f98ef2acb7f91c>.

*Commentary.*

Exact licensed source support consumed by the complete polygon-count proof. Its source proof body is unchanged.

**Theorem 1.28 (basePos_lt).**

$$\forall m \in Nat,\; [\operatorname{NeZero}\left(m\right)], \forall c \in \operatorname{ZMod}\left(m\right),\; \forall v \in \operatorname{ZMod}\left(m\right),\; (\operatorname{basePos}\left(c, v\right) < \operatorname{intCast}\left(m\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.basePos_lt` (`✓ std3`). ∎

*Citation.* Ashvin A. Swaminathan and Alexey Sorokin (2026). *ClusterAlgebras: interval and polygon triangulation enumeration*. URL: <https://github.com/AxiomMath/ClusterAlgebras/tree/a9174706bce3bcb0fa342b4614f98ef2acb7f91c>.

*Commentary.*

Exact licensed source support consumed by the complete polygon-count proof. Its source proof body is unchanged.

**Theorem 1.29 (basePos_eq_ite).**

$$\forall m \in Nat,\; [\operatorname{NeZero}\left(m\right)], \forall c \in \operatorname{ZMod}\left(m\right),\; \forall v \in \operatorname{ZMod}\left(m\right),\; (\operatorname{basePos}\left(c, v\right) = \operatorname{ite}\left((\operatorname{val}\left(c\right) \leq \operatorname{val}\left(v\right)), (\operatorname{intCast}\left(\operatorname{val}\left(v\right)\right) - \operatorname{intCast}\left(\operatorname{val}\left(c\right)\right)), ((\operatorname{intCast}\left(\operatorname{val}\left(v\right)\right) - \operatorname{intCast}\left(\operatorname{val}\left(c\right)\right)) + \operatorname{intCast}\left(m\right))\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.basePos_eq_ite` (`✓ std3`). ∎

*Citation.* Ashvin A. Swaminathan and Alexey Sorokin (2026). *ClusterAlgebras: interval and polygon triangulation enumeration*. URL: <https://github.com/AxiomMath/ClusterAlgebras/tree/a9174706bce3bcb0fa342b4614f98ef2acb7f91c>.

*Commentary.*

Exact licensed source support consumed by the complete polygon-count proof. Its source proof body is unchanged.

**Theorem 1.30 (basePos_injective).**

$$\forall m \in Nat,\; [\operatorname{NeZero}\left(m\right)], \forall c \in \operatorname{ZMod}\left(m\right),\; \operatorname{Injective}\left(\operatorname{basePos}\left(c\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.basePos_injective` (`✓ std3`). ∎

*Citation.* Ashvin A. Swaminathan and Alexey Sorokin (2026). *ClusterAlgebras: interval and polygon triangulation enumeration*. URL: <https://github.com/AxiomMath/ClusterAlgebras/tree/a9174706bce3bcb0fa342b4614f98ef2acb7f91c>.

*Commentary.*

Exact licensed source support consumed by the complete polygon-count proof. Its source proof body is unchanged.

**Theorem 1.31 (exists_basePos_eq).**

$$\forall m \in Nat,\; \forall c \in \operatorname{ZMod}\left(m\right),\; \forall k \in \mathbb{Z},\; ((0 \leq k) \implies ((k < \operatorname{intCast}\left(m\right)) \implies (\exists v \in \operatorname{ZMod}\left(m\right),\; (\operatorname{basePos}\left(c, v\right) = k))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.exists_basePos_eq` (`✓ std3`). ∎

*Citation.* Ashvin A. Swaminathan and Alexey Sorokin (2026). *ClusterAlgebras: interval and polygon triangulation enumeration*. URL: <https://github.com/AxiomMath/ClusterAlgebras/tree/a9174706bce3bcb0fa342b4614f98ef2acb7f91c>.

*Commentary.*

Exact licensed source support consumed by the complete polygon-count proof. Its source proof body is unchanged.

**Theorem 1.32 (sbtw_iff_val).**

$$\forall m \in Nat,\; [\operatorname{NeZero}\left(m\right)], \forall x \in \operatorname{ZMod}\left(m\right),\; \forall y \in \operatorname{ZMod}\left(m\right),\; \forall z \in \operatorname{ZMod}\left(m\right),\; (\operatorname{sbtw}\left(x, y, z\right) \iff (((\operatorname{val}\left(x\right) < \operatorname{val}\left(y\right)) \land (\operatorname{val}\left(y\right) < \operatorname{val}\left(z\right))) \lor (((\operatorname{val}\left(y\right) < \operatorname{val}\left(z\right)) \land (\operatorname{val}\left(z\right) < \operatorname{val}\left(x\right))) \lor ((\operatorname{val}\left(z\right) < \operatorname{val}\left(x\right)) \land (\operatorname{val}\left(x\right) < \operatorname{val}\left(y\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.sbtw_iff_val` (`✓ std3`). ∎

*Citation.* Ashvin A. Swaminathan and Alexey Sorokin (2026). *ClusterAlgebras: interval and polygon triangulation enumeration*. URL: <https://github.com/AxiomMath/ClusterAlgebras/tree/a9174706bce3bcb0fa342b4614f98ef2acb7f91c>.

*Commentary.*

Exact licensed source support consumed by the complete polygon-count proof. Its source proof body is unchanged.

**Theorem 1.33 (sbtw_iff_sbtw_basePos).**

$$\forall m \in Nat,\; [\operatorname{NeZero}\left(m\right)], \forall c \in \operatorname{ZMod}\left(m\right),\; \forall u \in \operatorname{ZMod}\left(m\right),\; \forall x \in \operatorname{ZMod}\left(m\right),\; \forall v \in \operatorname{ZMod}\left(m\right),\; (\operatorname{sbtw}\left(u, x, v\right) \iff \operatorname{sbtw}\left(\operatorname{basePos}\left(c, u\right), \operatorname{basePos}\left(c, x\right), \operatorname{basePos}\left(c, v\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.sbtw_iff_sbtw_basePos` (`✓ std3`). ∎

*Citation.* Ashvin A. Swaminathan and Alexey Sorokin (2026). *ClusterAlgebras: interval and polygon triangulation enumeration*. URL: <https://github.com/AxiomMath/ClusterAlgebras/tree/a9174706bce3bcb0fa342b4614f98ef2acb7f91c>.

*Commentary.*

Exact licensed source support consumed by the complete polygon-count proof. Its source proof body is unchanged.

**Theorem 1.34 (basePos_add_one).**

$$\forall m \in Nat,\; [\operatorname{NeZero}\left(m\right)], \forall c \in \operatorname{ZMod}\left(m\right),\; \forall u \in \operatorname{ZMod}\left(m\right),\; (\operatorname{basePos}\left(c, (u + 1)\right) = \operatorname{ite}\left(((\operatorname{basePos}\left(c, u\right) + 1) = \operatorname{intCast}\left(m\right)), 0, (\operatorname{basePos}\left(c, u\right) + 1)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.basePos_add_one` (`✓ std3`). ∎

*Citation.* Ashvin A. Swaminathan and Alexey Sorokin (2026). *ClusterAlgebras: interval and polygon triangulation enumeration*. URL: <https://github.com/AxiomMath/ClusterAlgebras/tree/a9174706bce3bcb0fa342b4614f98ef2acb7f91c>.

*Commentary.*

Exact licensed source support consumed by the complete polygon-count proof. Its source proof body is unchanged.

**Theorem 1.35 (basePosSeg_injective).**

$$\forall m \in Nat,\; [\operatorname{NeZero}\left(m\right)], \forall c \in \operatorname{ZMod}\left(m\right),\; \operatorname{Injective}\left(\operatorname{basePosSeg}\left(c\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.basePosSeg_injective` (`✓ std3`). ∎

*Citation.* Ashvin A. Swaminathan and Alexey Sorokin (2026). *ClusterAlgebras: interval and polygon triangulation enumeration*. URL: <https://github.com/AxiomMath/ClusterAlgebras/tree/a9174706bce3bcb0fa342b4614f98ef2acb7f91c>.

*Commentary.*

Exact licensed source support consumed by the complete polygon-count proof. Its source proof body is unchanged.

**Theorem 1.36 (IsSegment.exists_basePos_lt).**

$$\forall m \in Nat,\; [\operatorname{NeZero}\left(m\right)], \forall c \in \operatorname{ZMod}\left(m\right),\; \forall s \in \operatorname{Symtwo}\left(\operatorname{ZMod}\left(m\right)\right),\; (\operatorname{IsSegment}\left(s\right) \implies (\exists u \in \operatorname{ZMod}\left(m\right),\; \exists v \in \operatorname{ZMod}\left(m\right),\; ((s = \operatorname{symPair}\left(u, v\right)) \land (\operatorname{basePos}\left(c, u\right) < \operatorname{basePos}\left(c, v\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.exists_basePos_lt` (`✓ std3`). ∎

*Citation.* Ashvin A. Swaminathan and Alexey Sorokin (2026). *ClusterAlgebras: interval and polygon triangulation enumeration*. URL: <https://github.com/AxiomMath/ClusterAlgebras/tree/a9174706bce3bcb0fa342b4614f98ef2acb7f91c>.

*Commentary.*

Exact licensed source support consumed by the complete polygon-count proof. Its source proof body is unchanged.

**Theorem 1.37 (basePosSeg_mk_of_lt).**

$$\forall m \in Nat,\; \forall c \in \operatorname{ZMod}\left(m\right),\; \forall u \in \operatorname{ZMod}\left(m\right),\; \forall v \in \operatorname{ZMod}\left(m\right),\; ((\operatorname{basePos}\left(c, u\right) < \operatorname{basePos}\left(c, v\right)) \implies (\operatorname{basePosSeg}\left(c, \operatorname{symPair}\left(u, v\right)\right) = \operatorname{pair}\left(\operatorname{basePos}\left(c, u\right), \operatorname{basePos}\left(c, v\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.basePosSeg_mk_of_lt` (`✓ std3`). ∎

*Citation.* Ashvin A. Swaminathan and Alexey Sorokin (2026). *ClusterAlgebras: interval and polygon triangulation enumeration*. URL: <https://github.com/AxiomMath/ClusterAlgebras/tree/a9174706bce3bcb0fa342b4614f98ef2acb7f91c>.

*Commentary.*

Exact licensed source support consumed by the complete polygon-count proof. Its source proof body is unchanged.

**Theorem 1.38 (isSide_mk_iff).**

$$\forall m \in Nat,\; \forall u \in \operatorname{ZMod}\left(m\right),\; \forall v \in \operatorname{ZMod}\left(m\right),\; (\operatorname{IsSide}\left(\operatorname{symPair}\left(u, v\right)\right) \iff ((v = (u + 1)) \lor (u = (v + 1))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.isSide_mk_iff` (`✓ std3`). ∎

*Citation.* Ashvin A. Swaminathan and Alexey Sorokin (2026). *ClusterAlgebras: interval and polygon triangulation enumeration*. URL: <https://github.com/AxiomMath/ClusterAlgebras/tree/a9174706bce3bcb0fa342b4614f98ef2acb7f91c>.

*Commentary.*

Exact licensed source support consumed by the complete polygon-count proof. Its source proof body is unchanged.

**Theorem 1.39 (cross_mk_iff).**

$$\forall m \in Nat,\; \forall u \in \operatorname{ZMod}\left(m\right),\; \forall v \in \operatorname{ZMod}\left(m\right),\; \forall x \in \operatorname{ZMod}\left(m\right),\; \forall y \in \operatorname{ZMod}\left(m\right),\; (\operatorname{Cross}\left(\operatorname{symPair}\left(u, v\right), \operatorname{symPair}\left(x, y\right)\right) \iff ((\operatorname{sbtw}\left(u, x, v\right) \land \operatorname{sbtw}\left(v, y, u\right)) \lor (\operatorname{sbtw}\left(u, y, v\right) \land \operatorname{sbtw}\left(v, x, u\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.cross_mk_iff` (`✓ std3`). ∎

*Citation.* Ashvin A. Swaminathan and Alexey Sorokin (2026). *ClusterAlgebras: interval and polygon triangulation enumeration*. URL: <https://github.com/AxiomMath/ClusterAlgebras/tree/a9174706bce3bcb0fa342b4614f98ef2acb7f91c>.

*Commentary.*

Exact licensed source support consumed by the complete polygon-count proof. Its source proof body is unchanged.

**Theorem 1.40 (cross_mk_iff_basePos).**

$$\forall m \in Nat,\; [\operatorname{NeZero}\left(m\right)], \forall c \in \operatorname{ZMod}\left(m\right),\; \forall u \in \operatorname{ZMod}\left(m\right),\; \forall v \in \operatorname{ZMod}\left(m\right),\; \forall x \in \operatorname{ZMod}\left(m\right),\; \forall y \in \operatorname{ZMod}\left(m\right),\; (\operatorname{Cross}\left(\operatorname{symPair}\left(u, v\right), \operatorname{symPair}\left(x, y\right)\right) \iff ((\operatorname{sbtw}\left(\operatorname{basePos}\left(c, u\right), \operatorname{basePos}\left(c, x\right), \operatorname{basePos}\left(c, v\right)\right) \land \operatorname{sbtw}\left(\operatorname{basePos}\left(c, v\right), \operatorname{basePos}\left(c, y\right), \operatorname{basePos}\left(c, u\right)\right)) \lor (\operatorname{sbtw}\left(\operatorname{basePos}\left(c, u\right), \operatorname{basePos}\left(c, y\right), \operatorname{basePos}\left(c, v\right)\right) \land \operatorname{sbtw}\left(\operatorname{basePos}\left(c, v\right), \operatorname{basePos}\left(c, x\right), \operatorname{basePos}\left(c, u\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.cross_mk_iff_basePos` (`✓ std3`). ∎

*Citation.* Ashvin A. Swaminathan and Alexey Sorokin (2026). *ClusterAlgebras: interval and polygon triangulation enumeration*. URL: <https://github.com/AxiomMath/ClusterAlgebras/tree/a9174706bce3bcb0fa342b4614f98ef2acb7f91c>.

*Commentary.*

Exact licensed source support consumed by the complete polygon-count proof. Its source proof body is unchanged.

**Theorem 1.41 (isSide_mk_iff_basePos).**

$$\forall m \in Nat,\; [\operatorname{NeZero}\left(m\right)], \forall c \in \operatorname{ZMod}\left(m\right),\; \forall u \in \operatorname{ZMod}\left(m\right),\; \forall v \in \operatorname{ZMod}\left(m\right),\; ((\operatorname{basePos}\left(c, u\right) < \operatorname{basePos}\left(c, v\right)) \implies (\operatorname{IsSide}\left(\operatorname{symPair}\left(u, v\right)\right) \iff ((\operatorname{basePos}\left(c, v\right) = (\operatorname{basePos}\left(c, u\right) + 1)) \lor ((\operatorname{basePos}\left(c, u\right) = 0) \land (\operatorname{basePos}\left(c, v\right) = (\operatorname{intCast}\left(m\right) - 1))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.isSide_mk_iff_basePos` (`✓ std3`). ∎

*Citation.* Ashvin A. Swaminathan and Alexey Sorokin (2026). *ClusterAlgebras: interval and polygon triangulation enumeration*. URL: <https://github.com/AxiomMath/ClusterAlgebras/tree/a9174706bce3bcb0fa342b4614f98ef2acb7f91c>.

*Commentary.*

Exact licensed source support consumed by the complete polygon-count proof. Its source proof body is unchanged.

**Theorem 1.42 (bijOn_basePosSeg_isDiagonal).**

$$\forall m \in Nat,\; [\operatorname{NeZero}\left(m\right)], \forall c \in \operatorname{ZMod}\left(m\right),\; \operatorname{BijOn}\left(\operatorname{basePosSeg}\left(c\right), \operatorname{DiagonalSet}\left(m\right), \operatorname{coeSet}\left(\operatorname{D}\left(0, (\operatorname{intCast}\left(m\right) - 1)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.bijOn_basePosSeg_isDiagonal` (`✓ std3`). ∎

*Citation.* Ashvin A. Swaminathan and Alexey Sorokin (2026). *ClusterAlgebras: interval and polygon triangulation enumeration*. URL: <https://github.com/AxiomMath/ClusterAlgebras/tree/a9174706bce3bcb0fa342b4614f98ef2acb7f91c>.

*Commentary.*

Exact licensed source support consumed by the complete polygon-count proof. Its source proof body is unchanged.

**Theorem 1.43 (cross_iff_interleave).**

$$\forall m \in Nat,\; [\operatorname{NeZero}\left(m\right)], \forall c \in \operatorname{ZMod}\left(m\right),\; \forall s \in \operatorname{Symtwo}\left(\operatorname{ZMod}\left(m\right)\right),\; \forall t \in \operatorname{Symtwo}\left(\operatorname{ZMod}\left(m\right)\right),\; (\operatorname{IsSegment}\left(s\right) \implies (\operatorname{IsSegment}\left(t\right) \implies (\operatorname{Cross}\left(s, t\right) \iff \operatorname{Interleave}\left(\operatorname{basePosSeg}\left(c, s\right), \operatorname{basePosSeg}\left(c, t\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.cross_iff_interleave` (`✓ std3`). ∎

*Citation.* Ashvin A. Swaminathan and Alexey Sorokin (2026). *ClusterAlgebras: interval and polygon triangulation enumeration*. URL: <https://github.com/AxiomMath/ClusterAlgebras/tree/a9174706bce3bcb0fa342b4614f98ef2acb7f91c>.

*Commentary.*

Exact licensed source support consumed by the complete polygon-count proof. Its source proof body is unchanged.

**Theorem 1.44 (bijOn_basePosTri).**

$$\forall m \in Nat,\; [\operatorname{NeZero}\left(m\right)], \forall c \in \operatorname{ZMod}\left(m\right),\; \operatorname{BijOn}\left(\operatorname{basePosTri}\left(c\right), \operatorname{PolygonTriSet}\left(m\right), \operatorname{IntervalTriSet}\left(0, (\operatorname{intCast}\left(m\right) - 1)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.bijOn_basePosTri` (`✓ std3`). ∎

*Citation.* Ashvin A. Swaminathan and Alexey Sorokin (2026). *ClusterAlgebras: interval and polygon triangulation enumeration*. URL: <https://github.com/AxiomMath/ClusterAlgebras/tree/a9174706bce3bcb0fa342b4614f98ef2acb7f91c>.

*Commentary.*

Exact licensed source support consumed by the complete polygon-count proof. Its source proof body is unchanged.

**Theorem 1.45 (encard_setOf_isTriangulation).**

$$\forall m \in Nat,\; [\operatorname{NeZero}\left(m\right)], ((3 \leq m) \implies (\operatorname{ENatcard}\left(\operatorname{A}\left(m\right)\right) = \operatorname{coeENat}\left(\operatorname{catalanNumber}\left((m - 2)\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.encard_setOf_isTriangulation` (`✓ std3`). ∎

*Citation.* Ashvin A. Swaminathan and Alexey Sorokin (2026). *ClusterAlgebras: interval and polygon triangulation enumeration*. URL: <https://github.com/AxiomMath/ClusterAlgebras/tree/a9174706bce3bcb0fa342b4614f98ef2acb7f91c>.

*Commentary.*

Exact licensed source support consumed by the complete polygon-count proof. Its source proof body is unchanged.

## References

- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.basePosSeg_injective`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.basePosSeg_mk`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.basePosSeg_mk_of_lt`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.basePos_add_one`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.basePos_eq_ite`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.basePos_injective`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.basePos_lt`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.basePos_nonneg`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.bijOn_basePosSeg_isDiagonal`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.bijOn_basePosTri`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.bounds_of_mem_intervalSegments`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.card_subtype_isIntervalTriangulation`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.catalanNumber_succ`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.catalanNumber_zero`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.cross_iff_interleave`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.cross_mk_iff`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.cross_mk_iff_basePos`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.encard_setOf_isTriangulation`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.eq_union_of_apex`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.existsUnique_apex`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.exists_basePos_eq`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.exists_basePos_lt`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.exists_equiv_intervalTriangulation`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.exists_interleave`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.inter_left_of_apex`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.inter_right_of_apex`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.intervalTriangulationCount_eq_catalanNumber`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.intervalTriangulationCount_eq_sum`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.intervalTriangulationCount_self_add_one`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.isSide_mk_iff`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.isSide_mk_iff_basePos`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.le_or_le_of_apex`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.mem_intervalTriangulations`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.mk_mem_intervalDiagonals_iff`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.mk_mem_intervalSides_iff`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.mk_mem_union_intervalDiagonals_iff`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.not_interleave`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.not_interleave_of_mem_intervalSides`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.sbtw_iff_sbtw_basePos`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.sbtw_iff_val`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.symm`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.union`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.union_apex_mem_intervalSegments`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.union_inter_intervalDiagonals_left`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCatalanSupplier.union_inter_intervalDiagonals_right`
