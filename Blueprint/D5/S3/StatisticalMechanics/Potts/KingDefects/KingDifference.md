# One-defect king colourings: KingDifference

## Abstract

Finite colourings with exactly one monochromatic king bond.

**Definition 1.1 (The additive Klein four group).**

$$\operatorname{KingDifference}.\operatorname{K} = (\operatorname{ZMod}\left(2\right)) \times (\operatorname{ZMod}\left(2\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingDifference.K` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

Addition is componentwise modulo two; every element is its own additive inverse.

**Definition 1.2 (Ordered distinct nonzero colours).**

$$\operatorname{KingDifference}.\operatorname{NZPair} = \{pq: (\operatorname{KingDifference}.\operatorname{K}) \times (\operatorname{KingDifference}.\operatorname{K}) // ((\operatorname{Prod}.\operatorname{fst}\left(pq\right) \ne 0) \land ((\operatorname{Prod}.\operatorname{snd}\left(pq\right) \ne 0) \land (\operatorname{Prod}.\operatorname{fst}\left(pq\right) \ne \operatorname{Prod}.\operatorname{snd}\left(pq\right))))\}$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingDifference.NZPair` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

Choose two different nonzero colours, retaining their order.

**Theorem 1.3 (Six ordered colour pairs).**

$$\operatorname{Nat}.\operatorname{card}\left(\operatorname{KingDifference}.\operatorname{NZPair}\right) = 6$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingDifference.nz_pair_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

The three nonzero colours give three choices for the first entry and two for the second.

**Theorem 1.4 (Zero sums identify equal colours).**

$$\forall (a: \operatorname{KingDifference}.\operatorname{K}), (\forall (b: \operatorname{KingDifference}.\operatorname{K}), (((a) + (b) = 0) \Leftrightarrow (a = b)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingDifference.add_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

Since each colour is its own additive inverse, two colours have zero sum exactly when they agree.

**Definition 1.5 (Horizontal and vertical differences).**

$$\forall (N: \operatorname{Nat}), (\forall (M: \operatorname{Nat}), (((\operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{mk}: ((\operatorname{Fin}\left((N) + (1)\right)) \to ((\operatorname{Fin}\left(M\right)) \to (\operatorname{KingDifference}.\operatorname{K}))) \to (((\operatorname{Fin}\left(N\right)) \to ((\operatorname{Fin}\left((M) + (1)\right)) \to (\operatorname{KingDifference}.\operatorname{K}))) \to (\operatorname{KingDifference}.\operatorname{DiffField}\left(N, M\right))))) \land (((\operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{h}: (\operatorname{KingDifference}.\operatorname{DiffField}\left(N, M\right)) \to ((\operatorname{Fin}\left((N) + (1)\right)) \to ((\operatorname{Fin}\left(M\right)) \to (\operatorname{KingDifference}.\operatorname{K}))))) \land ((\operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{v}: (\operatorname{KingDifference}.\operatorname{DiffField}\left(N, M\right)) \to ((\operatorname{Fin}\left(N\right)) \to ((\operatorname{Fin}\left((M) + (1)\right)) \to (\operatorname{KingDifference}.\operatorname{K}))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingDifference.DiffField` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

The record has fields h and v of the displayed types. They assign differences to horizontal and vertical bonds, respectively.

**Definition 1.6 (Compatibility around every square).**

$$\forall (N: \operatorname{Nat}), (\forall (M: \operatorname{Nat}), (\forall (s: \operatorname{KingDifference}.\operatorname{DiffField}\left(N, M\right)), ((\operatorname{KingDifference}.\operatorname{Cocycle}\left(s\right)) \Leftrightarrow (\forall (i: \operatorname{Fin}\left(N\right)), (\forall (j: \operatorname{Fin}\left(M\right)), ((\operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{h}\left(s, \operatorname{Fin}.\operatorname{castSucc}\left(i\right), j\right)) + (\operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{v}\left(s, i, \operatorname{Fin}.\operatorname{succ}\left(j\right)\right)) = (\operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{v}\left(s, i, \operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right)) + (\operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{h}\left(s, \operatorname{Fin}.\operatorname{succ}\left(i\right), j\right))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingDifference.Cocycle` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

The two sums along the two-step paths across each elementary square agree.

**Definition 1.7 (Take adjacent colour differences).**

$$\forall (N: \operatorname{Nat}), (\forall (M: \operatorname{Nat}), (\forall (f: (\operatorname{KingGrid}.\operatorname{Cell}\left((N) + (1), (M) + (1)\right)) \to (\operatorname{KingDifference}.\operatorname{K})), ((\forall (i: \operatorname{Fin}\left((N) + (1)\right)), (\forall (j: \operatorname{Fin}\left(M\right)), (\operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{h}\left(\operatorname{KingDifference}.\operatorname{differentiate}\left(f\right), i, j\right) = (f\left((i, \operatorname{Fin}.\operatorname{castSucc}\left(j\right))\right)) + (f\left((i, \operatorname{Fin}.\operatorname{succ}\left(j\right))\right))))) \land (\forall (i: \operatorname{Fin}\left(N\right)), (\forall (j: \operatorname{Fin}\left((M) + (1)\right)), (\operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{v}\left(\operatorname{KingDifference}.\operatorname{differentiate}\left(f\right), i, j\right) = (f\left((\operatorname{Fin}.\operatorname{castSucc}\left(i\right), j)\right)) + (f\left((\operatorname{Fin}.\operatorname{succ}\left(i\right), j)\right))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingDifference.differentiate` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

Over this group, a difference is the sum of the endpoint colours.

**Definition 1.8 (Integrate from a root colour).**

$$\forall (N: \operatorname{Nat}), (\forall (M: \operatorname{Nat}), (\forall (t: \operatorname{KingDifference}.\operatorname{K}), (\forall (s: \operatorname{KingDifference}.\operatorname{DiffField}\left(N, M\right)), (\forall (p: \operatorname{KingGrid}.\operatorname{Cell}\left((N) + (1), (M) + (1)\right)), (\operatorname{KingDifference}.\operatorname{integrate}\left(t, s\right)\left(p\right) = ((t) + (\operatorname{Fin}.\operatorname{partialSum}\left((\lambda (i: \operatorname{Fin}\left(N\right)) \mapsto \operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{v}\left(s, i, 0\right)), \operatorname{Prod}.\operatorname{fst}\left(p\right)\right))) + (\operatorname{Fin}.\operatorname{partialSum}\left(\operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{h}\left(s, \operatorname{Prod}.\operatorname{fst}\left(p\right)\right), \operatorname{Prod}.\operatorname{snd}\left(p\right)\right)))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingDifference.integrate` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

Starting with root colour t, the path goes down column zero and then across the target row. Fin.partialSum adds entries strictly before the indicated endpoint.

**Theorem 1.9 (Recover a compatible difference field).**

$$\forall (N: \operatorname{Nat}), (\forall (M: \operatorname{Nat}), (\forall (t: \operatorname{KingDifference}.\operatorname{K}), (\forall (s: \operatorname{KingDifference}.\operatorname{DiffField}\left(N, M\right)), ((\operatorname{KingDifference}.\operatorname{Cocycle}\left(s\right)) \Rightarrow (\operatorname{KingDifference}.\operatorname{differentiate}\left(\operatorname{KingDifference}.\operatorname{integrate}\left(t, s\right)\right) = s)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingDifference.differentiate_integrate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

Compatibility around squares makes the path integral recover every horizontal and vertical difference. The consumed private helper psum_add obtains partial-sum additivity directly from List.sum_map_add after unfolding Fin.partialSum.

**Definition 1.10 (Differences on all four orientations).**

$$\forall (N: \operatorname{Nat}), (\forall (M: \operatorname{Nat}), (\forall (s: \operatorname{KingDifference}.\operatorname{DiffField}\left(N, M\right)), ((\forall (i: \operatorname{Fin}\left((N) + (1)\right)), (\forall (j: \operatorname{Fin}\left(M\right)), (\operatorname{KingDifference}.\operatorname{edgeValue}\left(s, \operatorname{KingGrid}.\operatorname{Edge}.\operatorname{H}\left(i, j\right)\right) = \operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{h}\left(s, i, j\right)))) \land ((\forall (i: \operatorname{Fin}\left(N\right)), (\forall (j: \operatorname{Fin}\left((M) + (1)\right)), (\operatorname{KingDifference}.\operatorname{edgeValue}\left(s, \operatorname{KingGrid}.\operatorname{Edge}.\operatorname{V}\left(i, j\right)\right) = \operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{v}\left(s, i, j\right)))) \land ((\forall (i: \operatorname{Fin}\left(N\right)), (\forall (j: \operatorname{Fin}\left(M\right)), (\operatorname{KingDifference}.\operatorname{edgeValue}\left(s, \operatorname{KingGrid}.\operatorname{Edge}.\operatorname{D}\left(i, j\right)\right) = (\operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{h}\left(s, \operatorname{Fin}.\operatorname{castSucc}\left(i\right), j\right)) + (\operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{v}\left(s, i, \operatorname{Fin}.\operatorname{succ}\left(j\right)\right))))) \land (\forall (i: \operatorname{Fin}\left(N\right)), (\forall (j: \operatorname{Fin}\left(M\right)), (\operatorname{KingDifference}.\operatorname{edgeValue}\left(s, \operatorname{KingGrid}.\operatorname{Edge}.\operatorname{A}\left(i, j\right)\right) = (\operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{h}\left(s, \operatorname{Fin}.\operatorname{castSucc}\left(i\right), j\right)) + (\operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{v}\left(s, i, \operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right))))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingDifference.edgeValue` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

Diagonal differences are sums of two adjacent differences along a two-step path.

**Definition 1.11 (A compatible field with a single zero bond).**

$$\forall (N: \operatorname{Nat}), (\forall (M: \operatorname{Nat}), (\forall (e: \operatorname{KingGrid}.\operatorname{Edge}\left((N) + (1), (M) + (1)\right)), (\forall (s: \operatorname{KingDifference}.\operatorname{DiffField}\left(N, M\right)), ((\operatorname{KingDifference}.\operatorname{RawAdmissible}\left(e, s\right)) \Leftrightarrow ((\operatorname{KingDifference}.\operatorname{Cocycle}\left(s\right)) \land (\forall (d: \operatorname{KingGrid}.\operatorname{Edge}\left((N) + (1), (M) + (1)\right)), ((\operatorname{KingDifference}.\operatorname{edgeValue}\left(s, d\right) = 0) \Leftrightarrow (d = e))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingDifference.RawAdmissible` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

The field is compatible and precisely the selected bond has zero difference.

**Theorem 1.12 (Zero differences are monochromatic bonds).**

$$\forall (N: \operatorname{Nat}), (\forall (M: \operatorname{Nat}), (\forall (f: (\operatorname{KingGrid}.\operatorname{Cell}\left((N) + (1), (M) + (1)\right)) \to (\operatorname{KingDifference}.\operatorname{K})), (\forall (e: \operatorname{KingGrid}.\operatorname{Edge}\left((N) + (1), (M) + (1)\right)), ((\operatorname{KingDifference}.\operatorname{RawAdmissible}\left(e, \operatorname{KingDifference}.\operatorname{differentiate}\left(f\right)\right)) \Leftrightarrow (\operatorname{KingGrid}.\operatorname{DefectAt}\left(e, f\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingDifference.raw_differentiate_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

Differentiation translates exactly one monochromatic bond into exactly one zero difference.

**Definition 1.13 (Separate root colour from differences).**

$$\forall (N: \operatorname{Nat}), (\forall (M: \operatorname{Nat}), (\forall (e: \operatorname{KingGrid}.\operatorname{Edge}\left((N) + (1), (M) + (1)\right)), (((\operatorname{KingDifference}.\operatorname{defectIntegrationEquiv}\left(e\right): \operatorname{Equiv}\left(\{f: (\operatorname{KingGrid}.\operatorname{Cell}\left((N) + (1), (M) + (1)\right)) \to (\operatorname{KingDifference}.\operatorname{K}) // (\operatorname{KingGrid}.\operatorname{DefectAt}\left(e, f\right))\}, (\operatorname{KingDifference}.\operatorname{K}) \times (\{s: \operatorname{KingDifference}.\operatorname{DiffField}\left(N, M\right) // (\operatorname{KingDifference}.\operatorname{RawAdmissible}\left(e, s\right))\})\right))) \land (\forall (f: \{f: (\operatorname{KingGrid}.\operatorname{Cell}\left((N) + (1), (M) + (1)\right)) \to (\operatorname{KingDifference}.\operatorname{K}) // (\operatorname{KingGrid}.\operatorname{DefectAt}\left(e, f\right))\}), ((\operatorname{Prod}.\operatorname{fst}\left(\operatorname{KingDifference}.\operatorname{defectIntegrationEquiv}\left(e\right)\left(f\right)\right) = \operatorname{Subtype}.\operatorname{val}\left(f\right)\left((0, 0)\right)) \land (\operatorname{Subtype}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{KingDifference}.\operatorname{defectIntegrationEquiv}\left(e\right)\left(f\right)\right)\right) = \operatorname{KingDifference}.\operatorname{differentiate}\left(\operatorname{Subtype}.\operatorname{val}\left(f\right)\right)))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingDifference.defectIntegrationEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

A colouring is determined by its root colour and admissible difference field. The inverse integrates the field from that root.

**Definition 1.14 (Count admissible fields for a fixed bond).**

$$\forall (N: \operatorname{Nat}), (\forall (M: \operatorname{Nat}), (\forall (e: \operatorname{KingGrid}.\operatorname{Edge}\left((N) + (1), (M) + (1)\right)), (\operatorname{KingDifference}.\operatorname{N_{e}}\left(e\right) = \operatorname{Nat}.\operatorname{card}\left(\{s: \operatorname{KingDifference}.\operatorname{DiffField}\left(N, M\right) // (\operatorname{KingDifference}.\operatorname{RawAdmissible}\left(e, s\right))\}\right))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingDifference.N_e` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

This is also the number of colourings with the prescribed defect and root colour zero.

**Theorem 1.15 (Four choices of root colour).**

$$\forall (N: \operatorname{Nat}), (\forall (M: \operatorname{Nat}), (\forall (e: \operatorname{KingGrid}.\operatorname{Edge}\left((N) + (1), (M) + (1)\right)), (\operatorname{Nat}.\operatorname{card}\left(\{f: (\operatorname{KingGrid}.\operatorname{Cell}\left((N) + (1), (M) + (1)\right)) \to (\operatorname{Fin}\left(4\right)) // (\operatorname{KingGrid}.\operatorname{DefectAt}\left(e, f\right))\}\right) = (4) \cdot (\operatorname{KingDifference}.\operatorname{N_{e}}\left(e\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingDifference.count_fixed_edge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

After identifying the four colours with the Klein four group, the root colour has four independent choices.

**Definition 1.16 (A square avoids the defective bond).**

$$\forall (N: \operatorname{Nat}), (\forall (M: \operatorname{Nat}), (\forall (e: \operatorname{KingGrid}.\operatorname{Edge}\left((N) + (1), (M) + (1)\right)), (\forall (i: \operatorname{Fin}\left(N\right)), (\forall (j: \operatorname{Fin}\left(M\right)), ((\operatorname{KingDifference}.\operatorname{BlockAvoids}\left(e, i, j\right)) \Leftrightarrow ((\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{H}\left(\operatorname{Fin}.\operatorname{castSucc}\left(i\right), j\right) \ne e) \land ((\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{V}\left(i, \operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right) \ne e) \land ((\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{D}\left(i, j\right) \ne e) \land ((\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{A}\left(i, j\right) \ne e) \land ((\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{V}\left(i, \operatorname{Fin}.\operatorname{succ}\left(j\right)\right) \ne e) \land (\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{H}\left(\operatorname{Fin}.\operatorname{succ}\left(i\right), j\right) \ne e)))))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingDifference.BlockAvoids` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

None of the square's four side bonds or two diagonal bonds is the selected defect.

**Theorem 1.17 (Opposite differences agree away from the defect).**

$$\forall (N: \operatorname{Nat}), (\forall (M: \operatorname{Nat}), (\forall (e: \operatorname{KingGrid}.\operatorname{Edge}\left((N) + (1), (M) + (1)\right)), (\forall (s: \operatorname{KingDifference}.\operatorname{DiffField}\left(N, M\right)), ((\operatorname{KingDifference}.\operatorname{RawAdmissible}\left(e, s\right)) \Rightarrow (\forall (i: \operatorname{Fin}\left(N\right)), (\forall (j: \operatorname{Fin}\left(M\right)), ((\operatorname{KingDifference}.\operatorname{BlockAvoids}\left(e, i, j\right)) \Rightarrow ((\operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{h}\left(s, \operatorname{Fin}.\operatorname{castSucc}\left(i\right), j\right) = \operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{h}\left(s, \operatorname{Fin}.\operatorname{succ}\left(i\right), j\right)) \land ((\operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{v}\left(s, i, \operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right) = \operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{v}\left(s, i, \operatorname{Fin}.\operatorname{succ}\left(j\right)\right)) \land ((\operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{h}\left(s, \operatorname{Fin}.\operatorname{castSucc}\left(i\right), j\right) \ne 0) \land ((\operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{v}\left(s, i, \operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right) \ne 0) \land (\operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{h}\left(s, \operatorname{Fin}.\operatorname{castSucc}\left(i\right), j\right) \ne \operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{v}\left(s, i, \operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right)))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingDifference.goodBlock_of_raw` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

A defect-free square is rainbow. Its opposite differences agree, and its horizontal and vertical differences are nonzero and distinct.

**Theorem 1.18 (Constant horizontal slots).**

$$\forall (N: \operatorname{Nat}), (\forall (M: \operatorname{Nat}), (\forall (e: \operatorname{KingGrid}.\operatorname{Edge}\left((N) + (1), (M) + (1)\right)), (\forall (s: \operatorname{KingDifference}.\operatorname{DiffField}\left(N, M\right)), ((\operatorname{KingDifference}.\operatorname{RawAdmissible}\left(e, s\right)) \Rightarrow (\forall (j: \operatorname{Fin}\left(M\right)), (\forall (a: \operatorname{Fin}\left((N) + (1)\right)), (\forall (b: \operatorname{Fin}\left((N) + (1)\right)), ((a \le b) \Rightarrow ((\forall (i: \operatorname{Fin}\left(N\right)), ((\operatorname{Fin}.\operatorname{val}\left(a\right) \le \operatorname{Fin}.\operatorname{val}\left(i\right)) \Rightarrow ((\operatorname{Fin}.\operatorname{val}\left(i\right) < \operatorname{Fin}.\operatorname{val}\left(b\right)) \Rightarrow (\operatorname{KingDifference}.\operatorname{BlockAvoids}\left(e, i, j\right))))) \Rightarrow (\operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{h}\left(s, a, j\right) = \operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{h}\left(s, b, j\right)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingDifference.horizontal_slot_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

Agreement of opposite differences propagates through every intervening square that avoids the selected defect.

**Theorem 1.19 (Constant vertical slots).**

$$\forall (N: \operatorname{Nat}), (\forall (M: \operatorname{Nat}), (\forall (e: \operatorname{KingGrid}.\operatorname{Edge}\left((N) + (1), (M) + (1)\right)), (\forall (s: \operatorname{KingDifference}.\operatorname{DiffField}\left(N, M\right)), ((\operatorname{KingDifference}.\operatorname{RawAdmissible}\left(e, s\right)) \Rightarrow (\forall (i: \operatorname{Fin}\left(N\right)), (\forall (a: \operatorname{Fin}\left((M) + (1)\right)), (\forall (b: \operatorname{Fin}\left((M) + (1)\right)), ((a \le b) \Rightarrow ((\forall (j: \operatorname{Fin}\left(M\right)), ((\operatorname{Fin}.\operatorname{val}\left(a\right) \le \operatorname{Fin}.\operatorname{val}\left(j\right)) \Rightarrow ((\operatorname{Fin}.\operatorname{val}\left(j\right) < \operatorname{Fin}.\operatorname{val}\left(b\right)) \Rightarrow (\operatorname{KingDifference}.\operatorname{BlockAvoids}\left(e, i, j\right))))) \Rightarrow (\operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{v}\left(s, i, a\right) = \operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{v}\left(s, i, b\right)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingDifference.vertical_slot_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

Agreement of opposite differences propagates through every intervening square that avoids the selected defect.

**Definition 1.20 (Sum over horizontal defect positions).**

$$\forall (N: \operatorname{Nat}), (\forall (M: \operatorname{Nat}), (\operatorname{KingDifference}.\operatorname{N_{H}}\left(N, M\right) = \sum_{i: \operatorname{Fin}\left((N) + (1)\right)} (\sum_{j: \operatorname{Fin}\left(M\right)} (\operatorname{KingDifference}.\operatorname{N_{e}}\left(\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{H}\left(i, j\right)\right)))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingDifference.N_H` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

The summands count admissible fields for each defect position of this orientation.

**Definition 1.21 (Sum over descending diagonal defect positions).**

$$\forall (N: \operatorname{Nat}), (\forall (M: \operatorname{Nat}), (\operatorname{KingDifference}.\operatorname{N_{D}}\left(N, M\right) = \sum_{i: \operatorname{Fin}\left(N\right)} (\sum_{j: \operatorname{Fin}\left(M\right)} (\operatorname{KingDifference}.\operatorname{N_{e}}\left(\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{D}\left(i, j\right)\right)))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingDifference.N_D` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

The summands count admissible fields for each defect position of this orientation.

**Theorem 1.22 (Count by orientation and remove colour labels).**

$$\forall (N: \operatorname{Nat}), (\forall (M: \operatorname{Nat}), ((1 \le N) \Rightarrow ((1 \le M) \Rightarrow (((\operatorname{KingDifference}.\operatorname{N_{H}}\left(N, M\right)) + (\operatorname{KingDifference}.\operatorname{N_{H}}\left(M, N\right))) + ((2) \cdot (\operatorname{KingDifference}.\operatorname{N_{D}}\left(N, M\right))) = (6) \cdot (\operatorname{KingGrid}.\operatorname{T}\left((N) + (1), (M) + (1)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingDifference.count_by_kind` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

Transposition identifies vertical with horizontal positions and reflection identifies the two diagonal orientations. Four root colours and twenty-four colour permutations leave a factor of six.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingDifference.BlockAvoids`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingDifference.Cocycle`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingDifference.DiffField`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingDifference.K`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingDifference.NZPair`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingDifference.N_D`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingDifference.N_H`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingDifference.N_e`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingDifference.RawAdmissible`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingDifference.add_eq_zero`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingDifference.count_by_kind`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingDifference.count_fixed_edge`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingDifference.defectIntegrationEquiv`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingDifference.differentiate`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingDifference.differentiate_integrate`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingDifference.edgeValue`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingDifference.goodBlock_of_raw`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingDifference.horizontal_slot_eq`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingDifference.integrate`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingDifference.nz_pair_card`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingDifference.raw_differentiate_iff`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingDifference.vertical_slot_eq`
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid](KingGrid.md)
