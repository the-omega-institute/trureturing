# One-defect king colourings: KingGrid

## Abstract

Finite colourings with exactly one monochromatic king bond.

**Definition 1.1 (Cells of the rectangle).**

$$\forall (n: \operatorname{Nat}), (\forall (k: \operatorname{Nat}), (\operatorname{KingGrid}.\operatorname{Cell}\left(n, k\right) = (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(k\right))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid.Cell` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

A cell consists of a row and a column, both indexed from zero.

**Definition 1.2 (The four kinds of king bonds).**

$$\forall (n: \operatorname{Nat}), (\forall (k: \operatorname{Nat}), (((\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{H}: (\operatorname{Fin}\left(n\right)) \to ((\operatorname{Fin}\left((k) - (1)\right)) \to (\operatorname{KingGrid}.\operatorname{Edge}\left(n, k\right))))) \land (((\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{V}: (\operatorname{Fin}\left((n) - (1)\right)) \to ((\operatorname{Fin}\left(k\right)) \to (\operatorname{KingGrid}.\operatorname{Edge}\left(n, k\right))))) \land (((\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{D}: (\operatorname{Fin}\left((n) - (1)\right)) \to ((\operatorname{Fin}\left((k) - (1)\right)) \to (\operatorname{KingGrid}.\operatorname{Edge}\left(n, k\right))))) \land ((\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{A}: (\operatorname{Fin}\left((n) - (1)\right)) \to ((\operatorname{Fin}\left((k) - (1)\right)) \to (\operatorname{KingGrid}.\operatorname{Edge}\left(n, k\right)))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid.Edge` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

The four disjoint constructors list horizontal, vertical, descending diagonal and ascending diagonal bonds. Their parameters enumerate each undirected bond once.

**Definition 1.3 (Left-slot endpoint index).**

$$\forall (n: \operatorname{Nat}), (\forall (i: \operatorname{Fin}\left((n) - (1)\right)), (\operatorname{KingGrid}.\operatorname{lo}\left(i\right) = \operatorname{QuandleMarkovColoring}.\operatorname{leftSlot}\left(i\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid.lo` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

This endpoint uses QuandleMarkovColoring.leftSlot: its value is i.val in the longer finite interval.

**Definition 1.4 (Right-slot endpoint index).**

$$\forall (n: \operatorname{Nat}), (\forall (i: \operatorname{Fin}\left((n) - (1)\right)), (\operatorname{KingGrid}.\operatorname{hi}\left(i\right) = \operatorname{QuandleMarkovColoring}.\operatorname{rightSlot}\left(i\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid.hi` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

This endpoint uses QuandleMarkovColoring.rightSlot: its value is i.val+1 in the longer finite interval. The theorem QuandleMarkovColoring.slots_ne separates the two coordinates and hence the two endpoints of every king bond.

**Definition 1.5 (First endpoints).**

$$\forall (n: \operatorname{Nat}), (\forall (k: \operatorname{Nat}), ((\forall (i: \operatorname{Fin}\left(n\right)), (\forall (j: \operatorname{Fin}\left((k) - (1)\right)), (\operatorname{KingGrid}.\operatorname{end0}\left(\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{H}\left(i, j\right)\right) = (i, \operatorname{KingGrid}.\operatorname{lo}\left(j\right))))) \land ((\forall (i: \operatorname{Fin}\left((n) - (1)\right)), (\forall (j: \operatorname{Fin}\left(k\right)), (\operatorname{KingGrid}.\operatorname{end0}\left(\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{V}\left(i, j\right)\right) = (\operatorname{KingGrid}.\operatorname{lo}\left(i\right), j)))) \land ((\forall (i: \operatorname{Fin}\left((n) - (1)\right)), (\forall (j: \operatorname{Fin}\left((k) - (1)\right)), (\operatorname{KingGrid}.\operatorname{end0}\left(\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{D}\left(i, j\right)\right) = (\operatorname{KingGrid}.\operatorname{lo}\left(i\right), \operatorname{KingGrid}.\operatorname{lo}\left(j\right))))) \land (\forall (i: \operatorname{Fin}\left((n) - (1)\right)), (\forall (j: \operatorname{Fin}\left((k) - (1)\right)), (\operatorname{KingGrid}.\operatorname{end0}\left(\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{A}\left(i, j\right)\right) = (\operatorname{KingGrid}.\operatorname{lo}\left(i\right), \operatorname{KingGrid}.\operatorname{hi}\left(j\right)))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid.end0` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

These endpoint formulas specify the two cells incident to each bond.

**Definition 1.6 (Second endpoints).**

$$\forall (n: \operatorname{Nat}), (\forall (k: \operatorname{Nat}), ((\forall (i: \operatorname{Fin}\left(n\right)), (\forall (j: \operatorname{Fin}\left((k) - (1)\right)), (\operatorname{KingGrid}.\operatorname{end1}\left(\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{H}\left(i, j\right)\right) = (i, \operatorname{KingGrid}.\operatorname{hi}\left(j\right))))) \land ((\forall (i: \operatorname{Fin}\left((n) - (1)\right)), (\forall (j: \operatorname{Fin}\left(k\right)), (\operatorname{KingGrid}.\operatorname{end1}\left(\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{V}\left(i, j\right)\right) = (\operatorname{KingGrid}.\operatorname{hi}\left(i\right), j)))) \land ((\forall (i: \operatorname{Fin}\left((n) - (1)\right)), (\forall (j: \operatorname{Fin}\left((k) - (1)\right)), (\operatorname{KingGrid}.\operatorname{end1}\left(\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{D}\left(i, j\right)\right) = (\operatorname{KingGrid}.\operatorname{hi}\left(i\right), \operatorname{KingGrid}.\operatorname{hi}\left(j\right))))) \land (\forall (i: \operatorname{Fin}\left((n) - (1)\right)), (\forall (j: \operatorname{Fin}\left((k) - (1)\right)), (\operatorname{KingGrid}.\operatorname{end1}\left(\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{A}\left(i, j\right)\right) = (\operatorname{KingGrid}.\operatorname{hi}\left(i\right), \operatorname{KingGrid}.\operatorname{lo}\left(j\right)))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid.end1` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

These endpoint formulas specify the two cells incident to each bond.

**Definition 1.7 (Monochromatic bonds).**

$$\forall (n: \operatorname{Nat}), (\forall (k: \operatorname{Nat}), (\forall (C: \operatorname{Type}), (\forall (f: (\operatorname{KingGrid}.\operatorname{Cell}\left(n, k\right)) \to (C)), (\forall (e: \operatorname{KingGrid}.\operatorname{Edge}\left(n, k\right)), ((\operatorname{KingGrid}.\operatorname{mono}\left(f, e\right)) \Leftrightarrow (f\left(\operatorname{KingGrid}.\operatorname{end0}\left(e\right)\right) = f\left(\operatorname{KingGrid}.\operatorname{end1}\left(e\right)\right)))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid.mono` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

A bond is monochromatic when its two endpoints have equal colours.

**Definition 1.8 (Exactly one monochromatic bond).**

$$\forall (n: \operatorname{Nat}), (\forall (k: \operatorname{Nat}), (\forall (C: \operatorname{Type}), ([\operatorname{DecidableEq}\left(C\right)], \forall (f: (\operatorname{KingGrid}.\operatorname{Cell}\left(n, k\right)) \to (C)), ((\operatorname{KingGrid}.\operatorname{OneDefect}\left(f\right)) \Leftrightarrow (\operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((\lambda (e: \operatorname{KingGrid}.\operatorname{Edge}\left(n, k\right)) \mapsto \operatorname{KingGrid}.\operatorname{mono}\left(f, e\right)), (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left(\operatorname{KingGrid}.\operatorname{Edge}\left(n, k\right)\right))\right)\right) = 1)))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid.OneDefect` (`✓ std3`).

*Citation.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

The predicate counts monochromatic bonds in all four directions and requires exactly one.

**Definition 1.9 (A prescribed defect).**

$$\forall (n: \operatorname{Nat}), (\forall (k: \operatorname{Nat}), (\forall (C: \operatorname{Type}), (\forall (e: \operatorname{KingGrid}.\operatorname{Edge}\left(n, k\right)), (\forall (f: (\operatorname{KingGrid}.\operatorname{Cell}\left(n, k\right)) \to (C)), ((\operatorname{KingGrid}.\operatorname{DefectAt}\left(e, f\right)) \Leftrightarrow (\forall (d: \operatorname{KingGrid}.\operatorname{Edge}\left(n, k\right)), ((\operatorname{KingGrid}.\operatorname{mono}\left(f, d\right)) \Leftrightarrow (d = e))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid.DefectAt` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

Exactly the selected bond is monochromatic.

**Definition 1.10 (Row-major first appearances).**

$$\forall (n: \operatorname{Nat}), (\forall (k: \operatorname{Nat}), (\forall (f: (\operatorname{KingGrid}.\operatorname{Cell}\left(n, k\right)) \to (\operatorname{Fin}\left(4\right))), ((\operatorname{KingGrid}.\operatorname{normal}\left(f\right)) \Leftrightarrow (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177Canonical}.\operatorname{Canonical}\left((\lambda (i: \operatorname{Fin}\left((n) \cdot (k)\right)) \mapsto f\left(\operatorname{Equiv}.\operatorname{symm}\left(\operatorname{finProdFinEquiv}\right)\left(i\right)\right))\right)))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid.normal` (`✓ std3`).

*Citation.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

Flattening uses the ordinal i*k+j. The canonical word introduces smaller colour labels before larger labels, which is precisely row-major first-appearance order.

**Definition 1.11 (Labelled one-defect colourings).**

$$\forall (n: \operatorname{Nat}), (\forall (k: \operatorname{Nat}), (\operatorname{KingGrid}.\operatorname{L}\left(n, k\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((\lambda (f: (\operatorname{KingGrid}.\operatorname{Cell}\left(n, k\right)) \to (\operatorname{Fin}\left(4\right))) \mapsto \operatorname{KingGrid}.\operatorname{OneDefect}\left(f\right)), (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left((\operatorname{KingGrid}.\operatorname{Cell}\left(n, k\right)) \to (\operatorname{Fin}\left(4\right))\right))\right)\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid.L` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

The finite filter ranges over all four-colour arrays. Colour names remain distinct.

**Definition 1.12 (Canonical one-defect colourings).**

$$\forall (n: \operatorname{Nat}), (\forall (k: \operatorname{Nat}), (\operatorname{KingGrid}.\operatorname{T}\left(n, k\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((\lambda (f: (\operatorname{KingGrid}.\operatorname{Cell}\left(n, k\right)) \to (\operatorname{Fin}\left(4\right))) \mapsto (\operatorname{KingGrid}.\operatorname{OneDefect}\left(f\right)) \land (\operatorname{KingGrid}.\operatorname{normal}\left(f\right))), (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left((\operatorname{KingGrid}.\operatorname{Cell}\left(n, k\right)) \to (\operatorname{Fin}\left(4\right))\right))\right)\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid.T` (`✓ std3`).

*Citation.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

The finite filter ranges over all four-colour arrays. First appearances fix the colour names in increasing order.

**Theorem 1.13 (The unique defective bond).**

$$\forall (n: \operatorname{Nat}), (\forall (k: \operatorname{Nat}), (\forall (C: \operatorname{Type}), ([\operatorname{DecidableEq}\left(C\right)], \forall (f: (\operatorname{KingGrid}.\operatorname{Cell}\left(n, k\right)) \to (C)), ((\operatorname{KingGrid}.\operatorname{OneDefect}\left(f\right)) \Leftrightarrow (\exists! (e: \operatorname{KingGrid}.\operatorname{Edge}\left(n, k\right)), (\operatorname{KingGrid}.\operatorname{mono}\left(f, e\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid.oneDefect_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

A one-element set of monochromatic bonds is equivalent to a unique monochromatic bond.

**Theorem 1.14 (Partition by defective bond).**

$$\forall (n: \operatorname{Nat}), (\forall (k: \operatorname{Nat}), (\operatorname{KingGrid}.\operatorname{L}\left(n, k\right) = \sum_{e: \operatorname{KingGrid}.\operatorname{Edge}\left(n, k\right)} (\operatorname{Nat}.\operatorname{card}\left(\{f: (\operatorname{KingGrid}.\operatorname{Cell}\left(n, k\right)) \to (\operatorname{Fin}\left(4\right)) // (\operatorname{KingGrid}.\operatorname{DefectAt}\left(e, f\right))\}\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid.count_by_edge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

Colourings with one defect are partitioned by the location of that defect.

**Theorem 1.15 (Separate the four bond orientations).**

$$\forall (n: \operatorname{Nat}), (\forall (k: \operatorname{Nat}), (\forall (F: (\operatorname{KingGrid}.\operatorname{Edge}\left(n, k\right)) \to (\operatorname{Nat})), (\sum_{e: \operatorname{KingGrid}.\operatorname{Edge}\left(n, k\right)} (F\left(e\right)) = (((\sum_{i: \operatorname{Fin}\left(n\right)} (\sum_{j: \operatorname{Fin}\left((k) - (1)\right)} (F\left(\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{H}\left(i, j\right)\right)))) + (\sum_{i: \operatorname{Fin}\left((n) - (1)\right)} (\sum_{j: \operatorname{Fin}\left(k\right)} (F\left(\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{V}\left(i, j\right)\right))))) + (\sum_{i: \operatorname{Fin}\left((n) - (1)\right)} (\sum_{j: \operatorname{Fin}\left((k) - (1)\right)} (F\left(\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{D}\left(i, j\right)\right))))) + (\sum_{i: \operatorname{Fin}\left((n) - (1)\right)} (\sum_{j: \operatorname{Fin}\left((k) - (1)\right)} (F\left(\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{A}\left(i, j\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid.sum_edges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

Summation over the bond type is the sum over its four constructors.

**Definition 1.16 (Transpose bonds).**

$$\forall (n: \operatorname{Nat}), (\forall (k: \operatorname{Nat}), (((\operatorname{KingGrid}.\operatorname{transposeEdge}: \operatorname{Equiv}\left(\operatorname{KingGrid}.\operatorname{Edge}\left(n, k\right), \operatorname{KingGrid}.\operatorname{Edge}\left(k, n\right)\right))) \land ((\forall (i: \operatorname{Fin}\left(n\right)), (\forall (j: \operatorname{Fin}\left((k) - (1)\right)), (\operatorname{KingGrid}.\operatorname{transposeEdge}\left(\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{H}\left(i, j\right)\right) = \operatorname{KingGrid}.\operatorname{Edge}.\operatorname{V}\left(j, i\right)))) \land ((\forall (i: \operatorname{Fin}\left((n) - (1)\right)), (\forall (j: \operatorname{Fin}\left(k\right)), (\operatorname{KingGrid}.\operatorname{transposeEdge}\left(\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{V}\left(i, j\right)\right) = \operatorname{KingGrid}.\operatorname{Edge}.\operatorname{H}\left(j, i\right)))) \land ((\forall (i: \operatorname{Fin}\left((n) - (1)\right)), (\forall (j: \operatorname{Fin}\left((k) - (1)\right)), (\operatorname{KingGrid}.\operatorname{transposeEdge}\left(\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{D}\left(i, j\right)\right) = \operatorname{KingGrid}.\operatorname{Edge}.\operatorname{D}\left(j, i\right)))) \land (\forall (i: \operatorname{Fin}\left((n) - (1)\right)), (\forall (j: \operatorname{Fin}\left((k) - (1)\right)), (\operatorname{KingGrid}.\operatorname{transposeEdge}\left(\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{A}\left(i, j\right)\right) = \operatorname{KingGrid}.\operatorname{Edge}.\operatorname{A}\left(j, i\right)))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid.transposeEdge` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

Transposition exchanges horizontal and vertical bonds and preserves each diagonal orientation.

**Definition 1.17 (Reflect columns).**

$$\forall (n: \operatorname{Nat}), (\forall (k: \operatorname{Nat}), (((\operatorname{KingGrid}.\operatorname{reflectEdge}: \operatorname{Equiv}\left(\operatorname{KingGrid}.\operatorname{Edge}\left(n, k\right), \operatorname{KingGrid}.\operatorname{Edge}\left(n, k\right)\right))) \land ((\forall (i: \operatorname{Fin}\left(n\right)), (\forall (j: \operatorname{Fin}\left((k) - (1)\right)), (\operatorname{KingGrid}.\operatorname{reflectEdge}\left(\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{H}\left(i, j\right)\right) = \operatorname{KingGrid}.\operatorname{Edge}.\operatorname{H}\left(i, \operatorname{Fin}.\operatorname{rev}\left(j\right)\right)))) \land ((\forall (i: \operatorname{Fin}\left((n) - (1)\right)), (\forall (j: \operatorname{Fin}\left(k\right)), (\operatorname{KingGrid}.\operatorname{reflectEdge}\left(\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{V}\left(i, j\right)\right) = \operatorname{KingGrid}.\operatorname{Edge}.\operatorname{V}\left(i, \operatorname{Fin}.\operatorname{rev}\left(j\right)\right)))) \land ((\forall (i: \operatorname{Fin}\left((n) - (1)\right)), (\forall (j: \operatorname{Fin}\left((k) - (1)\right)), (\operatorname{KingGrid}.\operatorname{reflectEdge}\left(\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{D}\left(i, j\right)\right) = \operatorname{KingGrid}.\operatorname{Edge}.\operatorname{A}\left(i, \operatorname{Fin}.\operatorname{rev}\left(j\right)\right)))) \land (\forall (i: \operatorname{Fin}\left((n) - (1)\right)), (\forall (j: \operatorname{Fin}\left((k) - (1)\right)), (\operatorname{KingGrid}.\operatorname{reflectEdge}\left(\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{A}\left(i, j\right)\right) = \operatorname{KingGrid}.\operatorname{Edge}.\operatorname{D}\left(i, \operatorname{Fin}.\operatorname{rev}\left(j\right)\right)))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid.reflectEdge` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

Column reflection reverses the column index and exchanges the two diagonal orientations.

**Definition 1.18 (Transpose a colouring).**

$$\forall (n: \operatorname{Nat}), (\forall (k: \operatorname{Nat}), (\forall (C: \operatorname{Type}), (\forall (f: (\operatorname{KingGrid}.\operatorname{Cell}\left(n, k\right)) \to (C)), (\forall (p: \operatorname{KingGrid}.\operatorname{Cell}\left(k, n\right)), (\operatorname{KingGrid}.\operatorname{transpose}\left(f\right)\left(p\right) = f\left((\operatorname{Prod}.\operatorname{snd}\left(p\right), \operatorname{Prod}.\operatorname{fst}\left(p\right))\right))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid.transpose` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

Transposition exchanges the two cell coordinates.

**Theorem 1.19 (Transposition preserves monochromatic bonds).**

$$\forall (n: \operatorname{Nat}), (\forall (k: \operatorname{Nat}), (\forall (C: \operatorname{Type}), (\forall (f: (\operatorname{KingGrid}.\operatorname{Cell}\left(n, k\right)) \to (C)), (\forall (e: \operatorname{KingGrid}.\operatorname{Edge}\left(n, k\right)), ((\operatorname{KingGrid}.\operatorname{mono}\left(\operatorname{KingGrid}.\operatorname{transpose}\left(f\right), \operatorname{KingGrid}.\operatorname{transposeEdge}\left(e\right)\right)) \Leftrightarrow (\operatorname{KingGrid}.\operatorname{mono}\left(f, e\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid.transpose_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

The endpoints are transposed together, so equality of their colours is preserved.

**Definition 1.20 (Transpose a prescribed defect).**

$$\forall (n: \operatorname{Nat}), (\forall (k: \operatorname{Nat}), (\forall (C: \operatorname{Type}), (\forall (e: \operatorname{KingGrid}.\operatorname{Edge}\left(n, k\right)), (((\operatorname{KingGrid}.\operatorname{transposeDefectEquiv}\left(e\right): \operatorname{Equiv}\left(\{f: (\operatorname{KingGrid}.\operatorname{Cell}\left(n, k\right)) \to (C) // (\operatorname{KingGrid}.\operatorname{DefectAt}\left(e, f\right))\}, \{f: (\operatorname{KingGrid}.\operatorname{Cell}\left(k, n\right)) \to (C) // (\operatorname{KingGrid}.\operatorname{DefectAt}\left(\operatorname{KingGrid}.\operatorname{transposeEdge}\left(e\right), f\right))\}\right))) \land (\forall (f: \{f: (\operatorname{KingGrid}.\operatorname{Cell}\left(n, k\right)) \to (C) // (\operatorname{KingGrid}.\operatorname{DefectAt}\left(e, f\right))\}), (\operatorname{Subtype}.\operatorname{val}\left(\operatorname{KingGrid}.\operatorname{transposeDefectEquiv}\left(e\right)\left(f\right)\right) = \operatorname{KingGrid}.\operatorname{transpose}\left(\operatorname{Subtype}.\operatorname{val}\left(f\right)\right)))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid.transposeDefectEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

The map acts on colourings by the geometric symmetry and carries the selected defective bond along with it. Applying the symmetry twice gives the inverse.

**Definition 1.21 (Reflect a prescribed defect).**

$$\forall (n: \operatorname{Nat}), (\forall (k: \operatorname{Nat}), (\forall (C: \operatorname{Type}), (\forall (e: \operatorname{KingGrid}.\operatorname{Edge}\left(n, k\right)), (((\operatorname{KingGrid}.\operatorname{reflectDefectEquiv}\left(e\right): \operatorname{Equiv}\left(\{f: (\operatorname{KingGrid}.\operatorname{Cell}\left(n, k\right)) \to (C) // (\operatorname{KingGrid}.\operatorname{DefectAt}\left(e, f\right))\}, \{f: (\operatorname{KingGrid}.\operatorname{Cell}\left(n, k\right)) \to (C) // (\operatorname{KingGrid}.\operatorname{DefectAt}\left(\operatorname{KingGrid}.\operatorname{reflectEdge}\left(e\right), f\right))\}\right))) \land (\forall (f: \{f: (\operatorname{KingGrid}.\operatorname{Cell}\left(n, k\right)) \to (C) // (\operatorname{KingGrid}.\operatorname{DefectAt}\left(e, f\right))\}), (\operatorname{Subtype}.\operatorname{val}\left(\operatorname{KingGrid}.\operatorname{reflectDefectEquiv}\left(e\right)\left(f\right)\right) = (\lambda (p: \operatorname{KingGrid}.\operatorname{Cell}\left(n, k\right)) \mapsto \operatorname{Subtype}.\operatorname{val}\left(f\right)\left((\operatorname{Prod}.\operatorname{fst}\left(p\right), \operatorname{Fin}.\operatorname{rev}\left(\operatorname{Prod}.\operatorname{snd}\left(p\right)\right))\right))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid.reflectDefectEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

The map acts on colourings by the geometric symmetry and carries the selected defective bond along with it. Applying the symmetry twice gives the inverse.

**Theorem 1.22 (Twenty-four labelled colourings per canonical colouring).**

$$\forall (n: \operatorname{Nat}), (\forall (k: \operatorname{Nat}), ((2 \le n) \Rightarrow ((2 \le k) \Rightarrow (\operatorname{KingGrid}.\operatorname{L}\left(n, k\right) = (24) \cdot (\operatorname{KingGrid}.\operatorname{T}\left(n, k\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid.labelled_eq_twentyFour` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

For both side lengths at least two, each one-defect array uses at least three colours. A permutation of four colours fixing three is the identity. Each colour orbit therefore has twenty-four elements and one row-major canonical representative.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid.Cell`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid.DefectAt`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid.Edge`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid.L`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid.OneDefect`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid.T`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid.count_by_edge`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid.end0`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid.end1`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid.hi`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid.labelled_eq_twentyFour`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid.lo`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid.mono`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid.normal`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid.oneDefect_iff`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid.reflectDefectEquiv`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid.reflectEdge`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid.sum_edges`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid.transpose`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid.transposeDefectEquiv`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid.transposeEdge`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid.transpose_mono`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233166KingStrip](../../../Combinatorics/TraceAvoidingArrays/HardinA233166KingStrip.md)
- Dependency: [D5/S3/Topology/QuandleMarkovColoring](../../../Topology/QuandleMarkovColoring.md)
