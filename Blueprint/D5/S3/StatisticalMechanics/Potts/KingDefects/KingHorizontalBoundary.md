# One-defect king colourings: KingHorizontalBoundary

## Abstract

Finite colourings with exactly one monochromatic king bond.

**Definition 1.1 (BoundaryData).**

$$\forall (m: \operatorname{Nat}), (\forall (M: \operatorname{Nat}), ((((((\operatorname{KingHorizontal}.\operatorname{BoundaryData}.\operatorname{mk}: (\operatorname{KingDifference}.\operatorname{K}) \to ((\operatorname{KingDifference}.\operatorname{K}) \to (((\operatorname{Fin}\left(M\right)) \to (\operatorname{KingDifference}.\operatorname{K})) \to (((\operatorname{Fin}\left(m\right)) \to (\operatorname{KingDifference}.\operatorname{K})) \to (\operatorname{KingHorizontal}.\operatorname{BoundaryData}\left(m, M\right))))))) \land ((\operatorname{KingHorizontal}.\operatorname{BoundaryData}.\operatorname{p}: (\operatorname{KingHorizontal}.\operatorname{BoundaryData}\left(m, M\right)) \to (\operatorname{KingDifference}.\operatorname{K})))) \land ((\operatorname{KingHorizontal}.\operatorname{BoundaryData}.\operatorname{q}: (\operatorname{KingHorizontal}.\operatorname{BoundaryData}\left(m, M\right)) \to (\operatorname{KingDifference}.\operatorname{K})))) \land ((\operatorname{KingHorizontal}.\operatorname{BoundaryData}.\operatorname{h}: (\operatorname{KingHorizontal}.\operatorname{BoundaryData}\left(m, M\right)) \to ((\operatorname{Fin}\left(M\right)) \to (\operatorname{KingDifference}.\operatorname{K}))))) \land ((\operatorname{KingHorizontal}.\operatorname{BoundaryData}.\operatorname{v}: (\operatorname{KingHorizontal}.\operatorname{BoundaryData}\left(m, M\right)) \to ((\operatorname{Fin}\left(m\right)) \to (\operatorname{KingDifference}.\operatorname{K}))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalBoundary.BoundaryData` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

The record contains two special colours p and q, a horizontal word h of length M and an ordinary vertical word v of length m.

**Definition 1.2 (BoundaryValid).**

$$\forall (m: \operatorname{Nat}), (\forall (M: \operatorname{Nat}), (\forall (s: \operatorname{Fin}\left(M\right)), (\forall (b: \operatorname{KingHorizontal}.\operatorname{BoundaryData}\left(m\right)\left(M\right)), ((\operatorname{KingHorizontal}.\operatorname{BoundaryValid}\left(s, b\right)) \Leftrightarrow ((\operatorname{KingHorizontal}.\operatorname{BoundaryData}.\operatorname{p}\left(b\right) \ne 0) \land ((\operatorname{KingHorizontal}.\operatorname{BoundaryData}.\operatorname{q}\left(b\right) \ne 0) \land ((\operatorname{KingHorizontal}.\operatorname{BoundaryData}.\operatorname{p}\left(b\right) \ne \operatorname{KingHorizontal}.\operatorname{BoundaryData}.\operatorname{q}\left(b\right)) \land ((\operatorname{KingHorizontal}.\operatorname{BoundaryData}.\operatorname{h}\left(b\right)\left(s\right) = (\operatorname{KingHorizontal}.\operatorname{BoundaryData}.\operatorname{p}\left(b\right)) + (\operatorname{KingHorizontal}.\operatorname{BoundaryData}.\operatorname{q}\left(b\right))) \land ((\forall (j: \operatorname{Fin}\left(M\right)), (\operatorname{KingHorizontal}.\operatorname{BoundaryData}.\operatorname{h}\left(b\right)\left(j\right) \ne 0)) \land ((\forall (i: \operatorname{Fin}\left(m\right)), (\operatorname{KingHorizontal}.\operatorname{BoundaryData}.\operatorname{v}\left(b\right)\left(i\right) \ne 0)) \land ((\forall (j: \operatorname{Fin}\left(M\right)), ((j < s) \Rightarrow (\operatorname{KingHorizontal}.\operatorname{BoundaryData}.\operatorname{h}\left(b\right)\left(j\right) \ne \operatorname{KingHorizontal}.\operatorname{BoundaryData}.\operatorname{p}\left(b\right)))) \land ((\forall (j: \operatorname{Fin}\left(M\right)), ((s < j) \Rightarrow (\operatorname{KingHorizontal}.\operatorname{BoundaryData}.\operatorname{h}\left(b\right)\left(j\right) \ne \operatorname{KingHorizontal}.\operatorname{BoundaryData}.\operatorname{q}\left(b\right)))) \land (\forall (i: \operatorname{Fin}\left(m\right)), (\forall (j: \operatorname{Fin}\left(M\right)), (\operatorname{KingHorizontal}.\operatorname{BoundaryData}.\operatorname{h}\left(b\right)\left(j\right) \ne \operatorname{KingHorizontal}.\operatorname{BoundaryData}.\operatorname{v}\left(b\right)\left(i\right))))))))))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalBoundary.BoundaryValid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

The special colours are distinct and nonzero. The pivot is their sum; all slots are nonzero. Left and right slots exclude p and q respectively, and every horizontal slot differs from every ordinary vertical slot.

**Definition 1.3 (boundary build).**

$$\forall (m: \operatorname{Nat}), (\forall (M: \operatorname{Nat}), (\forall (s: \operatorname{Fin}\left(M\right)), (\forall (b: \operatorname{KingHorizontal}.\operatorname{BoundaryData}\left(m, M\right)), ((\operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{h}\left(\operatorname{KingHorizontal}.\operatorname{boundary_{build}}\left(s, b\right)\right) = \operatorname{Fin}.\operatorname{cons}\left(\operatorname{Function}.\operatorname{update}\left(\operatorname{KingHorizontal}.\operatorname{BoundaryData}.\operatorname{h}\left(b\right), s, 0\right), \operatorname{Function}.\operatorname{const}\left(\operatorname{Fin}\left((m) + (1)\right), \operatorname{KingHorizontal}.\operatorname{BoundaryData}.\operatorname{h}\left(b\right)\right)\right)) \land (\operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{v}\left(\operatorname{KingHorizontal}.\operatorname{boundary_{build}}\left(s, b\right)\right) = \operatorname{Fin}.\operatorname{cons}\left((\lambda (j: \operatorname{Fin}\left((M) + (1)\right)) \mapsto \operatorname{ite}\left(\operatorname{Fin}.\operatorname{val}\left(j\right) \le \operatorname{Fin}.\operatorname{val}\left(s\right), \operatorname{KingHorizontal}.\operatorname{BoundaryData}.\operatorname{p}\left(b\right), \operatorname{KingHorizontal}.\operatorname{BoundaryData}.\operatorname{q}\left(b\right)\right)), (\lambda (i: \operatorname{Fin}\left(m\right)) \mapsto \operatorname{Function}.\operatorname{const}\left(\operatorname{Fin}\left((M) + (1)\right), \operatorname{KingHorizontal}.\operatorname{BoundaryData}.\operatorname{v}\left(b\right)\left(i\right)\right))\right))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalBoundary.boundary_build` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

Fin.cons prepends the exceptional row to each field. Function.update sets horizontal position s to zero. The first vertical step uses p through column s and q afterwards; Function.const supplies the constant tails.

**Definition 1.4 (boundary extract).**

$$\forall (m: \operatorname{Nat}), (\forall (M: \operatorname{Nat}), (\forall (s: \operatorname{Fin}\left(M\right)), (\forall (t: \operatorname{KingDifference}.\operatorname{DiffField}\left((m) + (1)\right)\left(M\right)), ((\operatorname{KingHorizontal}.\operatorname{BoundaryData}.\operatorname{p}\left(\operatorname{KingHorizontal}.\operatorname{boundary_{extract}}\left(s\right)\left(t\right)\right) = \operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{v}\left(t\right)\left(0\right)\left(\operatorname{Fin}.\operatorname{castSucc}\left(s\right)\right)) \land ((\operatorname{KingHorizontal}.\operatorname{BoundaryData}.\operatorname{q}\left(\operatorname{KingHorizontal}.\operatorname{boundary_{extract}}\left(s\right)\left(t\right)\right) = \operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{v}\left(t\right)\left(0\right)\left(\operatorname{Fin}.\operatorname{succ}\left(s\right)\right)) \land ((\forall (j: \operatorname{Fin}\left(M\right)), (\operatorname{KingHorizontal}.\operatorname{BoundaryData}.\operatorname{h}\left(\operatorname{KingHorizontal}.\operatorname{boundary_{extract}}\left(s\right)\left(t\right)\right)\left(j\right) = \operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{h}\left(t\right)\left(1\right)\left(j\right))) \land (\forall (i: \operatorname{Fin}\left(m\right)), (\operatorname{KingHorizontal}.\operatorname{BoundaryData}.\operatorname{v}\left(\operatorname{KingHorizontal}.\operatorname{boundary_{extract}}\left(s\right)\left(t\right)\right)\left(i\right) = \operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{v}\left(t\right)\left(\operatorname{Fin}.\operatorname{succ}\left(i\right)\right)\left(0\right)))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalBoundary.boundary_extract` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

The special colours are the two vertical values adjacent to s on the first step. The horizontal word comes from row one and the ordinary vertical word from column zero.

**Theorem 1.5 (boundary h).**

$$\forall (m: \operatorname{Nat}), (\forall (M: \operatorname{Nat}), (\forall (s: \operatorname{Fin}\left(M\right)), (\forall (t: \operatorname{KingDifference}.\operatorname{DiffField}\left((m) + (1)\right)\left(M\right)), ((\operatorname{KingDifference}.\operatorname{RawAdmissible}\left(\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{H}\left(0\right)\left(s\right)\right)\left(t\right)) \Rightarrow (\forall (i: \operatorname{Fin}\left(((m) + (1)) + (1)\right)), (\forall (j: \operatorname{Fin}\left(M\right)), (\operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{h}\left(t\right)\left(i\right)\left(j\right) = \operatorname{ite}\left((i = 0) \land (j = s), 0, \operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{h}\left(t\right)\left(1\right)\left(j\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalBoundary.boundary_h` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

Every nondefective horizontal slot is constant through the rows, while the selected bond has value zero.

**Definition 1.6 (boundary slot equiv).**

$$\forall (m: \operatorname{Nat}), (\forall (M: \operatorname{Nat}), (\forall (s: \operatorname{Fin}\left(M\right)), (((\operatorname{KingHorizontal}.\operatorname{boundary_{slot_{equiv}}}\left(m, M, s\right): \operatorname{Equiv}\left(\{t: \operatorname{KingDifference}.\operatorname{DiffField}\left((m) + (1)\right)\left(M\right) // (\operatorname{KingDifference}.\operatorname{RawAdmissible}\left(\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{H}\left(0\right)\left(s\right)\right)\left(t\right))\}, \{b: \operatorname{KingHorizontal}.\operatorname{BoundaryData}\left(m\right)\left(M\right) // (\operatorname{KingHorizontal}.\operatorname{BoundaryValid}\left(s\right)\left(b\right))\}\right))) \land (\forall (t: \{t: \operatorname{KingDifference}.\operatorname{DiffField}\left((m) + (1)\right)\left(M\right) // (\operatorname{KingDifference}.\operatorname{RawAdmissible}\left(\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{H}\left(0\right)\left(s\right)\right)\left(t\right))\}), (\operatorname{Subtype}.\operatorname{val}\left(\operatorname{KingHorizontal}.\operatorname{boundary_{slot_{equiv}}}\left(m, M, s\right)\left(t\right)\right) = \operatorname{KingHorizontal}.\operatorname{boundary_{extract}}\left(s, \operatorname{Subtype}.\operatorname{val}\left(t\right)\right))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalBoundary.boundary_slot_equiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

Extraction and filling identify admissible top-boundary fields with valid boundary data.

**Definition 1.7 (BoundaryWords).**

$$\forall (m: \operatorname{Nat}), (\forall (c: \operatorname{Nat}), (\forall (d: \operatorname{Nat}), (\operatorname{KingHorizontal}.\operatorname{BoundaryWords}\left(m, c, d\right) = \{w: ((\operatorname{Fin}\left(m\right)) \to (\operatorname{Bool})) \times (((\operatorname{Fin}\left(c\right)) \to (\operatorname{Bool})) \times ((\operatorname{Fin}\left(d\right)) \to (\operatorname{Bool}))) // (((\operatorname{Prod}.\operatorname{fst}\left(w\right) \ne \operatorname{Function}.\operatorname{const}\left(\operatorname{Fin}\left(m\right)\right)\left(\operatorname{Bool}.\operatorname{false}\right)) \Rightarrow (\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Prod}.\operatorname{snd}\left(w\right)\right) = \operatorname{Function}.\operatorname{const}\left(\operatorname{Fin}\left(c\right)\right)\left(\operatorname{Bool}.\operatorname{true}\right))) \land ((\operatorname{Prod}.\operatorname{fst}\left(w\right) \ne \operatorname{Function}.\operatorname{const}\left(\operatorname{Fin}\left(m\right)\right)\left(\operatorname{Bool}.\operatorname{true}\right)) \Rightarrow (\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(w\right)\right) = \operatorname{Function}.\operatorname{const}\left(\operatorname{Fin}\left(d\right)\right)\left(\operatorname{Bool}.\operatorname{true}\right))))\})))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalBoundary.BoundaryWords` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

The vertical word and the left and right horizontal words are Boolean. A nonconstant vertical word forces both side words to be constantly true.

**Theorem 1.8 (boundary words zero card).**

$$\forall (c: \operatorname{Nat}), (\forall (d: \operatorname{Nat}), (\operatorname{Nat}.\operatorname{card}\left(\operatorname{KingHorizontal}.\operatorname{BoundaryWords}\left(0\right)\left(c\right)\left(d\right)\right) = (2)^{(c) + (d)}))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalBoundary.boundary_words_zero_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

With no ordinary vertical positions, the two horizontal words are independent binary words.

**Theorem 1.9 (boundary words pos card).**

$$\forall (m: \operatorname{Nat}), (\forall (c: \operatorname{Nat}), (\forall (d: \operatorname{Nat}), ((0 < m) \Rightarrow ((\operatorname{Nat}.\operatorname{card}\left(\operatorname{KingHorizontal}.\operatorname{BoundaryWords}\left(m\right)\left(c\right)\left(d\right)\right)) + (2) = (((2)^{m}) + ((2)^{c})) + ((2)^{d})))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalBoundary.boundary_words_pos_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

For positive m, partition according to the two constant vertical words and the remaining vertical words.

**Definition 1.10 (pivot).**

$$\forall (c: \operatorname{Nat}), (\forall (d: \operatorname{Nat}), (((\operatorname{KingHorizontal}.\operatorname{pivot}\left(c, d\right): \operatorname{Fin}\left((c) + ((d) + (1))\right))) \land (\operatorname{Fin}.\operatorname{val}\left(\operatorname{KingHorizontal}.\operatorname{pivot}\left(c, d\right)\right) = c)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalBoundary.pivot` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

The pivot has natural value c in a row of c + d + 1 positions.

**Theorem 1.11 (boundary count zero).**

$$\forall (c: \operatorname{Nat}), (\forall (d: \operatorname{Nat}), (\operatorname{KingDifference}.\operatorname{N_{e}}\left((\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{H}\left(0\right)\left(\operatorname{KingHorizontal}.\operatorname{pivot}\left(c\right)\left(d\right)\right): \operatorname{KingGrid}.\operatorname{Edge}\left(2\right)\left(((c) + ((d) + (1))) + (1)\right))\right) = (6) \cdot ((2)^{(c) + (d)})))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalBoundary.boundary_count_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

Six choices of the special ordered pair multiply the binary choices on the two horizontal sides.

**Theorem 1.12 (boundary count pos).**

$$\forall (m: \operatorname{Nat}), (\forall (c: \operatorname{Nat}), (\forall (d: \operatorname{Nat}), ((0 < m) \Rightarrow ((\operatorname{KingDifference}.\operatorname{N_{e}}\left((\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{H}\left(0\right)\left(\operatorname{KingHorizontal}.\operatorname{pivot}\left(c\right)\left(d\right)\right): \operatorname{KingGrid}.\operatorname{Edge}\left(((m) + (1)) + (1)\right)\left(((c) + ((d) + (1))) + (1)\right))\right)) + (12) = (6) \cdot ((((2)^{m}) + ((2)^{c})) + ((2)^{d}))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalBoundary.boundary_count_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

For positive m, the two constant vertical cases and the remaining vertical cases give the three powers of two.

**Theorem 1.13 (horizontal count row reflect).**

$$\forall (N: \operatorname{Nat}), (\forall (M: \operatorname{Nat}), (\forall (i: \operatorname{Fin}\left((N) + (1)\right)), (\forall (j: \operatorname{Fin}\left(M\right)), (\operatorname{KingDifference}.\operatorname{N_{e}}\left((\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{H}\left(\operatorname{Fin}.\operatorname{rev}\left(i\right)\right)\left(j\right): \operatorname{KingGrid}.\operatorname{Edge}\left((N) + (1)\right)\left((M) + (1)\right))\right) = \operatorname{KingDifference}.\operatorname{N_{e}}\left(\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{H}\left(i\right)\left(j\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalBoundary.horizontal_count_row_reflect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

Row reflection gives a bijection of admissible fields at the two reflected horizontal bonds.

**Definition 1.14 (E).**

$$\forall (m: \operatorname{Nat}), (\forall (c: \operatorname{Nat}), (\forall (d: \operatorname{Nat}), (\operatorname{KingHorizontal}.\operatorname{E}\left(m, c, d\right) = \operatorname{ite}\left(m = 0, (2)^{(c) + (d)}, ((((2)^{m}) + ((2)^{c})) + ((2)^{d})) - (2)\right))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalBoundary.E` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

The empty ordinary vertical word leaves two independent horizontal words. For positive m the two constant vertical words and the nonconstant words give the second branch. Subtraction is natural subtraction.

**Theorem 1.15 (boundary count).**

$$\forall (m: \operatorname{Nat}), (\forall (c: \operatorname{Nat}), (\forall (d: \operatorname{Nat}), (\operatorname{KingDifference}.\operatorname{N_{e}}\left((\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{H}\left(0\right)\left(\operatorname{KingHorizontal}.\operatorname{pivot}\left(c\right)\left(d\right)\right): \operatorname{KingGrid}.\operatorname{Edge}\left(((m) + (1)) + (1)\right)\left(((c) + ((d) + (1))) + (1)\right))\right) = (6) \cdot (\operatorname{KingHorizontal}.\operatorname{E}\left(m\right)\left(c\right)\left(d\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalBoundary.boundary_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

The boundary-field count is six times its Boolean-word count, including an empty ordinary vertical word.

**Theorem 1.16 (boundary count at).**

$$\forall (m: \operatorname{Nat}), (\forall (M: \operatorname{Nat}), (\forall (s: \operatorname{Fin}\left(M\right)), (\operatorname{KingDifference}.\operatorname{N_{e}}\left((\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{H}\left(0\right)\left(s\right): \operatorname{KingGrid}.\operatorname{Edge}\left(((m) + (1)) + (1)\right)\left((M) + (1)\right))\right) = (6) \cdot (\operatorname{KingHorizontal}.\operatorname{E}\left(m\right)\left(\operatorname{Fin}.\operatorname{val}\left(s\right)\right)\left(((M) - (1)) - (\operatorname{Fin}.\operatorname{val}\left(s\right))\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalBoundary.boundary_count_at` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

The column index determines the left side length, and natural subtraction gives the right side length.

**Theorem 1.17 (boundary rows count).**

$$\forall (m: \operatorname{Nat}), (\forall (M: \operatorname{Nat}), (\forall (r: \operatorname{Fin}\left(((m) + (1)) + (1)\right)), (\forall (s: \operatorname{Fin}\left(M\right)), (((r = 0) \lor (r = \operatorname{Fin}.\operatorname{last}\left((m) + (1)\right))) \Rightarrow (\operatorname{KingDifference}.\operatorname{N_{e}}\left((\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{H}\left(r\right)\left(s\right): \operatorname{KingGrid}.\operatorname{Edge}\left(((m) + (1)) + (1)\right)\left((M) + (1)\right))\right) = (6) \cdot (\operatorname{KingHorizontal}.\operatorname{E}\left(m\right)\left(\operatorname{Fin}.\operatorname{val}\left(s\right)\right)\left(((M) - (1)) - (\operatorname{Fin}.\operatorname{val}\left(s\right))\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalBoundary.boundary_rows_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

The same count holds on either boundary row by row reflection.

**Definition 1.18 (row reflect).**

$$\forall (N: \operatorname{Nat}), (\forall (M: \operatorname{Nat}), (\forall (t: \operatorname{KingDifference}.\operatorname{DiffField}\left(N\right)\left(M\right)), ((\forall (i: \operatorname{Fin}\left((N) + (1)\right)), (\forall (j: \operatorname{Fin}\left(M\right)), (\operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{h}\left(\operatorname{KingHorizontal}.\operatorname{row_{reflect}}\left(t\right)\right)\left(i\right)\left(j\right) = \operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{h}\left(t\right)\left(\operatorname{Fin}.\operatorname{rev}\left(i\right)\right)\left(j\right)))) \land (\forall (i: \operatorname{Fin}\left(N\right)), (\forall (j: \operatorname{Fin}\left((M) + (1)\right)), (\operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{v}\left(\operatorname{KingHorizontal}.\operatorname{row_{reflect}}\left(t\right)\right)\left(i\right)\left(j\right) = \operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{v}\left(t\right)\left(\operatorname{Fin}.\operatorname{rev}\left(i\right)\right)\left(j\right)))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalBoundary.row_reflect` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

Reverse both finite row indices; column indices and colours are unchanged.

**Theorem 1.19 (row reflect raw).**

$$\forall (N: \operatorname{Nat}), (\forall (M: \operatorname{Nat}), (\forall (r: \operatorname{Fin}\left((N) + (1)\right)), (\forall (s: \operatorname{Fin}\left(M\right)), (\forall (t: \operatorname{KingDifference}.\operatorname{DiffField}\left(N\right)\left(M\right)), ((\operatorname{KingDifference}.\operatorname{RawAdmissible}\left(\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{H}\left(r\right)\left(s\right)\right)\left(t\right)) \Rightarrow (\operatorname{KingDifference}.\operatorname{RawAdmissible}\left(\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{H}\left(\operatorname{Fin}.\operatorname{rev}\left(r\right)\right)\left(s\right)\right)\left(\operatorname{KingHorizontal}.\operatorname{row_{reflect}}\left(t\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalBoundary.row_reflect_raw` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

Reversing the row indices preserves compatibility and sends the unique zero bond to its reflected row.

**Definition 1.20 (row reflect equiv).**

$$\forall (N: \operatorname{Nat}), (\forall (M: \operatorname{Nat}), (\forall (r: \operatorname{Fin}\left((N) + (1)\right)), (\forall (s: \operatorname{Fin}\left(M\right)), (((\operatorname{KingHorizontal}.\operatorname{row_{reflect_{equiv}}}\left(r, s\right): \operatorname{Equiv}\left(\{t: \operatorname{KingDifference}.\operatorname{DiffField}\left(N\right)\left(M\right) // (\operatorname{KingDifference}.\operatorname{RawAdmissible}\left(\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{H}\left(r\right)\left(s\right)\right)\left(t\right))\}, \{t: \operatorname{KingDifference}.\operatorname{DiffField}\left(N\right)\left(M\right) // (\operatorname{KingDifference}.\operatorname{RawAdmissible}\left(\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{H}\left(\operatorname{Fin}.\operatorname{rev}\left(r\right)\right)\left(s\right)\right)\left(t\right))\}\right))) \land (\forall (t: \{t: \operatorname{KingDifference}.\operatorname{DiffField}\left(N\right)\left(M\right) // (\operatorname{KingDifference}.\operatorname{RawAdmissible}\left(\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{H}\left(r\right)\left(s\right)\right)\left(t\right))\}), (\operatorname{Subtype}.\operatorname{val}\left(\operatorname{KingHorizontal}.\operatorname{row_{reflect_{equiv}}}\left(r, s\right)\left(t\right)\right) = \operatorname{KingHorizontal}.\operatorname{row_{reflect}}\left(\operatorname{Subtype}.\operatorname{val}\left(t\right)\right)))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalBoundary.row_reflect_equiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

Row reversal is its own inverse on admissible difference fields.

**Definition 1.21 (boundary bottom slot equiv).**

$$\forall (m: \operatorname{Nat}), (\forall (M: \operatorname{Nat}), (\forall (s: \operatorname{Fin}\left(M\right)), (((\operatorname{KingHorizontal}.\operatorname{boundary_{bottom_{slot_{equiv}}}}\left(m, M, s\right): \operatorname{Equiv}\left(\{t: \operatorname{KingDifference}.\operatorname{DiffField}\left((m) + (1)\right)\left(M\right) // (\operatorname{KingDifference}.\operatorname{RawAdmissible}\left(\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{H}\left(\operatorname{Fin}.\operatorname{last}\left((m) + (1)\right)\right)\left(s\right)\right)\left(t\right))\}, \{b: \operatorname{KingHorizontal}.\operatorname{BoundaryData}\left(m\right)\left(M\right) // (\operatorname{KingHorizontal}.\operatorname{BoundaryValid}\left(s\right)\left(b\right))\}\right))) \land (\forall (t: \{t: \operatorname{KingDifference}.\operatorname{DiffField}\left((m) + (1)\right)\left(M\right) // (\operatorname{KingDifference}.\operatorname{RawAdmissible}\left(\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{H}\left(\operatorname{Fin}.\operatorname{last}\left((m) + (1)\right)\right)\left(s\right)\right)\left(t\right))\}), (\operatorname{Subtype}.\operatorname{val}\left(\operatorname{KingHorizontal}.\operatorname{boundary_{bottom_{slot_{equiv}}}}\left(m, M, s\right)\left(t\right)\right) = \operatorname{KingHorizontal}.\operatorname{boundary_{extract}}\left(s, \operatorname{KingHorizontal}.\operatorname{row_{reflect}}\left(\operatorname{Subtype}.\operatorname{val}\left(t\right)\right)\right))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalBoundary.boundary_bottom_slot_equiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

Reflect an admissible bottom-boundary field to the top boundary, then extract its valid boundary data.

**Definition 1.22 (cut row).**

$$\forall (A: \operatorname{Nat}), (\forall (B: \operatorname{Nat}), (((\operatorname{KingHorizontal}.\operatorname{cut_{row}}\left(A, B\right): \operatorname{Fin}\left(((A) + (B)) + (1)\right))) \land ((\operatorname{KingHorizontal}.\operatorname{cut_{row}}\left(A, B\right) = \operatorname{KingHorizontal}.\operatorname{pivot}\left(A, B\right)) \land (\operatorname{Fin}.\operatorname{val}\left(\operatorname{KingHorizontal}.\operatorname{cut_{row}}\left(A, B\right)\right) = A))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalBoundary.cut_row` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

The shared row is pivot A B, with natural value A in a rectangle with A + B vertical steps.

**Definition 1.23 (CutFields).**

$$\forall (A: \operatorname{Nat}), (\forall (B: \operatorname{Nat}), (\forall (M: \operatorname{Nat}), (\forall (s: \operatorname{Fin}\left(M\right)), (\operatorname{KingHorizontal}.\operatorname{CutFields}\left(A, B, M, s\right) = \{q: (\operatorname{KingDifference}.\operatorname{DiffField}\left(A\right)\left(M\right)) \times (\operatorname{KingDifference}.\operatorname{DiffField}\left(B\right)\left(M\right)) // ((\operatorname{KingDifference}.\operatorname{RawAdmissible}\left(\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{H}\left(\operatorname{Fin}.\operatorname{last}\left(A\right)\right)\left(s\right)\right)\left(\operatorname{Prod}.\operatorname{fst}\left(q\right)\right)) \land ((\operatorname{KingDifference}.\operatorname{RawAdmissible}\left(\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{H}\left(0\right)\left(s\right)\right)\left(\operatorname{Prod}.\operatorname{snd}\left(q\right)\right)) \land (\forall (j: \operatorname{Fin}\left(M\right)), (\operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{h}\left(\operatorname{Prod}.\operatorname{fst}\left(q\right)\right)\left(\operatorname{Fin}.\operatorname{last}\left(A\right)\right)\left(j\right) = \operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{h}\left(\operatorname{Prod}.\operatorname{snd}\left(q\right)\right)\left(0\right)\left(j\right)))))\}))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalBoundary.CutFields` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

The two half-fields have defects at their common row and agree on every horizontal value there, including the zero at s.

**Definition 1.24 (horizontal cut equiv).**

$$(\forall (A: \operatorname{Nat}), (\forall (B: \operatorname{Nat}), (\forall (M: \operatorname{Nat}), (\forall (s: \operatorname{Fin}\left(M\right)), (((\operatorname{KingHorizontal}.\operatorname{horizontal_{cut_{equiv}}}\left(A, B, M, s\right): \operatorname{Equiv}\left(\{t: \operatorname{KingDifference}.\operatorname{DiffField}\left((A) + (B)\right)\left(M\right) // (\operatorname{KingDifference}.\operatorname{RawAdmissible}\left(\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{H}\left(\operatorname{KingHorizontal}.\operatorname{cut_{row}}\left(A\right)\left(B\right)\right)\left(s\right)\right)\left(t\right))\}, \operatorname{KingHorizontal}.\operatorname{CutFields}\left(A\right)\left(B\right)\left(M\right)\left(s\right)\right))) \land (\forall (t: \{t: \operatorname{KingDifference}.\operatorname{DiffField}\left((A) + (B)\right)\left(M\right) // (\operatorname{KingDifference}.\operatorname{RawAdmissible}\left(\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{H}\left(\operatorname{KingHorizontal}.\operatorname{cut_{row}}\left(A\right)\left(B\right)\right)\left(s\right)\right)\left(t\right))\}), ((\forall (i: \operatorname{Fin}\left((A) + (1)\right)), (\forall (k: \operatorname{Fin}\left(((A) + (B)) + (1)\right)), (\forall (j: \operatorname{Fin}\left(M\right)), ((\operatorname{Fin}.\operatorname{val}\left(k\right) = \operatorname{Fin}.\operatorname{val}\left(i\right)) \Rightarrow (\operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{h}\left(\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Subtype}.\operatorname{val}\left(\operatorname{KingHorizontal}.\operatorname{horizontal_{cut_{equiv}}}\left(A, B, M, s\right)\left(t\right)\right)\right), i, j\right) = \operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{h}\left(\operatorname{Subtype}.\operatorname{val}\left(t\right), k, j\right)))))) \land ((\forall (i: \operatorname{Fin}\left(A\right)), (\forall (k: \operatorname{Fin}\left((A) + (B)\right)), (\forall (j: \operatorname{Fin}\left((M) + (1)\right)), ((\operatorname{Fin}.\operatorname{val}\left(k\right) = \operatorname{Fin}.\operatorname{val}\left(i\right)) \Rightarrow (\operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{v}\left(\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Subtype}.\operatorname{val}\left(\operatorname{KingHorizontal}.\operatorname{horizontal_{cut_{equiv}}}\left(A, B, M, s\right)\left(t\right)\right)\right), i, j\right) = \operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{v}\left(\operatorname{Subtype}.\operatorname{val}\left(t\right), k, j\right)))))) \land ((\forall (i: \operatorname{Fin}\left((B) + (1)\right)), (\forall (k: \operatorname{Fin}\left(((A) + (B)) + (1)\right)), (\forall (j: \operatorname{Fin}\left(M\right)), ((\operatorname{Fin}.\operatorname{val}\left(k\right) = (A) + (\operatorname{Fin}.\operatorname{val}\left(i\right))) \Rightarrow (\operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{h}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Subtype}.\operatorname{val}\left(\operatorname{KingHorizontal}.\operatorname{horizontal_{cut_{equiv}}}\left(A, B, M, s\right)\left(t\right)\right)\right), i, j\right) = \operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{h}\left(\operatorname{Subtype}.\operatorname{val}\left(t\right), k, j\right)))))) \land (\forall (i: \operatorname{Fin}\left(B\right)), (\forall (k: \operatorname{Fin}\left((A) + (B)\right)), (\forall (j: \operatorname{Fin}\left((M) + (1)\right)), ((\operatorname{Fin}.\operatorname{val}\left(k\right) = (A) + (\operatorname{Fin}.\operatorname{val}\left(i\right))) \Rightarrow (\operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{v}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Subtype}.\operatorname{val}\left(\operatorname{KingHorizontal}.\operatorname{horizontal_{cut_{equiv}}}\left(A, B, M, s\right)\left(t\right)\right)\right), i, j\right) = \operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{v}\left(\operatorname{Subtype}.\operatorname{val}\left(t\right), k, j\right))))))))))))))) \land (\forall (A: \operatorname{Nat}), (\forall (B: \operatorname{Nat}), (\forall (M: \operatorname{Nat}), (\forall (s: \operatorname{Fin}\left(M\right)), (\forall (q: \operatorname{KingHorizontal}.\operatorname{CutFields}\left(A, B, M, s\right)), ((\operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{h}\left(\operatorname{Subtype}.\operatorname{val}\left(\operatorname{Equiv}.\operatorname{symm}\left(\operatorname{KingHorizontal}.\operatorname{horizontal_{cut_{equiv}}}\left(A, B, M, s\right)\right)\left(q\right)\right)\right) = \operatorname{Fin}.\operatorname{append}\left(\operatorname{Fin}.\operatorname{init}\left(\operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{h}\left(\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Subtype}.\operatorname{val}\left(q\right)\right)\right)\right), \operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{h}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Subtype}.\operatorname{val}\left(q\right)\right)\right)\right)) \land (\operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{v}\left(\operatorname{Subtype}.\operatorname{val}\left(\operatorname{Equiv}.\operatorname{symm}\left(\operatorname{KingHorizontal}.\operatorname{horizontal_{cut_{equiv}}}\left(A, B, M, s\right)\right)\left(q\right)\right)\right) = \operatorname{Fin}.\operatorname{append}\left(\operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{v}\left(\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Subtype}.\operatorname{val}\left(q\right)\right)\right), \operatorname{KingDifference}.\operatorname{DiffField}.\operatorname{v}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Subtype}.\operatorname{val}\left(q\right)\right)\right)\right))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalBoundary.horizontal_cut_equiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

Restrict above and below the selected row. The row embeddings top_row and bottom_row use Fin.castLE and Fin.natAdd, respectively. The inverse uses Fin.append to join the vertical tuples, and Fin.append with Fin.init of the upper horizontal tuple joins the horizontal tuples, retaining the lower copy of the shared row.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalBoundary.BoundaryData`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalBoundary.BoundaryValid`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalBoundary.BoundaryWords`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalBoundary.CutFields`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalBoundary.E`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalBoundary.boundary_bottom_slot_equiv`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalBoundary.boundary_build`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalBoundary.boundary_count`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalBoundary.boundary_count_at`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalBoundary.boundary_count_pos`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalBoundary.boundary_count_zero`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalBoundary.boundary_extract`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalBoundary.boundary_h`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalBoundary.boundary_rows_count`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalBoundary.boundary_slot_equiv`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalBoundary.boundary_words_pos_card`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalBoundary.boundary_words_zero_card`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalBoundary.cut_row`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalBoundary.horizontal_count_row_reflect`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalBoundary.horizontal_cut_equiv`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalBoundary.pivot`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalBoundary.row_reflect`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalBoundary.row_reflect_equiv`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalBoundary.row_reflect_raw`
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/KingDifference](KingDifference.md)
