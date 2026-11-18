# One-defect king colourings: KingHorizontalSlots

## Abstract

Finite colourings with exactly one monochromatic king bond.

**Definition 1.1 (InteriorSlots).**

$$\forall (a: \operatorname{Nat}), (\forall (b: \operatorname{Nat}), (\forall (M: \operatorname{Nat}), (\forall (s: \operatorname{Fin}\left(M\right)), (\operatorname{KingHorizontal}.\operatorname{InteriorSlots}\left(a, b, M, s\right) = \{q: (\{u: \operatorname{KingHorizontal}.\operatorname{BoundaryData}\left(a\right)\left(M\right) // (\operatorname{KingHorizontal}.\operatorname{BoundaryValid}\left(s\right)\left(u\right))\}) \times (\{l: \operatorname{KingHorizontal}.\operatorname{BoundaryData}\left(b\right)\left(M\right) // (\operatorname{KingHorizontal}.\operatorname{BoundaryValid}\left(s\right)\left(l\right))\}) // (\forall (j: \operatorname{Fin}\left(M\right)), ((j \ne s) \Rightarrow (\operatorname{KingHorizontal}.\operatorname{BoundaryData}.\operatorname{h}\left(\operatorname{Subtype}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(q\right)\right)\right)\left(j\right) = \operatorname{KingHorizontal}.\operatorname{BoundaryData}.\operatorname{h}\left(\operatorname{Subtype}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(q\right)\right)\right)\left(j\right))))\}))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalSlots.InteriorSlots` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

Two valid boundary assignments share every horizontal slot except the defective position. Their special ordered pairs may differ.

**Definition 1.2 (interior slot equiv).**

$$\forall (a: \operatorname{Nat}), (\forall (b: \operatorname{Nat}), (\forall (M: \operatorname{Nat}), (\forall (s: \operatorname{Fin}\left(M\right)), (((\operatorname{KingHorizontal}.\operatorname{interior_{slot_{equiv}}}\left(a, b, M, s\right): \operatorname{Equiv}\left(\{t: \operatorname{KingDifference}.\operatorname{DiffField}\left(((a) + (1)) + ((b) + (1))\right)\left(M\right) // (\operatorname{KingDifference}.\operatorname{RawAdmissible}\left(\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{H}\left(\operatorname{KingHorizontal}.\operatorname{cut_{row}}\left((a) + (1)\right)\left((b) + (1)\right)\right)\left(s\right)\right)\left(t\right))\}, \operatorname{KingHorizontal}.\operatorname{InteriorSlots}\left(a\right)\left(b\right)\left(M\right)\left(s\right)\right))) \land (\forall (t: \{t: \operatorname{KingDifference}.\operatorname{DiffField}\left(((a) + (1)) + ((b) + (1))\right)\left(M\right) // (\operatorname{KingDifference}.\operatorname{RawAdmissible}\left(\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{H}\left(\operatorname{KingHorizontal}.\operatorname{cut_{row}}\left((a) + (1)\right)\left((b) + (1)\right)\right)\left(s\right)\right)\left(t\right))\}), ((\operatorname{Subtype}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Subtype}.\operatorname{val}\left(\operatorname{KingHorizontal}.\operatorname{interior_{slot_{equiv}}}\left(a, b, M, s\right)\left(t\right)\right)\right)\right) = \operatorname{KingHorizontal}.\operatorname{boundary_{extract}}\left(s, \operatorname{KingHorizontal}.\operatorname{row_{reflect}}\left(\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Subtype}.\operatorname{val}\left(\operatorname{KingHorizontal}.\operatorname{horizontal_{cut_{equiv}}}\left((a) + (1), (b) + (1), M, s\right)\left(t\right)\right)\right)\right)\right)) \land (\operatorname{Subtype}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Subtype}.\operatorname{val}\left(\operatorname{KingHorizontal}.\operatorname{interior_{slot_{equiv}}}\left(a, b, M, s\right)\left(t\right)\right)\right)\right) = \operatorname{KingHorizontal}.\operatorname{boundary_{extract}}\left(s, \operatorname{Prod}.\operatorname{snd}\left(\operatorname{Subtype}.\operatorname{val}\left(\operatorname{KingHorizontal}.\operatorname{horizontal_{cut_{equiv}}}\left((a) + (1), (b) + (1), M, s\right)\left(t\right)\right)\right)\right))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalSlots.interior_slot_equiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

Cut at the defective row and express the two resulting boundary fields as compatible slot assignments.

**Definition 1.3 (OrdinaryAlphabet).**

$$\forall (x: \operatorname{KingDifference}.\operatorname{NZPair}), (\operatorname{KingHorizontal}.\operatorname{OrdinaryAlphabet}\left(x\right) = \{v: \operatorname{KingDifference}.\operatorname{K} // ((v \ne 0) \land (v \ne (\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Subtype}.\operatorname{val}\left(x\right)\right)) + (\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Subtype}.\operatorname{val}\left(x\right)\right))))\})$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalSlots.OrdinaryAlphabet` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

An ordinary vertical colour is nonzero and differs from the sum of the special ordered pair.

**Definition 1.4 (InteriorAlphabet).**

$$\forall (a: \operatorname{Nat}), (\forall (b: \operatorname{Nat}), (\forall (x: \operatorname{KingDifference}.\operatorname{NZPair}), (\forall (y: \operatorname{KingDifference}.\operatorname{NZPair}), (\forall (u: (\operatorname{Fin}\left(a\right)) \to (\operatorname{KingHorizontal}.\operatorname{OrdinaryAlphabet}\left(x\right))), (\forall (v: (\operatorname{Fin}\left(b\right)) \to (\operatorname{KingHorizontal}.\operatorname{OrdinaryAlphabet}\left(y\right))), (\forall (p: \operatorname{KingDifference}.\operatorname{K}), (\forall (q: \operatorname{KingDifference}.\operatorname{K}), (\operatorname{KingHorizontal}.\operatorname{InteriorAlphabet}\left(x, y, u, v, p, q\right) = \{h: \operatorname{KingDifference}.\operatorname{K} // ((h \ne 0) \land ((h \ne p) \land ((h \ne q) \land ((\forall (i: \operatorname{Fin}\left(a\right)), (h \ne \operatorname{Subtype}.\operatorname{val}\left(u\left(i\right)\right))) \land (\forall (i: \operatorname{Fin}\left(b\right)), (h \ne \operatorname{Subtype}.\operatorname{val}\left(v\left(i\right)\right)))))))\}))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalSlots.InteriorAlphabet` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

A shared horizontal colour excludes zero, the two relevant special colours and every value of both ordinary vertical words.

**Theorem 1.5 (interior count alphabets).**

$$\forall (a: \operatorname{Nat}), (\forall (b: \operatorname{Nat}), (\forall (c: \operatorname{Nat}), (\forall (d: \operatorname{Nat}), (\operatorname{KingDifference}.\operatorname{N_{e}}\left((\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{H}\left(\operatorname{KingHorizontal}.\operatorname{cut_{row}}\left((a) + (1)\right)\left((b) + (1)\right)\right)\left(\operatorname{KingHorizontal}.\operatorname{pivot}\left(c\right)\left(d\right)\right): \operatorname{KingGrid}.\operatorname{Edge}\left((((a) + (1)) + ((b) + (1))) + (1)\right)\left(((c) + ((d) + (1))) + (1)\right))\right) = \sum_{x: \operatorname{KingDifference}.\operatorname{NZPair}} (\sum_{y: \operatorname{KingDifference}.\operatorname{NZPair}} (\sum_{u: (\operatorname{Fin}\left(a\right)) \to (\operatorname{KingHorizontal}.\operatorname{OrdinaryAlphabet}\left(x\right))} (\sum_{v: (\operatorname{Fin}\left(b\right)) \to (\operatorname{KingHorizontal}.\operatorname{OrdinaryAlphabet}\left(y\right))} (((\operatorname{Nat}.\operatorname{card}\left(\operatorname{KingHorizontal}.\operatorname{InteriorAlphabet}\left(x\right)\left(y\right)\left(u\right)\left(v\right)\left(\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Subtype}.\operatorname{val}\left(x\right)\right)\right)\left(\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Subtype}.\operatorname{val}\left(y\right)\right)\right)\right))^{c}) \cdot ((\operatorname{Nat}.\operatorname{card}\left(\operatorname{KingHorizontal}.\operatorname{InteriorAlphabet}\left(x\right)\left(y\right)\left(u\right)\left(v\right)\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Subtype}.\operatorname{val}\left(x\right)\right)\right)\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Subtype}.\operatorname{val}\left(y\right)\right)\right)\right))^{d})))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalSlots.interior_count_alphabets` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

After choosing the two special pairs and the ordinary vertical words, the shared horizontal positions vary independently in their allowed alphabets.

**Definition 1.6 (word support).**

$$\forall (n: \operatorname{Nat}), (\forall (u: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Bool})), (\operatorname{KingHorizontal}.\operatorname{word_{support}}\left(u\right) = \operatorname{Finset}.\operatorname{image}\left(u\right)\left((\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right))\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalSlots.word_support` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

The support is the image of the entire finite index set under the Boolean word.

**Theorem 1.7 (word support empty).**

$$\forall (n: \operatorname{Nat}), (\forall (u: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Bool})), ((\operatorname{KingHorizontal}.\operatorname{word_{support}}\left(u\right) = \operatorname{Finset}.\operatorname{empty}) \Leftrightarrow (n = 0)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalSlots.word_support_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

A Boolean word has empty image exactly when its index set is empty.

**Theorem 1.8 (word support singleton).**

$$\forall (n: \operatorname{Nat}), ((0 < n) \Rightarrow (\forall (u: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Bool})), (\forall (b: \operatorname{Bool}), ((\operatorname{KingHorizontal}.\operatorname{word_{support}}\left(u\right) = \left\{b\right\}) \Leftrightarrow (u = \operatorname{Function}.\operatorname{const}\left(\operatorname{Fin}\left(n\right), b\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalSlots.word_support_singleton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

A nonempty Boolean word has singleton support exactly when it is the corresponding constant word.

**Theorem 1.9 (word support full).**

$$\forall (n: \operatorname{Nat}), ((0 < n) \Rightarrow (\forall (u: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Bool})), ((\operatorname{KingHorizontal}.\operatorname{word_{support}}\left(u\right) = \operatorname{Finset}.\operatorname{univ}) \Leftrightarrow ((u \ne \operatorname{Function}.\operatorname{const}\left(\operatorname{Fin}\left(n\right), \operatorname{Bool}.\operatorname{false}\right)) \land (u \ne \operatorname{Function}.\operatorname{const}\left(\operatorname{Fin}\left(n\right), \operatorname{Bool}.\operatorname{true}\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalSlots.word_support_full` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

A nonempty Boolean word has both values exactly when it is neither constant false nor constant true.

**Definition 1.10 (support weight).**

$$\forall (n: \operatorname{Nat}), (\forall (S: \operatorname{Finset}\left(\operatorname{Bool}\right)), (\operatorname{KingHorizontal}.\operatorname{support_{weight}}\left(n, S\right) = \operatorname{ite}\left(n = 0, \operatorname{ite}\left(S = \operatorname{Finset}.\operatorname{empty}, 1, 0\right), \operatorname{ite}\left(S = \operatorname{Finset}.\operatorname{empty}, 0, \operatorname{ite}\left((S = \left\{\operatorname{Bool}.\operatorname{false}\right\}) \lor (S = \left\{\operatorname{Bool}.\operatorname{true}\right\}), 1, ((2)^{n}) - (2)\right)\right)\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalSlots.support_weight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

An empty word has empty support. A nonempty word has one realization for either singleton support, no realization for empty support, and 2 raised to n minus two realizations for full support. Subtraction is natural subtraction.

**Theorem 1.11 (word support card).**

$$\forall (n: \operatorname{Nat}), (\forall (S: \operatorname{Finset}\left(\operatorname{Bool}\right)), (\operatorname{Nat}.\operatorname{card}\left(\{u: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Bool}) // (\operatorname{KingHorizontal}.\operatorname{word_{support}}\left(u\right) = S)\}\right) = \operatorname{KingHorizontal}.\operatorname{support_{weight}}\left(n\right)\left(S\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalSlots.word_support_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

The number of Boolean words with a fixed support is its support weight.

**Theorem 1.12 (sum by support).**

$$\forall (n: \operatorname{Nat}), (\forall (f: (\operatorname{Finset}\left(\operatorname{Bool}\right)) \to (\operatorname{Nat})), (\sum_{u: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Bool})} (f\left(\operatorname{KingHorizontal}.\operatorname{word_{support}}\left(u\right)\right)) = \sum_{S: \operatorname{Finset}\left(\operatorname{Bool}\right)} ((\operatorname{KingHorizontal}.\operatorname{support_{weight}}\left(n\right)\left(S\right)) \cdot (f\left(S\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalSlots.sum_by_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

Apply Fintype.sum_fiberwise' to word_support, then use word_support_card to weight each support by its number of realizations.

**Definition 1.13 (ordinary value).**

$$\forall (x: \operatorname{KingDifference}.\operatorname{NZPair}), (\forall (b: \operatorname{Bool}), (\operatorname{KingHorizontal}.\operatorname{ordinary_{value}}\left(x, b\right) = \operatorname{ite}\left(b, \operatorname{Prod}.\operatorname{snd}\left(\operatorname{Subtype}.\operatorname{val}\left(x\right)\right), \operatorname{Prod}.\operatorname{fst}\left(\operatorname{Subtype}.\operatorname{val}\left(x\right)\right)\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalSlots.ordinary_value` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

False chooses the first entry and true the second entry of the ordered pair.

**Theorem 1.14 (ordinary value valid).**

$$\forall (x: \operatorname{KingDifference}.\operatorname{NZPair}), (\forall (b: \operatorname{Bool}), ((\operatorname{KingHorizontal}.\operatorname{ordinary_{value}}\left(x\right)\left(b\right) \ne 0) \land (\operatorname{KingHorizontal}.\operatorname{ordinary_{value}}\left(x\right)\left(b\right) \ne (\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Subtype}.\operatorname{val}\left(x\right)\right)) + (\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Subtype}.\operatorname{val}\left(x\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalSlots.ordinary_value_valid` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

Either selected entry is nonzero and differs from the sum of the two distinct nonzero entries.

**Definition 1.15 (SupportAlphabet).**

$$\forall (x: \operatorname{KingDifference}.\operatorname{NZPair}), (\forall (y: \operatorname{KingDifference}.\operatorname{NZPair}), (\forall (S: \operatorname{Finset}\left(\operatorname{Bool}\right)), (\forall (T: \operatorname{Finset}\left(\operatorname{Bool}\right)), (\forall (p: \operatorname{KingDifference}.\operatorname{K}), (\forall (q: \operatorname{KingDifference}.\operatorname{K}), (\operatorname{KingHorizontal}.\operatorname{SupportAlphabet}\left(x, y, S, T, p, q\right) = \{h: \operatorname{KingDifference}.\operatorname{K} // ((h \ne 0) \land ((h \ne p) \land ((h \ne q) \land ((\forall (z: \operatorname{Bool}), ((z \in S) \Rightarrow (h \ne \operatorname{KingHorizontal}.\operatorname{ordinary_{value}}\left(x\right)\left(z\right)))) \land (\forall (z: \operatorname{Bool}), ((z \in T) \Rightarrow (h \ne \operatorname{KingHorizontal}.\operatorname{ordinary_{value}}\left(y\right)\left(z\right))))))))\}))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalSlots.SupportAlphabet` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

Replace the vertical words by their supports while retaining all exclusions on a horizontal colour.

**Definition 1.16 (pair support count).**

$$\forall (a: \operatorname{Nat}), (\forall (b: \operatorname{Nat}), (\forall (c: \operatorname{Nat}), (\forall (d: \operatorname{Nat}), (\forall (x: \operatorname{KingDifference}.\operatorname{NZPair}), (\forall (y: \operatorname{KingDifference}.\operatorname{NZPair}), (\operatorname{KingHorizontal}.\operatorname{pair_{support_{count}}}\left(a, b, c, d, x, y\right) = \sum_{S: \operatorname{Finset}\left(\operatorname{Bool}\right)} (\sum_{T: \operatorname{Finset}\left(\operatorname{Bool}\right)} ((((\operatorname{KingHorizontal}.\operatorname{support_{weight}}\left(a\right)\left(S\right)) \cdot (\operatorname{KingHorizontal}.\operatorname{support_{weight}}\left(b\right)\left(T\right))) \cdot ((\operatorname{Nat}.\operatorname{card}\left(\operatorname{KingHorizontal}.\operatorname{SupportAlphabet}\left(x\right)\left(y\right)\left(S\right)\left(T\right)\left(\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Subtype}.\operatorname{val}\left(x\right)\right)\right)\left(\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Subtype}.\operatorname{val}\left(y\right)\right)\right)\right))^{c})) \cdot ((\operatorname{Nat}.\operatorname{card}\left(\operatorname{KingHorizontal}.\operatorname{SupportAlphabet}\left(x\right)\left(y\right)\left(S\right)\left(T\right)\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Subtype}.\operatorname{val}\left(x\right)\right)\right)\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Subtype}.\operatorname{val}\left(y\right)\right)\right)\right))^{d})))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalSlots.pair_support_count` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

Sum over the two Boolean supports. Their word multiplicities multiply the independent left and right horizontal alphabet powers.

**Theorem 1.17 (pair count support).**

$$\forall (a: \operatorname{Nat}), (\forall (b: \operatorname{Nat}), (\forall (c: \operatorname{Nat}), (\forall (d: \operatorname{Nat}), (\forall (x: \operatorname{KingDifference}.\operatorname{NZPair}), (\forall (y: \operatorname{KingDifference}.\operatorname{NZPair}), (\sum_{u: (\operatorname{Fin}\left(a\right)) \to (\operatorname{KingHorizontal}.\operatorname{OrdinaryAlphabet}\left(x\right))} (\sum_{v: (\operatorname{Fin}\left(b\right)) \to (\operatorname{KingHorizontal}.\operatorname{OrdinaryAlphabet}\left(y\right))} (((\operatorname{Nat}.\operatorname{card}\left(\operatorname{KingHorizontal}.\operatorname{InteriorAlphabet}\left(x\right)\left(y\right)\left(u\right)\left(v\right)\left(\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Subtype}.\operatorname{val}\left(x\right)\right)\right)\left(\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Subtype}.\operatorname{val}\left(y\right)\right)\right)\right))^{c}) \cdot ((\operatorname{Nat}.\operatorname{card}\left(\operatorname{KingHorizontal}.\operatorname{InteriorAlphabet}\left(x\right)\left(y\right)\left(u\right)\left(v\right)\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Subtype}.\operatorname{val}\left(x\right)\right)\right)\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Subtype}.\operatorname{val}\left(y\right)\right)\right)\right))^{d}))) = \operatorname{KingHorizontal}.\operatorname{pair_{support_{count}}}\left(a\right)\left(b\right)\left(c\right)\left(d\right)\left(x\right)\left(y\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalSlots.pair_count_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

Transport ordinary vertical words to Boolean words and group the sum by their two supports.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalSlots.InteriorAlphabet`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalSlots.InteriorSlots`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalSlots.OrdinaryAlphabet`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalSlots.SupportAlphabet`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalSlots.interior_count_alphabets`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalSlots.interior_slot_equiv`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalSlots.ordinary_value`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalSlots.ordinary_value_valid`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalSlots.pair_count_support`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalSlots.pair_support_count`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalSlots.sum_by_support`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalSlots.support_weight`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalSlots.word_support`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalSlots.word_support_card`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalSlots.word_support_empty`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalSlots.word_support_full`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalSlots.word_support_singleton`
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalBoundary](KingHorizontalBoundary.md)
