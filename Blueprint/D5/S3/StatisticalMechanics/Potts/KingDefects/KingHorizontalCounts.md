# One-defect king colourings: KingHorizontalCounts

## Abstract

Finite colourings with exactly one monochromatic king bond.

**Theorem 1.1 (interior count support).**

$$\forall (a: \operatorname{Nat}), (\forall (b: \operatorname{Nat}), (\forall (c: \operatorname{Nat}), (\forall (d: \operatorname{Nat}), (\operatorname{KingDifference}.\operatorname{N_{e}}\left((\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{H}\left(\operatorname{KingHorizontal}.\operatorname{cut_{row}}\left((a) + (1)\right)\left((b) + (1)\right)\right)\left(\operatorname{KingHorizontal}.\operatorname{pivot}\left(c\right)\left(d\right)\right): \operatorname{KingGrid}.\operatorname{Edge}\left((((a) + (1)) + ((b) + (1))) + (1)\right)\left(((c) + ((d) + (1))) + (1)\right))\right) = \sum_{x: \operatorname{KingDifference}.\operatorname{NZPair}} (\sum_{y: \operatorname{KingDifference}.\operatorname{NZPair}} (\operatorname{KingHorizontal}.\operatorname{pair_{support_{count}}}\left(a\right)\left(b\right)\left(c\right)\left(d\right)\left(x\right)\left(y\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.interior_count_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

Sum the support counts over the two special ordered pairs.

**Definition 1.2 (supports).**

$$((\operatorname{KingHorizontal}.\operatorname{supports}: (\operatorname{Fin}\left(4\right)) \to (\operatorname{Finset}\left(\operatorname{Bool}\right)))) \land ((\operatorname{KingHorizontal}.\operatorname{supports}\left((0: \operatorname{Fin}\left(4\right))\right) = \operatorname{Finset}.\operatorname{empty}) \land ((\operatorname{KingHorizontal}.\operatorname{supports}\left((1: \operatorname{Fin}\left(4\right))\right) = \left\{\operatorname{Bool}.\operatorname{false}\right\}) \land ((\operatorname{KingHorizontal}.\operatorname{supports}\left((2: \operatorname{Fin}\left(4\right))\right) = \left\{\operatorname{Bool}.\operatorname{true}\right\}) \land (\operatorname{KingHorizontal}.\operatorname{supports}\left((3: \operatorname{Fin}\left(4\right))\right) = (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left(\operatorname{Bool}\right))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.supports` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

The four supports in index order are empty, the singleton false, the singleton true, and the full Boolean set.

**Definition 1.3 (lower pair values).**

$$\forall (x: \operatorname{KingDifference}.\operatorname{NZPair}), (((\operatorname{KingHorizontal}.\operatorname{lower_{pair_{values}}}\left(x\right): (\operatorname{Fin}\left(6\right)) \to ((\operatorname{KingDifference}.\operatorname{K}) \times (\operatorname{KingDifference}.\operatorname{K})))) \land ((\operatorname{KingHorizontal}.\operatorname{lower_{pair_{values}}}\left(x, (0: \operatorname{Fin}\left(6\right))\right) = (\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Subtype}.\operatorname{val}\left(x\right)\right), \operatorname{Prod}.\operatorname{snd}\left(\operatorname{Subtype}.\operatorname{val}\left(x\right)\right))) \land ((\operatorname{KingHorizontal}.\operatorname{lower_{pair_{values}}}\left(x, (1: \operatorname{Fin}\left(6\right))\right) = (\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Subtype}.\operatorname{val}\left(x\right)\right), \operatorname{Prod}.\operatorname{fst}\left(\operatorname{Subtype}.\operatorname{val}\left(x\right)\right))) \land ((\operatorname{KingHorizontal}.\operatorname{lower_{pair_{values}}}\left(x, (2: \operatorname{Fin}\left(6\right))\right) = (\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Subtype}.\operatorname{val}\left(x\right)\right), (\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Subtype}.\operatorname{val}\left(x\right)\right)) + (\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Subtype}.\operatorname{val}\left(x\right)\right)))) \land ((\operatorname{KingHorizontal}.\operatorname{lower_{pair_{values}}}\left(x, (3: \operatorname{Fin}\left(6\right))\right) = ((\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Subtype}.\operatorname{val}\left(x\right)\right)) + (\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Subtype}.\operatorname{val}\left(x\right)\right)), \operatorname{Prod}.\operatorname{snd}\left(\operatorname{Subtype}.\operatorname{val}\left(x\right)\right))) \land ((\operatorname{KingHorizontal}.\operatorname{lower_{pair_{values}}}\left(x, (4: \operatorname{Fin}\left(6\right))\right) = ((\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Subtype}.\operatorname{val}\left(x\right)\right)) + (\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Subtype}.\operatorname{val}\left(x\right)\right)), \operatorname{Prod}.\operatorname{fst}\left(\operatorname{Subtype}.\operatorname{val}\left(x\right)\right))) \land (\operatorname{KingHorizontal}.\operatorname{lower_{pair_{values}}}\left(x, (5: \operatorname{Fin}\left(6\right))\right) = (\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Subtype}.\operatorname{val}\left(x\right)\right), (\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Subtype}.\operatorname{val}\left(x\right)\right)) + (\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Subtype}.\operatorname{val}\left(x\right)\right))))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.lower_pair_values` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

The six ordered pairs are obtained from the first colour, the second colour and their sum, in the displayed order.

**Theorem 1.4 (lower pair valid).**

$$\forall (x: \operatorname{KingDifference}.\operatorname{NZPair}), (\forall (i: \operatorname{Fin}\left(6\right)), ((\operatorname{Prod}.\operatorname{fst}\left(\operatorname{KingHorizontal}.\operatorname{lower_{pair_{values}}}\left(x\right)\left(i\right)\right) \ne 0) \land ((\operatorname{Prod}.\operatorname{snd}\left(\operatorname{KingHorizontal}.\operatorname{lower_{pair_{values}}}\left(x\right)\left(i\right)\right) \ne 0) \land (\operatorname{Prod}.\operatorname{fst}\left(\operatorname{KingHorizontal}.\operatorname{lower_{pair_{values}}}\left(x\right)\left(i\right)\right) \ne \operatorname{Prod}.\operatorname{snd}\left(\operatorname{KingHorizontal}.\operatorname{lower_{pair_{values}}}\left(x\right)\left(i\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.lower_pair_valid` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

Each of the six indexed pairs consists of distinct nonzero colours.

**Definition 1.5 (lower pair).**

$$\forall (x: \operatorname{KingDifference}.\operatorname{NZPair}), (\forall (i: \operatorname{Fin}\left(6\right)), (((\operatorname{KingHorizontal}.\operatorname{lower_{pair}}\left(x, i\right): \operatorname{KingDifference}.\operatorname{NZPair})) \land (\operatorname{Subtype}.\operatorname{val}\left(\operatorname{KingHorizontal}.\operatorname{lower_{pair}}\left(x, i\right)\right) = \operatorname{KingHorizontal}.\operatorname{lower_{pair_{values}}}\left(x, i\right))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.lower_pair` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

Attach the nonzero and distinctness conditions to the indexed ordered pair.

**Definition 1.6 (support sizes).**

$$(\operatorname{KingHorizontal}.\operatorname{support_{sizes}}: (\operatorname{Fin}\left(6\right)) \to ((\operatorname{Fin}\left(4\right)) \to ((\operatorname{Fin}\left(4\right)) \to ((\operatorname{Nat}) \times (\operatorname{Nat})))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.support_sizes` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

This is a 6 by 4 by 4 table of pairs of natural numbers. The first index chooses the lower ordered pair and the next two choose Boolean supports; the two entries count the left and right shared horizontal alphabets.

**Theorem 1.7 (support sizes correct).**

$$\forall (x: \operatorname{KingDifference}.\operatorname{NZPair}), (\forall (i: \operatorname{Fin}\left(6\right)), (\forall (j: \operatorname{Fin}\left(4\right)), (\forall (k: \operatorname{Fin}\left(4\right)), ((\operatorname{Nat}.\operatorname{card}\left(\operatorname{KingHorizontal}.\operatorname{SupportAlphabet}\left(x\right)\left(\operatorname{KingHorizontal}.\operatorname{lower_{pair}}\left(x\right)\left(i\right)\right)\left(\operatorname{KingHorizontal}.\operatorname{supports}\left(j\right)\right)\left(\operatorname{KingHorizontal}.\operatorname{supports}\left(k\right)\right)\left(\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Subtype}.\operatorname{val}\left(x\right)\right)\right)\left(\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Subtype}.\operatorname{val}\left(\operatorname{KingHorizontal}.\operatorname{lower_{pair}}\left(x\right)\left(i\right)\right)\right)\right)\right), \operatorname{Nat}.\operatorname{card}\left(\operatorname{KingHorizontal}.\operatorname{SupportAlphabet}\left(x\right)\left(\operatorname{KingHorizontal}.\operatorname{lower_{pair}}\left(x\right)\left(i\right)\right)\left(\operatorname{KingHorizontal}.\operatorname{supports}\left(j\right)\right)\left(\operatorname{KingHorizontal}.\operatorname{supports}\left(k\right)\right)\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Subtype}.\operatorname{val}\left(x\right)\right)\right)\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Subtype}.\operatorname{val}\left(\operatorname{KingHorizontal}.\operatorname{lower_{pair}}\left(x\right)\left(i\right)\right)\right)\right)\right)) = \operatorname{KingHorizontal}.\operatorname{support_{sizes}}\left(i\right)\left(j\right)\left(k\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.support_sizes_correct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

Each table entry is exactly the pair of shared horizontal alphabet cardinalities for its ordered-pair case and two supports.

**Definition 1.8 (support case count).**

$$\forall (a: \operatorname{Nat}), (\forall (b: \operatorname{Nat}), (\forall (c: \operatorname{Nat}), (\forall (d: \operatorname{Nat}), (\forall (i: \operatorname{Fin}\left(6\right)), (\operatorname{KingHorizontal}.\operatorname{support_{case_{count}}}\left(a, b, c, d, i\right) = \sum_{j: \operatorname{Fin}\left(4\right)} (\sum_{k: \operatorname{Fin}\left(4\right)} ((((\operatorname{KingHorizontal}.\operatorname{support_{weight}}\left(a\right)\left(\operatorname{KingHorizontal}.\operatorname{supports}\left(j\right)\right)) \cdot (\operatorname{KingHorizontal}.\operatorname{support_{weight}}\left(b\right)\left(\operatorname{KingHorizontal}.\operatorname{supports}\left(k\right)\right))) \cdot ((\operatorname{Prod}.\operatorname{fst}\left(\operatorname{KingHorizontal}.\operatorname{support_{sizes}}\left(i\right)\left(j\right)\left(k\right)\right))^{c})) \cdot ((\operatorname{Prod}.\operatorname{snd}\left(\operatorname{KingHorizontal}.\operatorname{support_{sizes}}\left(i\right)\left(j\right)\left(k\right)\right))^{d}))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.support_case_count` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

For a fixed lower-pair case, sum the two support multiplicities times the two alphabet-size powers.

**Theorem 1.9 (pair support cases).**

$$\forall (a: \operatorname{Nat}), (\forall (b: \operatorname{Nat}), (\forall (c: \operatorname{Nat}), (\forall (d: \operatorname{Nat}), (\forall (x: \operatorname{KingDifference}.\operatorname{NZPair}), (\forall (i: \operatorname{Fin}\left(6\right)), (\operatorname{KingHorizontal}.\operatorname{pair_{support_{count}}}\left(a\right)\left(b\right)\left(c\right)\left(d\right)\left(x\right)\left(\operatorname{KingHorizontal}.\operatorname{lower_{pair}}\left(x\right)\left(i\right)\right) = \operatorname{KingHorizontal}.\operatorname{support_{case_{count}}}\left(a\right)\left(b\right)\left(c\right)\left(d\right)\left(i\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.pair_support_cases` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

For a fixed upper pair, the six lower-pair choices have the indicated support-table counts.

**Definition 1.10 (P).**

$$\forall (a: \operatorname{Nat}), (\forall (b: \operatorname{Nat}), (\forall (c: \operatorname{Nat}), (\forall (d: \operatorname{Nat}), (\operatorname{KingHorizontal}.\operatorname{P}\left(a, b, c, d\right) = \operatorname{ite}\left(d = 0, \operatorname{KingHorizontal}.\operatorname{E}\left(c\right)\left(a\right)\left(b\right), ((\operatorname{ite}\left(a = 0, 1, 0\right)) + (\operatorname{ite}\left(b = 0, 1, 0\right)))^{c}\right)))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.P` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

If the final side is empty, the count is E with the indicated reordered lengths. Otherwise only empty ordinary vertical sides contribute choices.

**Definition 1.11 (Q).**

$$\forall (a: \operatorname{Nat}), (\forall (b: \operatorname{Nat}), (\forall (c: \operatorname{Nat}), (\forall (d: \operatorname{Nat}), (\operatorname{KingHorizontal}.\operatorname{Q}\left(a, b, c, d\right) = (((1) + (\operatorname{ite}\left(c = 0, 1, 0\right)))^{a}) \cdot (((1) + (\operatorname{ite}\left(d = 0, 1, 0\right)))^{b})))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.Q` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

Each factor records whether its opposite horizontal side is empty, with independent exponents a and b.

**Definition 1.12 (six case value).**

$$\forall (a: \operatorname{Nat}), (\forall (b: \operatorname{Nat}), (\forall (c: \operatorname{Nat}), (\forall (d: \operatorname{Nat}), (((\operatorname{KingHorizontal}.\operatorname{six_{case_{value}}}\left(a, b, c, d\right): (\operatorname{Fin}\left(6\right)) \to (\operatorname{Nat}))) \land ((\operatorname{KingHorizontal}.\operatorname{six_{case_{value}}}\left(a, b, c, d, (0: \operatorname{Fin}\left(6\right))\right) = \operatorname{KingHorizontal}.\operatorname{E}\left((a) + (b)\right)\left(c\right)\left(d\right)) \land ((\operatorname{KingHorizontal}.\operatorname{six_{case_{value}}}\left(a, b, c, d, (1: \operatorname{Fin}\left(6\right))\right) = (2)^{(a) + (b)}) \land ((\operatorname{KingHorizontal}.\operatorname{six_{case_{value}}}\left(a, b, c, d, (2: \operatorname{Fin}\left(6\right))\right) = \operatorname{KingHorizontal}.\operatorname{P}\left(a\right)\left(b\right)\left(c\right)\left(d\right)) \land ((\operatorname{KingHorizontal}.\operatorname{six_{case_{value}}}\left(a, b, c, d, (3: \operatorname{Fin}\left(6\right))\right) = \operatorname{KingHorizontal}.\operatorname{P}\left(a\right)\left(b\right)\left(d\right)\left(c\right)) \land ((\operatorname{KingHorizontal}.\operatorname{six_{case_{value}}}\left(a, b, c, d, (4: \operatorname{Fin}\left(6\right))\right) = \operatorname{KingHorizontal}.\operatorname{Q}\left(a\right)\left(b\right)\left(c\right)\left(d\right)) \land (\operatorname{KingHorizontal}.\operatorname{six_{case_{value}}}\left(a, b, c, d, (5: \operatorname{Fin}\left(6\right))\right) = \operatorname{KingHorizontal}.\operatorname{Q}\left(a\right)\left(b\right)\left(d\right)\left(c\right)))))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.six_case_value` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

The six cases are E of a + b, the binary-word power, the two P terms and the two Q terms in the displayed order.

**Theorem 1.13 (support case eval).**

$$\forall (a: \operatorname{Nat}), (\forall (b: \operatorname{Nat}), (\forall (c: \operatorname{Nat}), (\forall (d: \operatorname{Nat}), (\forall (i: \operatorname{Fin}\left(6\right)), (\operatorname{KingHorizontal}.\operatorname{support_{case_{count}}}\left(a\right)\left(b\right)\left(c\right)\left(d\right)\left(i\right) = \operatorname{KingHorizontal}.\operatorname{six_{case_{value}}}\left(a\right)\left(b\right)\left(c\right)\left(d\right)\left(i\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.support_case_eval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

The finite support sum has six expressions, with empty sides included in E, P and Q.

**Theorem 1.14 (interior count).**

$$\forall (a: \operatorname{Nat}), (\forall (b: \operatorname{Nat}), (\forall (c: \operatorname{Nat}), (\forall (d: \operatorname{Nat}), (\operatorname{KingDifference}.\operatorname{N_{e}}\left((\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{H}\left(\operatorname{KingHorizontal}.\operatorname{cut_{row}}\left((a) + (1)\right)\left((b) + (1)\right)\right)\left(\operatorname{KingHorizontal}.\operatorname{pivot}\left(c\right)\left(d\right)\right): \operatorname{KingGrid}.\operatorname{Edge}\left((((a) + (1)) + ((b) + (1))) + (1)\right)\left(((c) + ((d) + (1))) + (1)\right))\right) = (6) \cdot ((((((\operatorname{KingHorizontal}.\operatorname{E}\left((a) + (b)\right)\left(c\right)\left(d\right)) + ((2)^{(a) + (b)})) + (\operatorname{KingHorizontal}.\operatorname{P}\left(a\right)\left(b\right)\left(c\right)\left(d\right))) + (\operatorname{KingHorizontal}.\operatorname{P}\left(a\right)\left(b\right)\left(d\right)\left(c\right))) + (\operatorname{KingHorizontal}.\operatorname{Q}\left(a\right)\left(b\right)\left(c\right)\left(d\right))) + (\operatorname{KingHorizontal}.\operatorname{Q}\left(a\right)\left(b\right)\left(d\right)\left(c\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.interior_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

There are six upper ordered-pair choices, and summing the six relative lower-pair cases gives the displayed expression.

**Theorem 1.15 (horizontal two rows).**

$$\forall (M: \operatorname{Nat}), (\operatorname{KingDifference}.\operatorname{N_{H}}\left(1\right)\left(M\right) = (6) \cdot ((M) \cdot ((2)^{M})))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.horizontal_two_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

On two rows every horizontal defect is on a boundary; summing its position gives the binary-word factor.

**Theorem 1.16 (boundary one column).**

$$\forall (m: \operatorname{Nat}), (\operatorname{KingDifference}.\operatorname{N_{e}}\left((\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{H}\left(0\right)\left((0: \operatorname{Fin}\left(1\right))\right): \operatorname{KingGrid}.\operatorname{Edge}\left(((m) + (1)) + (1)\right)\left(2\right))\right) = (6) \cdot ((2)^{m}))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.boundary_one_column` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

With one horizontal step, the boundary words disappear and the ordinary vertical word remains free.

**Theorem 1.17 (boundary slots one column).**

$$\forall (m: \operatorname{Nat}), (\operatorname{Nat}.\operatorname{card}\left(\{b: \operatorname{KingHorizontal}.\operatorname{BoundaryData}\left(m\right)\left(1\right) // (\operatorname{KingHorizontal}.\operatorname{BoundaryValid}\left((0: \operatorname{Fin}\left(1\right))\right)\left(b\right))\}\right) = (6) \cdot ((2)^{m}))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.boundary_slots_one_column` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

Valid boundary data with a single horizontal slot have six special-pair choices and a free binary vertical word.

**Theorem 1.18 (interior one column count).**

$$\forall (a: \operatorname{Nat}), (\forall (b: \operatorname{Nat}), (\operatorname{KingDifference}.\operatorname{N_{e}}\left((\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{H}\left(\operatorname{KingHorizontal}.\operatorname{cut_{row}}\left((a) + (1)\right)\left((b) + (1)\right)\right)\left((0: \operatorname{Fin}\left(1\right))\right): \operatorname{KingGrid}.\operatorname{Edge}\left((((a) + (1)) + ((b) + (1))) + (1)\right)\left(2\right))\right) = (36) \cdot ((2)^{(a) + (b)})))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.interior_one_column_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

With one horizontal step, the two boundary assignments have independent special pairs and vertical words.

**Theorem 1.19 (horizontal two columns).**

$$\forall (p: \operatorname{Nat}), (\operatorname{KingDifference}.\operatorname{N_{H}}\left((p) + (1)\right)\left(1\right) = (6) \cdot ((((3) \cdot (p)) + (2)) \cdot ((2)^{p})))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.horizontal_two_columns` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

Sum the two boundary rows and all interior rows for a rectangle with two columns.

**Theorem 1.20 (interior three rows count).**

$$\forall (c: \operatorname{Nat}), (\forall (d: \operatorname{Nat}), (\operatorname{KingDifference}.\operatorname{N_{e}}\left((\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{H}\left((1: \operatorname{Fin}\left(3\right))\right)\left(\operatorname{KingHorizontal}.\operatorname{pivot}\left(c\right)\left(d\right)\right): \operatorname{KingGrid}.\operatorname{Edge}\left(3\right)\left(((c) + ((d) + (1))) + (1)\right))\right) = (6) \cdot (((((2)^{(c) + (d)}) + ((2)^{c})) + ((2)^{d})) + (3))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.interior_three_rows_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

The unique interior row has no ordinary vertical words on either side of the defect.

**Theorem 1.21 (horizontal three rows).**

$$\forall (q: \operatorname{Nat}), ((\operatorname{KingDifference}.\operatorname{N_{H}}\left(2\right)\left((q) + (1)\right)) + (54) = (6) \cdot ((((q) + (13)) \cdot ((2)^{q})) + ((3) \cdot ((q) + (2)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.horizontal_three_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

Combine the two boundary-row counts with the unique interior-row count and sum all column positions.

**Theorem 1.22 (interior endpoint value).**

$$\forall (a: \operatorname{Nat}), (\forall (b: \operatorname{Nat}), (\forall (d: \operatorname{Nat}), ((0 < (a) + (b)) \Rightarrow ((0 < d) \Rightarrow (((((((\operatorname{KingHorizontal}.\operatorname{E}\left((a) + (b)\right)\left(0\right)\left(d\right)) + ((2)^{(a) + (b)})) + (\operatorname{KingHorizontal}.\operatorname{P}\left(a\right)\left(b\right)\left(0\right)\left(d\right))) + (\operatorname{KingHorizontal}.\operatorname{P}\left(a\right)\left(b\right)\left(d\right)\left(0\right))) + (\operatorname{KingHorizontal}.\operatorname{Q}\left(a\right)\left(b\right)\left(0\right)\left(d\right))) + (\operatorname{KingHorizontal}.\operatorname{Q}\left(a\right)\left(b\right)\left(d\right)\left(0\right))) + (2) = ((((2)^{((a) + (b)) + (1)}) + ((2)^{(d) + (1)})) + ((2)^{(a) + (1)})) + ((2)^{(b) + (1)}))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.interior_endpoint_value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

When a horizontal side is empty and both combined vertical and opposite horizontal lengths are positive, the six terms reduce to four powers of two.

**Theorem 1.23 (interior middle value).**

$$\forall (a: \operatorname{Nat}), (\forall (b: \operatorname{Nat}), (\forall (c: \operatorname{Nat}), (\forall (d: \operatorname{Nat}), ((0 < (a) + (b)) \Rightarrow ((0 < c) \Rightarrow ((0 < d) \Rightarrow ((((((\operatorname{KingHorizontal}.\operatorname{E}\left((a) + (b)\right)\left(c\right)\left(d\right)) + ((2)^{(a) + (b)})) + (\operatorname{KingHorizontal}.\operatorname{P}\left(a\right)\left(b\right)\left(c\right)\left(d\right))) + (\operatorname{KingHorizontal}.\operatorname{P}\left(a\right)\left(b\right)\left(d\right)\left(c\right))) + (\operatorname{KingHorizontal}.\operatorname{Q}\left(a\right)\left(b\right)\left(c\right)\left(d\right))) + (\operatorname{KingHorizontal}.\operatorname{Q}\left(a\right)\left(b\right)\left(d\right)\left(c\right)) = ((((2)^{((a) + (b)) + (1)}) + ((2)^{c})) + ((2)^{d})) + ((2) \cdot ((\operatorname{ite}\left(a = 0, 1, 0\right)) + (\operatorname{ite}\left(b = 0, 1, 0\right)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.interior_middle_value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

When both horizontal sides and the combined vertical length are positive, only the two empty-vertical-side indicators remain besides the powers of two.

**Theorem 1.24 (interior row sum).**

$$\forall (a: \operatorname{Nat}), (\forall (b: \operatorname{Nat}), (\forall (q: \operatorname{Nat}), ((0 < (a) + (b)) \Rightarrow ((\sum_{s: \operatorname{Fin}\left((q) + (2)\right)} (\operatorname{KingDifference}.\operatorname{N_{e}}\left((\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{H}\left(\operatorname{KingHorizontal}.\operatorname{cut_{row}}\left((a) + (1)\right)\left((b) + (1)\right)\right)\left(s\right): \operatorname{KingGrid}.\operatorname{Edge}\left((((a) + (1)) + ((b) + (1))) + (1)\right)\left(((q) + (2)) + (1)\right))\right))) + (48) = (6) \cdot (((((((q) + (2)) \cdot ((2)^{((a) + (b)) + (1)})) + ((3) \cdot ((2)^{(q) + (2)}))) + ((2)^{(a) + (2)})) + ((2)^{(b) + (2)})) + (((2) \cdot (q)) \cdot ((\operatorname{ite}\left(a = 0, 1, 0\right)) + (\operatorname{ite}\left(b = 0, 1, 0\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.interior_row_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

Sum the endpoint and middle column counts along a fixed interior row.

**Theorem 1.25 (boundary row sum).**

$$\forall (m: \operatorname{Nat}), (\forall (q: \operatorname{Nat}), ((0 < m) \Rightarrow (((\sum_{s: \operatorname{Fin}\left((q) + (2)\right)} (\operatorname{KingDifference}.\operatorname{N_{e}}\left((\operatorname{KingGrid}.\operatorname{Edge}.\operatorname{H}\left((0: \operatorname{Fin}\left((m) + (2)\right))\right)\left(s\right): \operatorname{KingGrid}.\operatorname{Edge}\left((m) + (2)\right)\left(((q) + (2)) + (1)\right))\right))) + ((12) \cdot ((q) + (2)))) + (12) = (6) \cdot ((((q) + (2)) \cdot ((2)^{m})) + ((2)^{(q) + (3)})))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.boundary_row_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

The two boundary-side powers form geometric sums over all column positions.

**Theorem 1.26 (horizontal sum).**

$$\forall (t: \operatorname{Nat}), (\forall (q: \operatorname{Nat}), ((\operatorname{KingDifference}.\operatorname{N_{H}}\left((t) + (3)\right)\left((q) + (2)\right)) + ((6) \cdot (((8) \cdot ((t) + (4))) + (4))) = (6) \cdot ((((((t) + (4)) \cdot ((q) + (2))) + (8)) \cdot ((2)^{(t) + (2)})) + ((((3) \cdot (t)) + (10)) \cdot ((2)^{(q) + (2)})))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.horizontal_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

Add the boundary rows and all interior rows, including their endpoint corrections.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.P`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.Q`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.boundary_one_column`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.boundary_row_sum`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.boundary_slots_one_column`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.horizontal_sum`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.horizontal_three_rows`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.horizontal_two_columns`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.horizontal_two_rows`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.interior_count`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.interior_count_support`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.interior_endpoint_value`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.interior_middle_value`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.interior_one_column_count`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.interior_row_sum`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.interior_three_rows_count`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.lower_pair`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.lower_pair_valid`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.lower_pair_values`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.pair_support_cases`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.six_case_value`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.support_case_count`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.support_case_eval`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.support_sizes`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.support_sizes_correct`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.supports`
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalSlots](KingHorizontalSlots.md)
