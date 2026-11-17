# Eight-colour complementary-pair exclusion

## Abstract

Barker's generating function for normalized eight-colour two-column arrays.

OEIS A233196, revision 12, counts arrays on n rows and two columns. Horizontal, vertical and antidiagonal bonds exclude equal colours and colours summing to seven. Main-diagonal neighbours are unconstrained. The first colour is zero. The three flags record previous occurrences of colours one, two and three, respectively. All Fin indices are zero-based; Fin.val is their natural value. Nat.sub is truncated subtraction, Nat.div is natural quotient division, and Nat.mod is its nonnegative remainder. Fin.ofNat 4 t has value Nat.mod t 4. No division enters the count or the power-series identity.

**Definition 1.1 (Three scanning flags).**

$$\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{Seen} = (\operatorname{Bool}) \times ((\operatorname{Bool}) \times (\operatorname{Bool}))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.Seen` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233196: eight-colour complementary-pair exclusion on a two-column strip*. URL: <https://oeis.org/A233196>.

*Commentary.*

The right-associated product records colours one, two and three.

**Definition 1.2 (The literal precedence restrictions).**

$$\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{Seen}), (\forall (c: \operatorname{Fin}\left(8\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{allowed}\left(s, c\right) = \left((((c = (2: \operatorname{Fin}\left(8\right))) \lor ((c = (3: \operatorname{Fin}\left(8\right))) \lor ((c = (4: \operatorname{Fin}\left(8\right))) \lor ((c = (5: \operatorname{Fin}\left(8\right))) \lor (c = (6: \operatorname{Fin}\left(8\right))))))) \Rightarrow (\operatorname{Prod}.\operatorname{fst}\left(s\right) = \operatorname{true})) \land ((((c = (3: \operatorname{Fin}\left(8\right))) \lor ((c = (4: \operatorname{Fin}\left(8\right))) \lor (c = (5: \operatorname{Fin}\left(8\right))))) \Rightarrow (\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Prod}.\operatorname{snd}\left(s\right)\right) = \operatorname{true})) \land ((c = (4: \operatorname{Fin}\left(8\right))) \Rightarrow (\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(s\right)\right) = \operatorname{true})))\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.allowed` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233196: eight-colour complementary-pair exclusion on a two-column strip*. URL: <https://oeis.org/A233196>.

*Commentary.*

A colour from 2,3,4,5,6 requires flag one. A colour from 3,4,5 requires flag two. Colour four requires flag three.

**Definition 1.3 (Advancing the scanner).**

$$\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{Seen}), (\forall (c: \operatorname{Fin}\left(8\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{advance}\left(s, c\right) = (\operatorname{Bool}.\operatorname{or}\left(\operatorname{Prod}.\operatorname{fst}\left(s\right), \operatorname{decide}\left(c = (1: \operatorname{Fin}\left(8\right))\right)\right), (\operatorname{Bool}.\operatorname{or}\left(\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Prod}.\operatorname{snd}\left(s\right)\right), \operatorname{decide}\left(c = (2: \operatorname{Fin}\left(8\right))\right)\right), \operatorname{Bool}.\operatorname{or}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(s\right)\right), \operatorname{decide}\left(c = (3: \operatorname{Fin}\left(8\right))\right)\right)))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.advance` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233196: eight-colour complementary-pair exclusion on a two-column strip*. URL: <https://oeis.org/A233196>.

*Commentary.*

The current colour can set its corresponding flag; flags never reset.

**Definition 1.4 (Scanning a finite row).**

$$(\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{Seen}), (\forall (f: (\operatorname{Fin}\left(0\right)) \to (\operatorname{Fin}\left(8\right))), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{good}\left(s, f\right) = \operatorname{True}))) \land (\forall (n: \operatorname{Nat}), (\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{Seen}), (\forall (f: (\operatorname{Fin}\left((n) + (1)\right)) \to (\operatorname{Fin}\left(8\right))), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{good}\left(s, f\right) = \left((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{allowed}\left(s, f\left((0: \operatorname{Fin}\left((n) + (1)\right))\right)\right)) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{good}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{advance}\left(s, f\left((0: \operatorname{Fin}\left((n) + (1)\right))\right)\right), \operatorname{Fin}.\operatorname{tail}\left(f\right)\right))\right)))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.good` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233196: eight-colour complementary-pair exclusion on a two-column strip*. URL: <https://oeis.org/A233196>.

*Commentary.*

The empty row satisfies the condition. A nonempty row checks its first colour before advancing the flags and scanning Fin.tail.

**Definition 1.5 (Flags at the end of a row).**

$$(\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{Seen}), (\forall (f: (\operatorname{Fin}\left(0\right)) \to (\operatorname{Fin}\left(8\right))), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{finish}\left(s, f\right) = s))) \land (\forall (n: \operatorname{Nat}), (\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{Seen}), (\forall (f: (\operatorname{Fin}\left((n) + (1)\right)) \to (\operatorname{Fin}\left(8\right))), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{finish}\left(s, f\right) = \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{finish}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{advance}\left(s, f\left((0: \operatorname{Fin}\left((n) + (1)\right))\right)\right), \operatorname{Fin}.\operatorname{tail}\left(f\right)\right)))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.finish` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233196: eight-colour complementary-pair exclusion on a two-column strip*. URL: <https://oeis.org/A233196>.

*Commentary.*

The terminal flags include every occurrence in the scanned row.

**Definition 1.6 (The complementary-pair map).**

$$\forall (c: \operatorname{Fin}\left(8\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{beta}\left(c\right) = \operatorname{Fin}.\operatorname{ofNat}\left(4, \operatorname{Nat}.\operatorname{min}\left(\operatorname{Fin}.\operatorname{val}\left(c\right), (7) - (\operatorname{Fin}.\operatorname{val}\left(c\right))\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.beta` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233196: eight-colour complementary-pair exclusion on a two-column strip*. URL: <https://oeis.org/A233196>.

*Commentary.*

The fibres are {0,7}, {1,6}, {2,5}, {3,4}. The minimum lies below four, so the Fin.ofNat remainder preserves it.

**Definition 1.7 (Rows of arbitrary width).**

$$\forall (k: \operatorname{Nat}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right) = \left((\operatorname{Fin}\left(k\right)) \to (\operatorname{Fin}\left(8\right))\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.WidthRow` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233196: eight-colour complementary-pair exclusion on a two-column strip*. URL: <https://oeis.org/A233196>.

*Commentary.*

The scanner is independent of the strip width.

**Definition 1.8 (An earlier row-major occurrence).**

$$\forall (k: \operatorname{Nat}), (\forall (n: \operatorname{Nat}), (\forall (f: (\operatorname{Fin}\left(n\right)) \to (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right))), (\forall (i: \operatorname{Fin}\left(n\right)), (\forall (j: \operatorname{Fin}\left(k\right)), (\forall (d: \operatorname{Fin}\left(8\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{prior}\left(f, i, j, d\right) = \exists (r: \operatorname{Fin}\left(n\right)), (\exists (t: \operatorname{Fin}\left(k\right)), (((r < i) \lor ((r = i) \land (t < j))) \land (f\left(r\right)\left(t\right) = d)))))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.prior` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233196: eight-colour complementary-pair exclusion on a two-column strip*. URL: <https://oeis.org/A233196>.

*Commentary.*

Strict lexicographic order first compares rows, then columns. This is equivalent to the order of i.val*k+j.val for indices in Fin n times Fin k.

**Definition 1.9 (Literal normalization at arbitrary width).**

$$\forall (k: \operatorname{Nat}), (\forall (n: \operatorname{Nat}), (\forall (f: (\operatorname{Fin}\left(n\right)) \to (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right))), (\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{Seen}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{widthNormal}\left(s, f\right) = \forall (i: \operatorname{Fin}\left(n\right)), (\forall (j: \operatorname{Fin}\left(k\right)), ((((f\left(i\right)\left(j\right) = (2: \operatorname{Fin}\left(8\right))) \lor ((f\left(i\right)\left(j\right) = (3: \operatorname{Fin}\left(8\right))) \lor ((f\left(i\right)\left(j\right) = (4: \operatorname{Fin}\left(8\right))) \lor ((f\left(i\right)\left(j\right) = (5: \operatorname{Fin}\left(8\right))) \lor (f\left(i\right)\left(j\right) = (6: \operatorname{Fin}\left(8\right))))))) \Rightarrow ((\operatorname{Prod}.\operatorname{fst}\left(s\right) = \operatorname{true}) \lor (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{prior}\left(f, i, j, (1: \operatorname{Fin}\left(8\right))\right)))) \land ((((f\left(i\right)\left(j\right) = (3: \operatorname{Fin}\left(8\right))) \lor ((f\left(i\right)\left(j\right) = (4: \operatorname{Fin}\left(8\right))) \lor (f\left(i\right)\left(j\right) = (5: \operatorname{Fin}\left(8\right))))) \Rightarrow ((\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Prod}.\operatorname{snd}\left(s\right)\right) = \operatorname{true}) \lor (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{prior}\left(f, i, j, (2: \operatorname{Fin}\left(8\right))\right)))) \land ((f\left(i\right)\left(j\right) = (4: \operatorname{Fin}\left(8\right))) \Rightarrow ((\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(s\right)\right) = \operatorname{true}) \lor (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{prior}\left(f, i, j, (3: \operatorname{Fin}\left(8\right))\right)))))))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.widthNormal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233196: eight-colour complementary-pair exclusion on a two-column strip*. URL: <https://oeis.org/A233196>.

*Commentary.*

The initial flags represent occurrences before the displayed array. Within the array, prior supplies the required earlier colour.

**Definition 1.10 (Two-column rows).**

$$\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{Row} = \left((\operatorname{Fin}\left(2\right)) \to (\operatorname{Fin}\left(8\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.Row` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233196: eight-colour complementary-pair exclusion on a two-column strip*. URL: <https://oeis.org/A233196>.

*Commentary.*

Each row is an ordered pair of colours.

**Definition 1.11 (Horizontal exclusion).**

$$\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{Row}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{rowLegal}\left(c\right) = \left((c\left((0: \operatorname{Fin}\left(2\right))\right) \ne c\left((1: \operatorname{Fin}\left(2\right))\right)) \land ((\operatorname{Fin}.\operatorname{val}\left(c\left((0: \operatorname{Fin}\left(2\right))\right)\right)) + (\operatorname{Fin}.\operatorname{val}\left(c\left((1: \operatorname{Fin}\left(2\right))\right)\right)) \ne 7)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.rowLegal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233196: eight-colour complementary-pair exclusion on a two-column strip*. URL: <https://oeis.org/A233196>.

*Commentary.*

The endpoints in columns zero and one must differ and not sum to seven.

**Definition 1.12 (Vertical and antidiagonal exclusion).**

$$\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{Row}), (\forall (d: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{Row}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{bonds}\left(c, d\right) = \left((\forall (j: \operatorname{Fin}\left(2\right)), ((c\left(j\right) \ne d\left(j\right)) \land ((\operatorname{Fin}.\operatorname{val}\left(c\left(j\right)\right)) + (\operatorname{Fin}.\operatorname{val}\left(d\left(j\right)\right)) \ne 7))) \land ((c\left((1: \operatorname{Fin}\left(2\right))\right) \ne d\left((0: \operatorname{Fin}\left(2\right))\right)) \land ((\operatorname{Fin}.\operatorname{val}\left(c\left((1: \operatorname{Fin}\left(2\right))\right)\right)) + (\operatorname{Fin}.\operatorname{val}\left(d\left((0: \operatorname{Fin}\left(2\right))\right)\right)) \ne 7))\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.bonds` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233196: eight-colour complementary-pair exclusion on a two-column strip*. URL: <https://oeis.org/A233196>.

*Commentary.*

Both vertical bonds and the bond from column one to the next column zero are constrained. The other diagonal is absent.

**Definition 1.13 (The literal array predicate).**

$$\forall (n: \operatorname{Nat}), (\forall (A: ((\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(2\right))) \to (\operatorname{Fin}\left(8\right))), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{Legal}\left(A\right) = \left((\exists (i: \operatorname{Fin}\left(n\right)), ((\operatorname{Fin}.\operatorname{val}\left(i\right) = 0) \land (A\left((i, (0: \operatorname{Fin}\left(2\right)))\right) = (0: \operatorname{Fin}\left(8\right))))) \land ((\forall (i: \operatorname{Fin}\left(n\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{rowLegal}\left(((j: \operatorname{Fin}\left(2\right)) \mapsto A\left((i, j)\right))\right))) \land ((\forall (i: \operatorname{Fin}\left(n\right)), (\forall (h: (\operatorname{Fin}.\operatorname{val}\left(i\right)) + (1) < n), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{bonds}\left(((j: \operatorname{Fin}\left(2\right)) \mapsto A\left((i, j)\right)), ((j: \operatorname{Fin}\left(2\right)) \mapsto A\left(((\operatorname{Fin}.\operatorname{mk}\left((\operatorname{Fin}.\operatorname{val}\left(i\right)) + (1), h\right): \operatorname{Fin}\left(n\right)), j)\right))\right)))) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{widthNormal}\left((\operatorname{false}, (\operatorname{false}, \operatorname{false})), ((i: \operatorname{Fin}\left(n\right)) \mapsto ((j: \operatorname{Fin}\left(2\right)) \mapsto A\left((i, j)\right)))\right))))\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.Legal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233196: eight-colour complementary-pair exclusion on a two-column strip*. URL: <https://oeis.org/A233196>.

*Commentary.*

The first-cell existential is false when n is zero. Every positive n fixes the unique row-zero, column-zero cell to colour zero.

**Definition 1.14 (The literal filtered Finset count).**

$$\forall (n: \operatorname{Nat}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{a}\left(n\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left(((A: ((\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(2\right))) \to (\operatorname{Fin}\left(8\right))) \mapsto \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{Legal}\left(A\right)), (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left(((\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(2\right))) \to (\operatorname{Fin}\left(8\right))\right))\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.a` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233196: eight-colour complementary-pair exclusion on a two-column strip*. URL: <https://oeis.org/A233196>.

*Commentary.*

Every function Fin n times Fin 2 to Fin 8 is filtered by Legal. The convention is a(0)=0, because the first-cell existential fails.

**Definition 1.15 (Boundary pair labels).**

$$\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{Row}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{pairs}\left(c\right) = (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{beta}\left(c\left((0: \operatorname{Fin}\left(2\right))\right)\right), \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{beta}\left(c\left((1: \operatorname{Fin}\left(2\right))\right)\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.pairs` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233196: eight-colour complementary-pair exclusion on a two-column strip*. URL: <https://oeis.org/A233196>.

*Commentary.*

The boundary retains the complementary-pair label of both columns.

**Definition 1.16 (Boundary compatibility).**

$$\forall (p: (\operatorname{Fin}\left(4\right)) \times (\operatorname{Fin}\left(4\right))), (\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{Row}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{compatible}\left(p, c\right) = \left((\operatorname{Prod}.\operatorname{fst}\left(p\right) \ne \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{beta}\left(c\left((0: \operatorname{Fin}\left(2\right))\right)\right)) \land ((\operatorname{Prod}.\operatorname{snd}\left(p\right) \ne \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{beta}\left(c\left((1: \operatorname{Fin}\left(2\right))\right)\right)) \land (\operatorname{Prod}.\operatorname{snd}\left(p\right) \ne \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{beta}\left(c\left((0: \operatorname{Fin}\left(2\right))\right)\right)))\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.compatible` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233196: eight-colour complementary-pair exclusion on a two-column strip*. URL: <https://oeis.org/A233196>.

*Commentary.*

These three pair-label inequalities express the two vertical and one antidiagonal exclusion constraints.

**Definition 1.17 (Reachable boundary states).**

$$\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{Seen}), (\forall (p: (\operatorname{Fin}\left(4\right)) \times (\operatorname{Fin}\left(4\right))), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{Valid}\left(s, p\right) = \left((\operatorname{Prod}.\operatorname{fst}\left(s\right) = \operatorname{true}) \land ((\operatorname{Prod}.\operatorname{fst}\left(p\right) \ne \operatorname{Prod}.\operatorname{snd}\left(p\right)) \land (((\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Prod}.\operatorname{snd}\left(s\right)\right) = \operatorname{false}) \Rightarrow ((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(p\right)\right) < 2) \land (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(p\right)\right) < 2))) \land (((\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(s\right)\right) = \operatorname{false}) \Rightarrow ((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(p\right)\right) < 3) \land (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(p\right)\right) < 3))) \land ((\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(s\right)\right) = \operatorname{true}) \Rightarrow (\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Prod}.\operatorname{snd}\left(s\right)\right) = \operatorname{true})))))\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.Valid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233196: eight-colour complementary-pair exclusion on a two-column strip*. URL: <https://oeis.org/A233196>.

*Commentary.*

After the first row, colour one has occurred. Before colour two occurs the labels are below two; before colour three occurs they are below three. A third flag implies the second flag.

**Definition 1.18 (The three continuation classes).**

$$\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{Seen}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{seenClass}\left(s\right) = (\operatorname{if} (\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(s\right)\right)) \operatorname{then} (2: \operatorname{Fin}\left(3\right)) \operatorname{else} (\operatorname{if} (\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Prod}.\operatorname{snd}\left(s\right)\right)) \operatorname{then} (1: \operatorname{Fin}\left(3\right)) \operatorname{else} (0: \operatorname{Fin}\left(3\right)))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.seenClass` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233196: eight-colour complementary-pair exclusion on a two-column strip*. URL: <https://oeis.org/A233196>.

*Commentary.*

Class zero has only colour one seen; class one has colour two seen but not three; class two has colour three seen.

**Definition 1.19 (The class transfer matrix).**

$$\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{T} = \operatorname{Matrix}.\operatorname{vecCons}\left(\operatorname{Matrix}.\operatorname{vecCons}\left((0: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((2: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((1: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecEmpty}\right)\right)\right), \operatorname{Matrix}.\operatorname{vecCons}\left(\operatorname{Matrix}.\operatorname{vecCons}\left((0: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((4: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((6: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecEmpty}\right)\right)\right), \operatorname{Matrix}.\operatorname{vecCons}\left(\operatorname{Matrix}.\operatorname{vecCons}\left((0: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((0: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((16: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecEmpty}\right)\right)\right), \operatorname{Matrix}.\operatorname{vecEmpty}\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.T` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233196: eight-colour complementary-pair exclusion on a two-column strip*. URL: <https://oeis.org/A233196>.

*Commentary.*

Rows and columns are indexed by Fin 3 in increasing order. The vector notation is expanded as Matrix.vecCons and Matrix.vecEmpty.

**Definition 1.20 (One-row class counts).**

$$\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{Seen}), (\forall (p: (\operatorname{Fin}\left(4\right)) \times (\operatorname{Fin}\left(4\right))), (\forall (b: \operatorname{Fin}\left(3\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{classCount}\left(s, p, b\right) = \sum_{(c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{Row})} ((\operatorname{if} ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{rowLegal}\left(c\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{compatible}\left(p, c\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{good}\left(s, c\right)) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{seenClass}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{finish}\left(s, c\right)\right) = b)))) \operatorname{then} (1: \operatorname{Int}) \operatorname{else} (0: \operatorname{Int}))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.classCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233196: eight-colour complementary-pair exclusion on a two-column strip*. URL: <https://oeis.org/A233196>.

*Commentary.*

The integer sum ranges over all two-column rows and records the final class.

**Definition 1.21 (First-row class counts).**

$$\forall (b: \operatorname{Fin}\left(3\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{firstCount}\left(b\right) = \sum_{(c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{Row})} ((\operatorname{if} ((c\left((0: \operatorname{Fin}\left(2\right))\right) = (0: \operatorname{Fin}\left(8\right))) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{rowLegal}\left(c\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{good}\left((\operatorname{false}, (\operatorname{false}, \operatorname{false})), c\right)) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{seenClass}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{finish}\left((\operatorname{false}, (\operatorname{false}, \operatorname{false})), c\right)\right) = b)))) \operatorname{then} (1: \operatorname{Int}) \operatorname{else} (0: \operatorname{Int}))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.firstCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233196: eight-colour complementary-pair exclusion on a two-column strip*. URL: <https://oeis.org/A233196>.

*Commentary.*

Only (0,1) is admissible as the first row, and it enters class zero.

**Theorem 1.22 (The finite class certificate).**

$$(\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{Seen}), (\forall (p: (\operatorname{Fin}\left(4\right)) \times (\operatorname{Fin}\left(4\right))), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{Valid}\left(s, p\right)) \Rightarrow (\forall (b: \operatorname{Fin}\left(3\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{classCount}\left(s, p, b\right) = \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{T}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{seenClass}\left(s\right), b\right)))))) \land ((\forall (b: \operatorname{Fin}\left(3\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{firstCount}\left(b\right) = (\operatorname{if} (b = (0: \operatorname{Fin}\left(3\right))) \operatorname{then} (1: \operatorname{Int}) \operatorname{else} (0: \operatorname{Int})))) \land (\operatorname{Matrix}.\operatorname{mulVec}\left((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{T})^{((1) + (2))}, (1: (\operatorname{Fin}\left(3\right)) \to (\operatorname{Int}))\right) = \sum_{(j: \operatorname{Fin}\left(2\right))} (\operatorname{HSMul}.\operatorname{hSMul}\left(\operatorname{Matrix}.\operatorname{vecCons}\left(-(64: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecCons}\left((20: \operatorname{Int}), \operatorname{Matrix}.\operatorname{vecEmpty}\right)\right)\left(j\right), \operatorname{Matrix}.\operatorname{mulVec}\left((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{T})^{((1) + (\operatorname{Fin}.\operatorname{val}\left(j\right)))}, (1: (\operatorname{Fin}\left(3\right)) \to (\operatorname{Int}))\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.finite_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233196: eight-colour complementary-pair exclusion on a two-column strip*. URL: <https://oeis.org/A233196>.

*Commentary.*

From class zero the counts are (0,2,1); from class one they are (0,4,6); from class two they are (0,0,16). The initial vector is (1,0,0). The last identity annihilates the transient zero eigenvalue and gives the quadratic recurrence on every later continuation.

**Theorem 1.23 (Barker's generating function).**

$$(((1) - ((4) \cdot ((\operatorname{PowerSeries}.\operatorname{X}: \operatorname{PowerSeries}\left(\operatorname{Int}\right))))) \cdot ((1) - ((16) \cdot ((\operatorname{PowerSeries}.\operatorname{X}: \operatorname{PowerSeries}\left(\operatorname{Int}\right)))))) \cdot (\operatorname{PowerSeries}.\operatorname{mk}\left(((n: \operatorname{Nat}) \mapsto (\operatorname{Nat}.\operatorname{cast}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{a}\left(n\right)\right): \operatorname{Int}))\right)) = ((\operatorname{PowerSeries}.\operatorname{X}: \operatorname{PowerSeries}\left(\operatorname{Int}\right))) \cdot (((1) - ((17) \cdot ((\operatorname{PowerSeries}.\operatorname{X}: \operatorname{PowerSeries}\left(\operatorname{Int}\right))))) + ((40) \cdot (((\operatorname{PowerSeries}.\operatorname{X}: \operatorname{PowerSeries}\left(\operatorname{Int}\right)))^{(2)})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin233196` (proved) by `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin233196","declaration_gid":"D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233196: eight-colour complementary-pair exclusion on a two-column strip*. URL: <https://oeis.org/A233196>.

*Commentary.*

Let w(n) be Matrix.mulVec (T^n) 1. Splitting a literal array into its first row and remaining rows gives a(n+1)=w(n)(0). The finite certificate and TransferMatrix.scalarRelationShift give a(n+4)=20*a(n+3)-64*a(n+2) for every natural n. The first three positive counts are 1,3,36. Comparing coefficients, including a(0)=0, proves the identity in PowerSeries Int. The counts are cast from Nat to Int before forming the series.

**Definition 1.24 (Deciding colour precedence).**

$$\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{Seen}), (\forall (c: \operatorname{Fin}\left(8\right)), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{instDecidableAllowed}\left(s, c\right): \operatorname{Decidable}\left((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{allowed}\left(s, c\right))\right)) = \operatorname{inferInstanceAs}\left((\operatorname{Decidable}\left(((((c = (2: \operatorname{Fin}\left(8\right))) \lor ((c = (3: \operatorname{Fin}\left(8\right))) \lor ((c = (4: \operatorname{Fin}\left(8\right))) \lor ((c = (5: \operatorname{Fin}\left(8\right))) \lor (c = (6: \operatorname{Fin}\left(8\right))))))) \Rightarrow (\operatorname{Prod}.\operatorname{fst}\left(s\right) = \operatorname{Bool}.\operatorname{true})) \land ((((c = (3: \operatorname{Fin}\left(8\right))) \lor ((c = (4: \operatorname{Fin}\left(8\right))) \lor (c = (5: \operatorname{Fin}\left(8\right))))) \Rightarrow (\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Prod}.\operatorname{snd}\left(s\right)\right) = \operatorname{Bool}.\operatorname{true})) \land ((c = (4: \operatorname{Fin}\left(8\right))) \Rightarrow (\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(s\right)\right) = \operatorname{Bool}.\operatorname{true}))))\right))\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.instDecidableAllowed` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233196: eight-colour complementary-pair exclusion on a two-column strip*. URL: <https://oeis.org/A233196>.

*Commentary.*

The defining expression is inferInstanceAs for the three implications.

**Theorem 1.25 (The first terminal flag).**

$$\forall (n: \operatorname{Nat}), (\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{Seen}), (\forall (f: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(8\right))), ((\operatorname{Prod}.\operatorname{fst}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{finish}\left(s, f\right)\right) = \operatorname{Bool}.\operatorname{true}) \iff ((\operatorname{Prod}.\operatorname{fst}\left(s\right) = \operatorname{Bool}.\operatorname{true}) \lor (\exists (i: \operatorname{Fin}\left(n\right)), (f\left(i\right) = (1: \operatorname{Fin}\left(8\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.finish_fst` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233196: eight-colour complementary-pair exclusion on a two-column strip*. URL: <https://oeis.org/A233196>.

*Commentary.*

The first flag records an initial flag or an occurrence of colour one.

**Theorem 1.26 (The second terminal flag).**

$$\forall (n: \operatorname{Nat}), (\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{Seen}), (\forall (f: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(8\right))), ((\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{finish}\left(s, f\right)\right)\right) = \operatorname{Bool}.\operatorname{true}) \iff ((\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Prod}.\operatorname{snd}\left(s\right)\right) = \operatorname{Bool}.\operatorname{true}) \lor (\exists (i: \operatorname{Fin}\left(n\right)), (f\left(i\right) = (2: \operatorname{Fin}\left(8\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.finish_snd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233196: eight-colour complementary-pair exclusion on a two-column strip*. URL: <https://oeis.org/A233196>.

*Commentary.*

The second flag records an initial flag or an occurrence of colour two.

**Theorem 1.27 (The third terminal flag).**

$$\forall (n: \operatorname{Nat}), (\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{Seen}), (\forall (f: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(8\right))), ((\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{finish}\left(s, f\right)\right)\right) = \operatorname{Bool}.\operatorname{true}) \iff ((\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(s\right)\right) = \operatorname{Bool}.\operatorname{true}) \lor (\exists (i: \operatorname{Fin}\left(n\right)), (f\left(i\right) = (3: \operatorname{Fin}\left(8\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.finish_third` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233196: eight-colour complementary-pair exclusion on a two-column strip*. URL: <https://oeis.org/A233196>.

*Commentary.*

The third flag records an initial flag or an occurrence of colour three.

**Theorem 1.28 (The scanner is the earlier-colour condition).**

$$\forall (n: \operatorname{Nat}), (\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{Seen}), (\forall (f: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(8\right))), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{good}\left(s, f\right)) \iff (\forall (i: \operatorname{Fin}\left(n\right)), ((((f\left(i\right) = (2: \operatorname{Fin}\left(8\right))) \lor ((f\left(i\right) = (3: \operatorname{Fin}\left(8\right))) \lor ((f\left(i\right) = (4: \operatorname{Fin}\left(8\right))) \lor ((f\left(i\right) = (5: \operatorname{Fin}\left(8\right))) \lor (f\left(i\right) = (6: \operatorname{Fin}\left(8\right))))))) \Rightarrow ((\operatorname{Prod}.\operatorname{fst}\left(s\right) = \operatorname{Bool}.\operatorname{true}) \lor (\exists (j: \operatorname{Fin}\left(n\right)), ((j < i) \land (f\left(j\right) = (1: \operatorname{Fin}\left(8\right))))))) \land ((((f\left(i\right) = (3: \operatorname{Fin}\left(8\right))) \lor ((f\left(i\right) = (4: \operatorname{Fin}\left(8\right))) \lor (f\left(i\right) = (5: \operatorname{Fin}\left(8\right))))) \Rightarrow ((\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Prod}.\operatorname{snd}\left(s\right)\right) = \operatorname{Bool}.\operatorname{true}) \lor (\exists (j: \operatorname{Fin}\left(n\right)), ((j < i) \land (f\left(j\right) = (2: \operatorname{Fin}\left(8\right))))))) \land ((f\left(i\right) = (4: \operatorname{Fin}\left(8\right))) \Rightarrow ((\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(s\right)\right) = \operatorname{Bool}.\operatorname{true}) \lor (\exists (j: \operatorname{Fin}\left(n\right)), ((j < i) \land (f\left(j\right) = (3: \operatorname{Fin}\left(8\right)))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.good_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233196: eight-colour complementary-pair exclusion on a two-column strip*. URL: <https://oeis.org/A233196>.

*Commentary.*

Each required colour occurs at a strictly earlier finite index or is already recorded by the initial flags.

**Theorem 1.29 (A bond depends on complementary pairs).**

$$\forall (x: \operatorname{Fin}\left(8\right)), (\forall (y: \operatorname{Fin}\left(8\right)), (((x \ne y) \land ((\operatorname{Fin}.\operatorname{val}\left(x\right)) + (\operatorname{Fin}.\operatorname{val}\left(y\right)) \ne 7)) \iff (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{beta}\left(x\right) \ne \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{beta}\left(y\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.colour_bond_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233196: eight-colour complementary-pair exclusion on a two-column strip*. URL: <https://oeis.org/A233196>.

*Commentary.*

Unequal colours that do not sum to seven have distinct pair labels.

**Definition 1.30 (Deciding an earlier occurrence).**

$$\forall (k: \operatorname{Nat}), (\forall (n: \operatorname{Nat}), (\forall (f: (\operatorname{Fin}\left(n\right)) \to (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right))), (\forall (i: \operatorname{Fin}\left(n\right)), (\forall (j: \operatorname{Fin}\left(k\right)), (\forall (d: \operatorname{Fin}\left(8\right)), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{instDecidablePrior}\left(f, i, j, d\right): \operatorname{Decidable}\left((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{prior}\left(f, i, j, d\right))\right)) = \operatorname{inferInstanceAs}\left((\operatorname{Decidable}\left((\exists (r: \operatorname{Fin}\left(n\right)), (\exists (t: \operatorname{Fin}\left(k\right)), (((r < i) \lor ((r = i) \land (t < j))) \land (f\left(r\right)\left(t\right) = d))))\right))\right)))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.instDecidablePrior` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233196: eight-colour complementary-pair exclusion on a two-column strip*. URL: <https://oeis.org/A233196>.

*Commentary.*

The defining expression is inferInstanceAs for the finite existential.

**Theorem 1.31 (Earlier occurrences in the first row).**

$$\forall (k: \operatorname{Nat}), (\forall (n: \operatorname{Nat}), (\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right)), (\forall (f: (\operatorname{Fin}\left(n\right)) \to (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right))), (\forall (j: \operatorname{Fin}\left(k\right)), (\forall (d: \operatorname{Fin}\left(8\right)), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{prior}\left(\operatorname{Fin}.\operatorname{cons}\left(c, f\right), (0: \operatorname{Fin}\left((n) + (1)\right)), j, d\right)) \iff (\exists (t: \operatorname{Fin}\left(k\right)), ((t < j) \land (c\left(t\right) = d)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.prior_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233196: eight-colour complementary-pair exclusion on a two-column strip*. URL: <https://oeis.org/A233196>.

*Commentary.*

Only an earlier column in the first row can precede its current cell.

**Theorem 1.32 (Earlier occurrences after the first row).**

$$\forall (k: \operatorname{Nat}), (\forall (n: \operatorname{Nat}), (\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right)), (\forall (f: (\operatorname{Fin}\left(n\right)) \to (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right))), (\forall (i: \operatorname{Fin}\left(n\right)), (\forall (j: \operatorname{Fin}\left(k\right)), (\forall (d: \operatorname{Fin}\left(8\right)), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{prior}\left(\operatorname{Fin}.\operatorname{cons}\left(c, f\right), \operatorname{Fin}.\operatorname{succ}\left(i\right), j, d\right)) \iff ((\exists (t: \operatorname{Fin}\left(k\right)), (c\left(t\right) = d)) \lor (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{prior}\left(f, i, j, d\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.prior_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233196: eight-colour complementary-pair exclusion on a two-column strip*. URL: <https://oeis.org/A233196>.

*Commentary.*

An earlier occurrence is in the first row or earlier in the tail.

**Theorem 1.33 (Splitting row-major normalization).**

$$\forall (k: \operatorname{Nat}), (\forall (n: \operatorname{Nat}), (\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{Seen}), (\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right)), (\forall (f: (\operatorname{Fin}\left(n\right)) \to (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right))), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{widthNormal}\left(s, \operatorname{Fin}.\operatorname{cons}\left(c, f\right)\right)) \iff ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{good}\left(s, c\right)) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{widthNormal}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{finish}\left(s, c\right), f\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.normal_cons` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233196: eight-colour complementary-pair exclusion on a two-column strip*. URL: <https://oeis.org/A233196>.

*Commentary.*

The first row is scanned from s; its terminal flags initialize the tail.

**Definition 1.34 (Literal legality at arbitrary positive width).**

$$\forall (k: \operatorname{Nat}), ([\operatorname{NeZero}\left(k\right)] (\forall (R: (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right)) \to (\operatorname{Prop})), (\forall (E: (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right)) \to ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right)) \to (\operatorname{Prop}))), (\forall (n: \operatorname{Nat}), (\forall (A: ((\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(k\right))) \to (\operatorname{Fin}\left(8\right))), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{widthLegal}\left(R, E, A\right) = ((\exists (i: \operatorname{Fin}\left(n\right)), ((\operatorname{Fin}.\operatorname{val}\left(i\right) = 0) \land (A\left((i, (0: \operatorname{Fin}\left(k\right)))\right) = (0: \operatorname{Fin}\left(8\right))))) \land ((\forall (i: \operatorname{Fin}\left(n\right)), (R\left(((j: \operatorname{Fin}\left(k\right)) \mapsto A\left((i, j)\right))\right))) \land ((\forall (i: \operatorname{Fin}\left(n\right)), (\forall (h: (\operatorname{Fin}.\operatorname{val}\left(i\right)) + (1) < n), (E\left(((j: \operatorname{Fin}\left(k\right)) \mapsto A\left((i, j)\right)), ((j: \operatorname{Fin}\left(k\right)) \mapsto A\left(((\operatorname{Fin}.\operatorname{mk}\left((\operatorname{Fin}.\operatorname{val}\left(i\right)) + (1), h\right): \operatorname{Fin}\left(n\right)), j)\right))\right)))) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{widthNormal}\left((\operatorname{Bool}.\operatorname{false}, (\operatorname{Bool}.\operatorname{false}, \operatorname{Bool}.\operatorname{false})), ((i: \operatorname{Fin}\left(n\right)) \mapsto ((j: \operatorname{Fin}\left(k\right)) \mapsto A\left((i, j)\right)))\right)))))))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.widthLegal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233196: eight-colour complementary-pair exclusion on a two-column strip*. URL: <https://oeis.org/A233196>.

*Commentary.*

The first cell is zero, rows satisfy R, consecutive rows satisfy E, and all cells satisfy row-major normalization.

**Definition 1.35 (Deciding normalization).**

$$\forall (k: \operatorname{Nat}), (\forall (n: \operatorname{Nat}), (\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{Seen}), (\forall (f: (\operatorname{Fin}\left(n\right)) \to (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right))), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{widthInstDecidableNormal}\left(s, f\right): \operatorname{Decidable}\left((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{widthNormal}\left(s, f\right))\right)) = \operatorname{inferInstanceAs}\left((\operatorname{Decidable}\left((\forall (i: \operatorname{Fin}\left(n\right)), (\forall (j: \operatorname{Fin}\left(k\right)), ((((f\left(i\right)\left(j\right) = (2: \operatorname{Fin}\left(8\right))) \lor ((f\left(i\right)\left(j\right) = (3: \operatorname{Fin}\left(8\right))) \lor ((f\left(i\right)\left(j\right) = (4: \operatorname{Fin}\left(8\right))) \lor ((f\left(i\right)\left(j\right) = (5: \operatorname{Fin}\left(8\right))) \lor (f\left(i\right)\left(j\right) = (6: \operatorname{Fin}\left(8\right))))))) \Rightarrow ((\operatorname{Prod}.\operatorname{fst}\left(s\right) = \operatorname{Bool}.\operatorname{true}) \lor (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{prior}\left(f, i, j, (1: \operatorname{Fin}\left(8\right))\right)))) \land ((((f\left(i\right)\left(j\right) = (3: \operatorname{Fin}\left(8\right))) \lor ((f\left(i\right)\left(j\right) = (4: \operatorname{Fin}\left(8\right))) \lor (f\left(i\right)\left(j\right) = (5: \operatorname{Fin}\left(8\right))))) \Rightarrow ((\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Prod}.\operatorname{snd}\left(s\right)\right) = \operatorname{Bool}.\operatorname{true}) \lor (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{prior}\left(f, i, j, (2: \operatorname{Fin}\left(8\right))\right)))) \land ((f\left(i\right)\left(j\right) = (4: \operatorname{Fin}\left(8\right))) \Rightarrow ((\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Prod}.\operatorname{snd}\left(s\right)\right) = \operatorname{Bool}.\operatorname{true}) \lor (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{prior}\left(f, i, j, (3: \operatorname{Fin}\left(8\right))\right))))))))\right))\right)))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.widthInstDecidableNormal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233196: eight-colour complementary-pair exclusion on a two-column strip*. URL: <https://oeis.org/A233196>.

*Commentary.*

The defining expression is inferInstanceAs for the finite universal.

**Definition 1.36 (Deciding a row scan).**

$$\begin{aligned}\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{Seen}), (\forall (c: (\operatorname{Fin}\left(0\right)) \to (\operatorname{Fin}\left(8\right))), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{widthInstDecidableGood}\left(s, c\right): \operatorname{Decidable}\left((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{good}\left(s, c\right))\right)) = \operatorname{Decidable}.\operatorname{isTrue}\left(\operatorname{True}.\operatorname{intro}\right)))\\\forall (k: \operatorname{Nat}), (\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{Seen}), (\forall (c: (\operatorname{Fin}\left((k) + (1)\right)) \to (\operatorname{Fin}\left(8\right))), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{widthInstDecidableGood}\left(s, c\right): \operatorname{Decidable}\left((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{good}\left(s, c\right))\right)) = \operatorname{instDecidableAnd}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{instDecidableAllowed}\left(s, c\left((0: \operatorname{Fin}\left((k) + (1)\right))\right)\right), \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{widthInstDecidableGood}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{advance}\left(s, c\left((0: \operatorname{Fin}\left((k) + (1)\right))\right)\right), \operatorname{Fin}.\operatorname{tail}\left(c\right)\right)\right))))\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.widthInstDecidableGood` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233196: eight-colour complementary-pair exclusion on a two-column strip*. URL: <https://oeis.org/A233196>.

*Commentary.*

The defining induction combines the allowed decision with the tail decision.

**Definition 1.37 (Deciding legality).**

$$\forall (k: \operatorname{Nat}), ([\operatorname{NeZero}\left(k\right)] (\forall (R: (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right)) \to (\operatorname{Prop})), (\forall (E: (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right)) \to ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right)) \to (\operatorname{Prop}))), ([\operatorname{DecidablePred}\left(R\right)] ([\operatorname{DecidableRel}\left(E\right)] (\forall (n: \operatorname{Nat}), (\forall (A: ((\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(k\right))) \to (\operatorname{Fin}\left(8\right))), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{widthInstDecidableLegal}\left(R, E, A\right): \operatorname{Decidable}\left((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{widthLegal}\left(R, E, A\right))\right)) = \operatorname{inferInstanceAs}\left((\operatorname{Decidable}\left(((\exists (i: \operatorname{Fin}\left(n\right)), ((\operatorname{Fin}.\operatorname{val}\left(i\right) = 0) \land (A\left((i, (0: \operatorname{Fin}\left(k\right)))\right) = (0: \operatorname{Fin}\left(8\right))))) \land ((\forall (i: \operatorname{Fin}\left(n\right)), (R\left(((j: \operatorname{Fin}\left(k\right)) \mapsto A\left((i, j)\right))\right))) \land ((\forall (i: \operatorname{Fin}\left(n\right)), (\forall (h: (\operatorname{Fin}.\operatorname{val}\left(i\right)) + (1) < n), (E\left(((j: \operatorname{Fin}\left(k\right)) \mapsto A\left((i, j)\right)), ((j: \operatorname{Fin}\left(k\right)) \mapsto A\left(((\operatorname{Fin}.\operatorname{mk}\left((\operatorname{Fin}.\operatorname{val}\left(i\right)) + (1), h\right): \operatorname{Fin}\left(n\right)), j)\right))\right)))) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{widthNormal}\left((\operatorname{Bool}.\operatorname{false}, (\operatorname{Bool}.\operatorname{false}, \operatorname{Bool}.\operatorname{false})), ((i: \operatorname{Fin}\left(n\right)) \mapsto ((j: \operatorname{Fin}\left(k\right)) \mapsto A\left((i, j)\right)))\right)))))\right))\right)))))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.widthInstDecidableLegal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233196: eight-colour complementary-pair exclusion on a two-column strip*. URL: <https://oeis.org/A233196>.

*Commentary.*

The defining expression is inferInstanceAs for the four legality conjuncts.

**Definition 1.38 (Legal normalized continuations).**

$$\forall (k: \operatorname{Nat}), (\forall (B: \operatorname{Type}), (\forall (R: (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right)) \to (\operatorname{Prop})), (\forall (P: (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right)) \to (B)), (\forall (C: (B) \to ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right)) \to (\operatorname{Prop}))), ((\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{Seen}), (\forall (p: B), (\forall (f: (\operatorname{Fin}\left(0\right)) \to (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right))), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{TailGood}\left(R, P, C, s, p, f\right) = \operatorname{True})))) \land (\forall (n: \operatorname{Nat}), (\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{Seen}), (\forall (p: B), (\forall (f: (\operatorname{Fin}\left((n) + (1)\right)) \to (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right))), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{TailGood}\left(R, P, C, s, p, f\right) = ((R\left(f\left((0: \operatorname{Fin}\left((n) + (1)\right))\right)\right)) \land ((C\left(p, f\left((0: \operatorname{Fin}\left((n) + (1)\right))\right)\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{good}\left(s, f\left((0: \operatorname{Fin}\left((n) + (1)\right))\right)\right)) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{TailGood}\left(R, P, C, \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{finish}\left(s, f\left((0: \operatorname{Fin}\left((n) + (1)\right))\right)\right), P\left(f\left((0: \operatorname{Fin}\left((n) + (1)\right))\right)\right), \operatorname{Fin}.\operatorname{tail}\left(f\right)\right)))))))))))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.TailGood` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233196: eight-colour complementary-pair exclusion on a two-column strip*. URL: <https://oeis.org/A233196>.

*Commentary.*

The empty continuation is true. A nonempty continuation checks R, C and good, then updates both the scanning flags and the boundary.

**Definition 1.39 (Deciding a continuation).**

$$\forall (k: \operatorname{Nat}), (\forall (B: \operatorname{Type}), (\forall (R: (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right)) \to (\operatorname{Prop})), (\forall (P: (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right)) \to (B)), (\forall (C: (B) \to ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right)) \to (\operatorname{Prop}))), ([instR: \operatorname{DecidablePred}\left(R\right)] ([instC: \operatorname{DecidableRel}\left(C\right)] (\begin{aligned}\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{Seen}), (\forall (p: B), (\forall (f: (\operatorname{Fin}\left(0\right)) \to (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right))), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{instDecidableTailGood}\left(R, P, C, s, p, f\right): \operatorname{Decidable}\left((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{TailGood}\left(R, P, C, s, p, f\right))\right)) = \operatorname{Decidable}.\operatorname{isTrue}\left(\operatorname{True}.\operatorname{intro}\right))))\\\forall (n: \operatorname{Nat}), (\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{Seen}), (\forall (p: B), (\forall (f: (\operatorname{Fin}\left((n) + (1)\right)) \to (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right))), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{instDecidableTailGood}\left(R, P, C, s, p, f\right): \operatorname{Decidable}\left((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{TailGood}\left(R, P, C, s, p, f\right))\right)) = \operatorname{instDecidableAnd}\left(instR\left(f\left((0: \operatorname{Fin}\left((n) + (1)\right))\right)\right), \operatorname{instDecidableAnd}\left(instC\left(p, f\left((0: \operatorname{Fin}\left((n) + (1)\right))\right)\right), \operatorname{instDecidableAnd}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{widthInstDecidableGood}\left(s, f\left((0: \operatorname{Fin}\left((n) + (1)\right))\right)\right), \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{instDecidableTailGood}\left(R, P, C, \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{finish}\left(s, f\left((0: \operatorname{Fin}\left((n) + (1)\right))\right)\right), P\left(f\left((0: \operatorname{Fin}\left((n) + (1)\right))\right)\right), \operatorname{Fin}.\operatorname{tail}\left(f\right)\right)\right)\right)\right)))))\end{aligned})))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.instDecidableTailGood` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233196: eight-colour complementary-pair exclusion on a two-column strip*. URL: <https://oeis.org/A233196>.

*Commentary.*

The defining induction decides the three current-row predicates and the recursive continuation with the updated flags and boundary.

**Theorem 1.40 (Continuation legality in literal form).**

$$\forall (k: \operatorname{Nat}), (\forall (B: \operatorname{Type}), (\forall (R: (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right)) \to (\operatorname{Prop})), (\forall (P: (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right)) \to (B)), (\forall (C: (B) \to ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right)) \to (\operatorname{Prop}))), (\forall (E: (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right)) \to ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right)) \to (\operatorname{Prop}))), (\forall (edge: \forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right)), (\forall (d: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right)), ((E\left(c, d\right)) \iff (C\left(P\left(c\right), d\right))))), (\forall (n: \operatorname{Nat}), (\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{Seen}), (\forall (p: B), (\forall (f: (\operatorname{Fin}\left(n\right)) \to (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right))), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{TailGood}\left(R, P, C, s, p, f\right)) \iff ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{widthNormal}\left(s, f\right)) \land ((\forall (i: \operatorname{Fin}\left(n\right)), (R\left(f\left(i\right)\right))) \land ((\forall (i: \operatorname{Fin}\left(n\right)), (\forall (h: (\operatorname{Fin}.\operatorname{val}\left(i\right)) + (1) < n), (E\left(f\left(i\right), f\left((\operatorname{Fin}.\operatorname{mk}\left((\operatorname{Fin}.\operatorname{val}\left(i\right)) + (1), h\right): \operatorname{Fin}\left(n\right))\right)\right)))) \land (\forall (h: 0 < n), (C\left(p, f\left((\operatorname{Fin}.\operatorname{mk}\left(0, h\right): \operatorname{Fin}\left(n\right))\right)\right)))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.tail_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233196: eight-colour complementary-pair exclusion on a two-column strip*. URL: <https://oeis.org/A233196>.

*Commentary.*

Assume E c d is equivalent to C (P c) d. Normalization, row legality, consecutive-row bonds and the initial boundary condition are then equivalent to TailGood, including the empty continuation.

**Definition 1.41 (One continuation transfer).**

$$\forall (k: \operatorname{Nat}), (\forall (B: \operatorname{Type}), (\forall (R: (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right)) \to (\operatorname{Prop})), (\forall (P: (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right)) \to (B)), (\forall (C: (B) \to ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right)) \to (\operatorname{Prop}))), ([\operatorname{DecidablePred}\left(R\right)] ([\operatorname{DecidableRel}\left(C\right)] (\forall (w: (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{Seen}) \to ((B) \to (\operatorname{Int}))), (\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{Seen}), (\forall (p: B), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{widthStep}\left(R, P, C, w, s, p\right) = \sum_{(c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right))} ((\operatorname{if} ((R\left(c\right)) \land ((C\left(p, c\right)) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{good}\left(s, c\right)))) \operatorname{then} w\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{finish}\left(s, c\right), P\left(c\right)\right) \operatorname{else} (0: \operatorname{Int})))))))))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.widthStep` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233196: eight-colour complementary-pair exclusion on a two-column strip*. URL: <https://oeis.org/A233196>.

*Commentary.*

The integer sum ranges over all rows, retaining exactly R, C and good.

**Definition 1.42 (Continuation vectors at arbitrary width).**

$$\forall (k: \operatorname{Nat}), (\forall (B: \operatorname{Type}), (\forall (R: (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right)) \to (\operatorname{Prop})), (\forall (P: (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right)) \to (B)), (\forall (C: (B) \to ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right)) \to (\operatorname{Prop}))), ([\operatorname{DecidablePred}\left(R\right)] ([\operatorname{DecidableRel}\left(C\right)] ((\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{Seen}), (\forall (p: B), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{widthV}\left(R, P, C, 0\right)\left(s, p\right) = (1: \operatorname{Int})))) \land (\forall (n: \operatorname{Nat}), (\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{Seen}), (\forall (p: B), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{widthV}\left(R, P, C, (n) + (1)\right)\left(s, p\right) = \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{widthStep}\left(R, P, C, \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{widthV}\left(R, P, C, n\right), s, p\right))))))))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.widthV` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233196: eight-colour complementary-pair exclusion on a two-column strip*. URL: <https://oeis.org/A233196>.

*Commentary.*

The empty continuation has weight one; each further row applies widthStep.

**Definition 1.43 (The literal continuation count).**

$$\forall (k: \operatorname{Nat}), (\forall (B: \operatorname{Type}), (\forall (R: (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right)) \to (\operatorname{Prop})), (\forall (P: (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right)) \to (B)), (\forall (C: (B) \to ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right)) \to (\operatorname{Prop}))), ([\operatorname{DecidablePred}\left(R\right)] ([\operatorname{DecidableRel}\left(C\right)] (\forall (n: \operatorname{Nat}), (\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{Seen}), (\forall (p: B), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{count}\left(R, P, C, n, s, p\right) = \sum_{(f: (\operatorname{Fin}\left(n\right)) \to (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right)))} ((\operatorname{if} (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{TailGood}\left(R, P, C, s, p, f\right)) \operatorname{then} (1: \operatorname{Int}) \operatorname{else} (0: \operatorname{Int})))))))))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.count` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233196: eight-colour complementary-pair exclusion on a two-column strip*. URL: <https://oeis.org/A233196>.

*Commentary.*

The integer sum ranges over every finite sequence of rows and tests TailGood.

**Theorem 1.44 (Literal and recursive continuation counts).**

$$\forall (k: \operatorname{Nat}), (\forall (B: \operatorname{Type}), (\forall (R: (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right)) \to (\operatorname{Prop})), (\forall (P: (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right)) \to (B)), (\forall (C: (B) \to ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right)) \to (\operatorname{Prop}))), ([\operatorname{DecidablePred}\left(R\right)] ([\operatorname{DecidableRel}\left(C\right)] (\forall (n: \operatorname{Nat}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{count}\left(R, P, C, n\right) = \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{widthV}\left(R, P, C, n\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.count_eq_v` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233196: eight-colour complementary-pair exclusion on a two-column strip*. URL: <https://oeis.org/A233196>.

*Commentary.*

The equality is between functions of the scanning flags and boundary.

**Definition 1.45 (First-row aggregation).**

$$\forall (k: \operatorname{Nat}), ([\operatorname{NeZero}\left(k\right)] (\forall (B: \operatorname{Type}), (\forall (R: (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right)) \to (\operatorname{Prop})), (\forall (P: (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right)) \to (B)), ([\operatorname{DecidablePred}\left(R\right)] (\forall (w: (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{Seen}) \to ((B) \to (\operatorname{Int}))), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{widthTotal}\left(R, P, w\right) = \sum_{(c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right))} ((\operatorname{if} ((c\left((0: \operatorname{Fin}\left(k\right))\right) = (0: \operatorname{Fin}\left(8\right))) \land ((R\left(c\right)) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{good}\left((\operatorname{Bool}.\operatorname{false}, (\operatorname{Bool}.\operatorname{false}, \operatorname{Bool}.\operatorname{false})), c\right)))) \operatorname{then} w\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{finish}\left((\operatorname{Bool}.\operatorname{false}, (\operatorname{Bool}.\operatorname{false}, \operatorname{Bool}.\operatorname{false})), c\right), P\left(c\right)\right) \operatorname{else} (0: \operatorname{Int}))))))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.widthTotal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233196: eight-colour complementary-pair exclusion on a two-column strip*. URL: <https://oeis.org/A233196>.

*Commentary.*

Positive width supplies column zero. The first row starts with all flags false.

**Theorem 1.46 (Literal arrays equal transfer counts).**

$$\forall (k: \operatorname{Nat}), ([\operatorname{NeZero}\left(k\right)] (\forall (B: \operatorname{Type}), (\forall (R: (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right)) \to (\operatorname{Prop})), (\forall (P: (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right)) \to (B)), (\forall (C: (B) \to ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right)) \to (\operatorname{Prop}))), ([\operatorname{DecidablePred}\left(R\right)] ([\operatorname{DecidableRel}\left(C\right)] (\forall (E: (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right)) \to ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right)) \to (\operatorname{Prop}))), ([\operatorname{DecidableRel}\left(E\right)] (\forall (edge: \forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right)), (\forall (d: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{WidthRow}\left(k\right)), ((E\left(c, d\right)) \iff (C\left(P\left(c\right), d\right))))), (\forall (n: \operatorname{Nat}), ((\operatorname{Nat}.\operatorname{cast}\left(\operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left(((A: ((\operatorname{Fin}\left((n) + (1)\right)) \times (\operatorname{Fin}\left(k\right))) \to (\operatorname{Fin}\left(8\right))) \mapsto (\exists (i: \operatorname{Fin}\left((n) + (1)\right)), ((\operatorname{Fin}.\operatorname{val}\left(i\right) = 0) \land (A\left((i, (0: \operatorname{Fin}\left(k\right)))\right) = (0: \operatorname{Fin}\left(8\right))))) \land ((\forall (i: \operatorname{Fin}\left((n) + (1)\right)), (R\left(((j: \operatorname{Fin}\left(k\right)) \mapsto A\left((i, j)\right))\right))) \land ((\forall (i: \operatorname{Fin}\left((n) + (1)\right)), (\forall (h: (\operatorname{Fin}.\operatorname{val}\left(i\right)) + (1) < (n) + (1)), (E\left(((j: \operatorname{Fin}\left(k\right)) \mapsto A\left((i, j)\right)), ((j: \operatorname{Fin}\left(k\right)) \mapsto A\left(((\operatorname{Fin}.\operatorname{mk}\left((\operatorname{Fin}.\operatorname{val}\left(i\right)) + (1), h\right): \operatorname{Fin}\left((n) + (1)\right)), j)\right))\right)))) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{widthNormal}\left((\operatorname{Bool}.\operatorname{false}, (\operatorname{Bool}.\operatorname{false}, \operatorname{Bool}.\operatorname{false})), ((i: \operatorname{Fin}\left((n) + (1)\right)) \mapsto ((j: \operatorname{Fin}\left(k\right)) \mapsto A\left((i, j)\right)))\right))))), (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left(((\operatorname{Fin}\left((n) + (1)\right)) \times (\operatorname{Fin}\left(k\right))) \to (\operatorname{Fin}\left(8\right))\right))\right)\right)\right): \operatorname{Int}) = \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{widthTotal}\left(R, P, \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233196Strip}.\operatorname{widthV}\left(R, P, C, n\right)\right)))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.width_counting_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233196: eight-colour complementary-pair exclusion on a two-column strip*. URL: <https://oeis.org/A233196>.

*Commentary.*

For every natural n and positive width k, the displayed literal filter on n+1 rows equals first-row aggregation of widthV n. Its cardinality is explicitly cast from Nat to Int.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.Legal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.Row`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.Seen`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.T`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.TailGood`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.Valid`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.WidthRow`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.a`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.advance`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.allowed`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.beta`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.bonds`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.classCount`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.colour_bond_iff`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.compatible`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.count`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.count_eq_v`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.finish`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.finish_fst`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.finish_snd`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.finish_third`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.finite_certificate`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.firstCount`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.good`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.good_iff`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.instDecidableAllowed`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.instDecidablePrior`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.instDecidableTailGood`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.normal_cons`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.pairs`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.prior`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.prior_succ`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.prior_zero`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.result`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.rowLegal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.seenClass`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.tail_iff`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.widthInstDecidableGood`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.widthInstDecidableLegal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.widthInstDecidableNormal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.widthLegal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.widthNormal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.widthStep`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.widthTotal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.widthV`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.width_counting_bridge`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix](TransferMatrix.md)
