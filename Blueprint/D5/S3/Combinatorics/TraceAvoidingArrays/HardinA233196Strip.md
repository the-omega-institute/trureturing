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

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233196: eight-colour complementary-pair exclusion on a two-column strip*. URL: <https://oeis.org/A233196>.

*Commentary.*

Let w(n) be Matrix.mulVec (T^n) 1. Splitting a literal array into its first row and remaining rows gives a(n+1)=w(n)(0). The finite certificate and TransferMatrix.scalarRelationShift give a(n+4)=20*a(n+3)-64*a(n+2) for every natural n. The first three positive counts are 1,3,36. Comparing coefficients, including a(0)=0, proves the identity in PowerSeries Int. The counts are cast from Nat to Int before forming the series.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.Legal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.Row`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.Seen`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.T`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.Valid`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.WidthRow`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.a`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.advance`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.allowed`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.beta`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.bonds`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.classCount`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.compatible`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.finish`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.finite_certificate`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.firstCount`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.good`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.pairs`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.prior`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.result`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.rowLegal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.seenClass`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.widthNormal`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix](TransferMatrix.md)
