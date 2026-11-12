# Literal normalization, zone counting and the formal generating series

## Abstract

Literal six-column king strips, complementary-pair fibres and their exact count.

OEIS A233166, revision 8, NAME: Number of n X 6 0..7 arrays with no element x(i,j) adjacent to itself or value 7-x(i,j) horizontally, diagonally, antidiagonally or vertically, top left element zero, and 1 appearing before 2 3 4 5 and 6, 2 appearing before 3 4 and 5, and 3 appearing before 4 in row major order (unlabelled 8-colorings with no clashing color pairs).

**Definition 1.1 (Literal functions with free boundaries).**

$$\forall n: Nat, (\forall f: ((\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(6\right))) \to \operatorname{Fin}\left(8\right), ((\operatorname{Legal}\left(f\right)) \Leftrightarrow ((\exists i: \operatorname{Fin}\left(n\right), ((\operatorname{Fin}.\operatorname{val}\left(i\right) = 0) \land (f\left((i, 0)\right) = 0))) \land ((\forall p: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(6\right)), (\forall q: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(6\right)), (((p \neq q) \land ((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(p\right)\right) \leq \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(q\right)\right) + 1) \land ((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(q\right)\right) \leq \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(p\right)\right) + 1) \land ((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(p\right)\right) \leq \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(q\right)\right) + 1) \land (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(q\right)\right) \leq \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(p\right)\right) + 1))))) \implies ((f\left(p\right) \neq f\left(q\right)) \land (\operatorname{Fin}.\operatorname{val}\left(f\left(p\right)\right) + \operatorname{Fin}.\operatorname{val}\left(f\left(q\right)\right) \neq 7))))) \land (\forall p: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(6\right)), ((((f\left(p\right) = 2) \lor ((f\left(p\right) = 3) \lor ((f\left(p\right) = 4) \lor ((f\left(p\right) = 5) \lor (f\left(p\right) = 6))))) \implies (\exists q: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(6\right)), ((6 \cdot \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(q\right)\right) + \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(q\right)\right) < 6 \cdot \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(p\right)\right) + \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(p\right)\right)) \land (f\left(q\right) = 1)))) \land ((((f\left(p\right) = 3) \lor ((f\left(p\right) = 4) \lor (f\left(p\right) = 5))) \implies (\exists q: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(6\right)), ((6 \cdot \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(q\right)\right) + \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(q\right)\right) < 6 \cdot \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(p\right)\right) + \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(p\right)\right)) \land (f\left(q\right) = 2)))) \land ((f\left(p\right) = 4) \implies (\exists q: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(6\right)), ((6 \cdot \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(q\right)\right) + \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(q\right)\right) < 6 \cdot \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(p\right)\right) + \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(p\right)\right)) \land (f\left(q\right) = 3)))))))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233166KingStrip.Legal` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233166: normalized eight-colour six-column king strips*. URL: <https://oeis.org/A233166>.

*Commentary.*

Both coordinate inequalities in both directions mean absolute difference at most one. The distinctness condition excludes the same cell. The rank is six times the row plus the column, and every earlier-cell inequality is strict. All functions are counted themselves. Colours may be absent; seven has no further precedence condition. The first-cell existential is false at height zero. Fin.val supplies coordinate values.

**Definition 1.2 (The literal cardinality).**

$$\forall n: Nat, (\operatorname{a}\left(n\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left(\lambda f: ((\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(6\right))) \to \operatorname{Fin}\left(8\right) \mapsto \operatorname{Legal}\left(f\right), \operatorname{Finset}.\operatorname{univ}\left(\right)\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233166KingStrip.a` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233166: normalized eight-colour six-column king strips*. URL: <https://oeis.org/A233166>.

*Commentary.*

Finset.univ ranges over every function on Fin n times Fin 6 into Fin 8. There is no group quotient, orbit divisor, transposition or boundary identification. The zero constant coefficient extends the positive-height source sequence only for its formal generating series.

**Definition 1.3 (The complete source conjunction).**

$$(\operatorname{claim}\left(\right)) \Leftrightarrow ((\operatorname{a}\left(1\right) = 236) \land ((\operatorname{PowerSeries}.\operatorname{mk}\left(\lambda n: Nat \mapsto (\operatorname{a}\left(n\right): Rat)\right) = 4 \cdot X \cdot \left(59 - 10304 \cdot X + 356352 \cdot (X)^{2}\right) \cdot (\left(1 - 64 \cdot X\right) \cdot \left(1 - 128 \cdot X\right))^{-1} \operatorname{in} \operatorname{PowerSeries}\left(Rat\right)) \land ((\forall n: Nat, ((2 \leq n) \implies (\operatorname{a}\left(n\right) = (64)^{n - 1} \cdot \left((2)^{n} + 60\right)))) \land (\forall n: Nat, ((4 \leq n) \implies ((\operatorname{a}\left(n\right): Int) = 192 \cdot (\operatorname{a}\left(n - 1\right): Int) - 8192 \cdot (\operatorname{a}\left(n - 2\right): Int)))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233166KingStrip.claim` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233166: normalized eight-colour six-column king strips*. URL: <https://oeis.org/A233166>.

*Commentary.*

FORMULA: Empirical: a(n) = 192*a(n-1) - 8192*a(n-2) for n>3. Conjectures from _Colin Barker_, Oct 09 2018: (Start) G.f.: 4*x*(59 - 10304*x + 356352*x^2) / ((1 - 64*x)*(1 - 128*x)). a(n) = 64^(n-1) * (2^n+60) for n>1. (End). The first DATA entry is 236. This proposition includes that exceptional value and every universal onset. PowerSeries.mk uses rational casts of the actual counts. X denotes PowerSeries.X over the rationals. The displayed denominator has constant coefficient one, so its formal inverse exists uniquely. The result below proves exactly this conjunction about the literal count.

**Definition 1.4 (Labelled proper pair-colourings).**

$$\forall n: Nat, (\forall c: ((\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(6\right))) \to \operatorname{Fin}\left(4\right), ((\operatorname{Proper}\left(c\right)) \Leftrightarrow (\forall p: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(6\right)), (\forall q: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(6\right)), (((p \neq q) \land ((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(p\right)\right) \leq \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(q\right)\right) + 1) \land ((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(q\right)\right) \leq \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(p\right)\right) + 1) \land ((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(p\right)\right) \leq \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(q\right)\right) + 1) \land (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(q\right)\right) \leq \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(p\right)\right) + 1))))) \implies (c\left(p\right) \neq c\left(q\right)))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233166KingStrip.Proper` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233166: normalized eight-colour six-column king strips*. URL: <https://oeis.org/A233166>.

*Commentary.*

The four labels name the complementary pairs. Proper means different labels at every distinct neighbouring cell pair, with both coordinate differences at most one. No normalization or surjectivity is included in this auxiliary class.

**Definition 1.5 (First-column values and first-row offsets).**

$$\forall n: Nat, (\forall z: ((\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(4\right)) \times ((\operatorname{Fin}\left(6\right)) \to \operatorname{Fin}\left(4\right)), ((z \in \operatorname{zones}\left(n\right)) \Leftrightarrow ((\operatorname{Prod}.\operatorname{snd}\left(z\right)\left(0\right) = 0) \land ((\forall j: \operatorname{Fin}\left(5\right), (\operatorname{xor}\left(\operatorname{Prod}.\operatorname{snd}\left(z\right)\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right), \operatorname{Prod}.\operatorname{snd}\left(z\right)\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right)\right) \neq 0)) \land (\forall i: Nat, ((i + 1 < n) \implies ((\operatorname{xor}\left(\operatorname{Prod}.\operatorname{fst}\left(z\right)\left(i\right), \operatorname{Prod}.\operatorname{fst}\left(z\right)\left(i + 1\right)\right) \neq 0) \land (\forall j: \operatorname{Fin}\left(5\right), (\operatorname{xor}\left(\operatorname{Prod}.\operatorname{snd}\left(z\right)\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right), \operatorname{Prod}.\operatorname{snd}\left(z\right)\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right)\right) \neq \operatorname{xor}\left(\operatorname{Prod}.\operatorname{fst}\left(z\right)\left(i\right), \operatorname{Prod}.\operatorname{fst}\left(z\right)\left(i + 1\right)\right))))))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233166KingStrip.zones` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233166: normalized eight-colour six-column king strips*. URL: <https://oeis.org/A233166>.

*Commentary.*

A zone datum z is the pair (u,v) of first-column values and first-row offsets. The offset v(0) is zero. Adjacent increments of each word are nonzero, and each horizontal increment differs from every vertical increment. Bounded natural indices denote their corresponding Fin indices; their proof arguments do not affect values.

**Definition 1.6 (A bijection for every positive height).**

$$\forall n: Nat, (\forall h: 0 < n, ((\forall c: ((\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(6\right))) \to \operatorname{Fin}\left(4\right), ((\operatorname{Proper}\left(c\right)) \implies (\operatorname{zoneEquiv}\left(h\right)\left(\operatorname{Subtype}.\operatorname{mk}\left(c\right)\right) = (\lambda i: \operatorname{Fin}\left(n\right) \mapsto c\left((i, 0)\right), \lambda j: \operatorname{Fin}\left(6\right) \mapsto \operatorname{xor}\left(c\left((0, 0)\right), c\left((0, j)\right)\right))))) \land (\forall z: ((\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(4\right)) \times ((\operatorname{Fin}\left(6\right)) \to \operatorname{Fin}\left(4\right)), ((z \in \operatorname{zones}\left(n\right)) \implies (\operatorname{Equiv}.\operatorname{symm}\left(\operatorname{zoneEquiv}\left(h\right)\right)\left(\operatorname{Subtype}.\operatorname{mk}\left(z\right)\right) = \lambda p: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(6\right)) \mapsto \operatorname{xor}\left(\operatorname{Prod}.\operatorname{fst}\left(z\right)\left(\operatorname{Prod}.\operatorname{fst}\left(p\right)\right), \operatorname{Prod}.\operatorname{snd}\left(z\right)\left(\operatorname{Prod}.\operatorname{snd}\left(p\right)\right)\right))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233166KingStrip.zoneEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233166: normalized eight-colour six-column king strips*. URL: <https://oeis.org/A233166>.

*Commentary.*

The forward map records u(i)=c(i,0) and v(j)=c(0,0) xor c(0,j). The inverse sends (u,v) to c(i,j)=u(i) xor v(j). The displayed equations describe the underlying functions of the subtype maps; proofs of membership are omitted. The rectangle identity proves the first composite is the identity. The zero offset proves the second. For the converse adjacency proof, equal rows or equal columns use the nonzero increments, and both diagonal directions use the disjointness of horizontal and vertical increments. This bijection includes height one; the later all-four-colours and literal-prefix saturation conclusions require height at least two.

**Theorem 1.7 (Necessary zone data for every literal strip).**

$$\forall n: Nat, ((2 \leq n) \implies (\forall f: ((\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(6\right))) \to \operatorname{Fin}\left(8\right), ((\operatorname{Legal}\left(f\right)) \implies ((\forall i: \operatorname{Fin}\left(n\right), (\forall j: \operatorname{Fin}\left(6\right), (\operatorname{beta}\left(f\left((i, j)\right)\right) = \operatorname{xor}\left(\operatorname{xor}\left(\operatorname{beta}\left(f\left((i, 0)\right)\right), \operatorname{beta}\left(f\left((0, 0)\right)\right)\right), \operatorname{beta}\left(f\left((0, j)\right)\right)\right)))) \land ((\forall j: \operatorname{Fin}\left(5\right), (\operatorname{xor}\left(\operatorname{beta}\left(f\left((0, \operatorname{Fin}.\operatorname{castSucc}\left(j\right))\right)\right), \operatorname{beta}\left(f\left((0, \operatorname{Fin}.\operatorname{succ}\left(j\right))\right)\right)\right) \neq 0)) \land ((\forall i: Nat, ((i + 1 < n) \implies ((\operatorname{xor}\left(\operatorname{beta}\left(f\left((i, 0)\right)\right), \operatorname{beta}\left(f\left((i + 1, 0)\right)\right)\right) \neq 0) \land (\forall j: \operatorname{Fin}\left(5\right), (\operatorname{xor}\left(\operatorname{beta}\left(f\left((0, \operatorname{Fin}.\operatorname{castSucc}\left(j\right))\right)\right), \operatorname{beta}\left(f\left((0, \operatorname{Fin}.\operatorname{succ}\left(j\right))\right)\right)\right) \neq \operatorname{xor}\left(\operatorname{beta}\left(f\left((i, 0)\right)\right), \operatorname{beta}\left(f\left((i + 1, 0)\right)\right)\right)))))) \land ((\forall k: \operatorname{Fin}\left(4\right), (\exists p: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(6\right)), ((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(p\right)\right) \leq 1) \land (\operatorname{beta}\left(f\left(p\right)\right) = k)))) \land ((\forall d: \operatorname{Fin}\left(3\right), (\exists p: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(6\right)), ((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(p\right)\right) \leq 1) \land (\operatorname{Fin}.\operatorname{val}\left(f\left(p\right)\right) = \operatorname{Fin}.\operatorname{val}\left(d\right) + 1)))) \land (\operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left(\lambda w: \operatorname{Fin}\left(4\right) \mapsto ((w \neq 0) \land (\forall j: \operatorname{Fin}\left(5\right), (\operatorname{xor}\left(\operatorname{beta}\left(f\left((0, \operatorname{Fin}.\operatorname{castSucc}\left(j\right))\right)\right), \operatorname{beta}\left(f\left((0, \operatorname{Fin}.\operatorname{succ}\left(j\right))\right)\right)\right) \neq w))), \operatorname{Finset}.\operatorname{univ}\left(\right)\right)\right) = \operatorname{ite}\left(\forall j: \operatorname{Fin}\left(5\right), (\operatorname{xor}\left(\operatorname{beta}\left(f\left((0, \operatorname{Fin}.\operatorname{castSucc}\left(j\right))\right)\right), \operatorname{beta}\left(f\left((0, \operatorname{Fin}.\operatorname{succ}\left(j\right))\right)\right)\right) = \operatorname{xor}\left(\operatorname{beta}\left(f\left((0, \operatorname{Fin}.\operatorname{castSucc}\left(0\right))\right)\right), \operatorname{beta}\left(f\left((0, \operatorname{Fin}.\operatorname{succ}\left(0\right))\right)\right)\right)), 2, 1\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233166KingStrip.pair_rectangle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233166: normalized eight-colour six-column king strips*. URL: <https://oeis.org/A233166>.

*Commentary.*

Write c(i,j)=beta(f(i,j)), where beta identifies the complementary pairs {0,7}, {1,6}, {2,5}, {3,4}. The binary operation xor is bitwise exclusive-or on Fin 4. Every adjacent square has four distinct pair colours. The xor of its upper edge equals that of its lower edge, and likewise for its left and right edges. Induction along rows and columns gives the displayed reconstruction. Horizontal and vertical increments are nonzero, and every horizontal increment differs from every vertical increment because the antidiagonal cells are adjacent. The first square also contains all four pair colours. Strict precedence then forces the literal colours one, two and three to have appeared within the first two rows. There are two allowed nonzero vertical increments when all five horizontal increments agree, and one otherwise. This is a count of pair increments, not yet a count of signed colour-row continuations. The zone correspondence is the algebraic rectangular form of Eppstein's published kinggraph construction. This statement concerns the original literal functions and does not replace their count with a labelled count.

**Theorem 1.8 (The complete literal count and formal series).**

$$(\operatorname{a}\left(1\right) = 236) \land ((\operatorname{PowerSeries}.\operatorname{mk}\left(\lambda n: Nat \mapsto (\operatorname{a}\left(n\right): Rat)\right) = 4 \cdot X \cdot \left(59 - 10304 \cdot X + 356352 \cdot (X)^{2}\right) \cdot (\left(1 - 64 \cdot X\right) \cdot \left(1 - 128 \cdot X\right))^{-1} \operatorname{in} \operatorname{PowerSeries}\left(Rat\right)) \land ((\forall n: Nat, ((2 \leq n) \implies (\operatorname{a}\left(n\right) = (64)^{n - 1} \cdot \left((2)^{n} + 60\right)))) \land (\forall n: Nat, ((4 \leq n) \implies ((\operatorname{a}\left(n\right): Int) = 192 \cdot (\operatorname{a}\left(n - 1\right): Int) - 8192 \cdot (\operatorname{a}\left(n - 2\right): Int))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233166KingStrip.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233166: normalized eight-colour six-column king strips*. URL: <https://oeis.org/A233166>.

*Commentary.*

The theorem proves the complete conjunction defined above. At the first occurrence of each complementary pair, the literal colour is its lower representative. All other positions have independent Boolean signs. The explicit fibre equivalence therefore has size two to the number of cells minus the number of used pair labels. A two-by-two square forces all four labels at heights at least two, giving the exact sign factor 2^(6n-4). Canonical representatives use labels in first-occurrence order. The existing general canonical-representative theorem supplies existence and uniqueness; a bijection with the twenty-four permutations of four labels proves the label factor, using the square's surjectivity. No division is assumed for missing labels.

For each first-row offset word, vertical words are walks whose permitted xor increments form its available set. The existing general finite-walk counting theorem gives four times the available-set cardinality to the number of vertical steps. Among proper offset words of length six beginning at zero, exactly three have two choices, ninety have one, and one hundred fifty have none. This finite certificate concerns 4^6 pair words; height remains arbitrary. It gives labelled count 4(3 times 2^(n-1)+90) for every n at least two. Combining the two exact fibres yields the displayed literal formula.

The height-one certificate uses canonical proper pair words and the weight 2^(6-k), where k is the actual number of used labels. It includes absent colours and gives 236. The integer recurrence follows from the two geometric terms 2 times 128^(n-1) and 60 times 64^(n-1). Multiplying the formal series by the denominator proves its coefficient identity, with the exceptional initial coefficients handled separately. The denominator has constant coefficient one, and the formal inverse law gives precisely the claimed rational series.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233166KingStrip.Legal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233166KingStrip.Proper`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233166KingStrip.a`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233166KingStrip.claim`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233166KingStrip.pair_rectangle`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233166KingStrip.result`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233166KingStrip.zoneEquiv`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233166KingStrip.zones`
- Dependency: [D5/S3/Combinatorics/Graph/Pressure/HardinBarkerA209721EdgeDifferences](../Graph/Pressure/HardinBarkerA209721EdgeDifferences.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](HardinA233177Canonical.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip](HardinA233196Strip.md)
