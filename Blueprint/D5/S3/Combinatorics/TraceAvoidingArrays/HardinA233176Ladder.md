# Three-row complementary-pair exclusion

## Abstract

Barker's integer generating function for normalized three-row six-colour ladders.

An array is a function from Fin 3 times Fin n to Fin 6. The first cell has colour zero. Bonds join cells in consecutive columns whose row indices differ by at most one. Each bond excludes equal colours and colours summing to five. The equivalence with distinct pair labels is HardinA233251TriangleStrip.colour_bond_iff, and its Row type represents each three-cell column. Row-major order scans every cell of row zero before row one, and every cell of row one before row two. The strict rank is Fin.val(row)*n+Fin.val(column). Fin.val is the explicit natural coercion throughout. Nat.div denotes natural quotient division and Nat.mod denotes its nonnegative remainder.

**Definition 1.1 (Scanner level encoding).**

$$\forall (s: \operatorname{Fin}\left(3\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233176Ladder}.\operatorname{seen}\left(s\right) = (\operatorname{decide}\left((0 < \operatorname{Fin}.\operatorname{val}\left(s\right))\right), \operatorname{decide}\left((1 < \operatorname{Fin}.\operatorname{val}\left(s\right))\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233176Ladder.seen` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233176: six-colour complementary-pair exclusion on a three-row ladder*. URL: <https://oeis.org/A233176>.

*Commentary.*

A level records whether colours one and two have already occurred.

**Definition 1.2 (Scanner level update).**

$$\forall (s: \operatorname{Fin}\left(3\right)), (\forall (x: \operatorname{Fin}\left(6\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233176Ladder}.\operatorname{next}\left(s, x\right) = \operatorname{max}\left(s, (\operatorname{if} (x = (1: \operatorname{Fin}\left(6\right))) \operatorname{then} ((1: \operatorname{Fin}\left(3\right))) \operatorname{else} ((\operatorname{if} (x = (2: \operatorname{Fin}\left(6\right))) \operatorname{then} ((2: \operatorname{Fin}\left(3\right))) \operatorname{else} ((0: \operatorname{Fin}\left(3\right))))))\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233176Ladder.next` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233176: six-colour complementary-pair exclusion on a three-row ladder*. URL: <https://oeis.org/A233176>.

*Commentary.*

The maximum retains the current level and incorporates the next colour.

**Theorem 1.3 (Encoding commutes with advance).**

$$\forall (s: \operatorname{Fin}\left(3\right)), (\forall (x: \operatorname{Fin}\left(6\right)), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{allowed}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233176Ladder}.\operatorname{seen}\left(s\right), x\right)) \Rightarrow (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{advance}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233176Ladder}.\operatorname{seen}\left(s\right), x\right) = \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233176Ladder}.\operatorname{seen}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233176Ladder}.\operatorname{next}\left(s, x\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233176Ladder.advance_seen` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233176: six-colour complementary-pair exclusion on a three-row ladder*. URL: <https://oeis.org/A233176>.

*Commentary.*

For every allowed colour, the Boolean scanner update agrees with the level update.

**Theorem 1.4 (A scanner step preserves the level order).**

$$\forall (s: \operatorname{Fin}\left(3\right)), (\forall (x: \operatorname{Fin}\left(6\right)), (s \le \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233176Ladder}.\operatorname{next}\left(s, x\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233176Ladder.next_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233176: six-colour complementary-pair exclusion on a three-row ladder*. URL: <https://oeis.org/A233176>.

*Commentary.*

Scanning one colour never decreases the level.

**Theorem 1.5 (An allowed label is below the new level).**

$$\forall (s: \operatorname{Fin}\left(3\right)), (\forall (x: \operatorname{Fin}\left(6\right)), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{allowed}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233176Ladder}.\operatorname{seen}\left(s\right), x\right)) \Rightarrow (\operatorname{D5}.\operatorname{S3}.\operatorname{Observer}.\operatorname{Separation}.\operatorname{BooleanRankThreeK4}.\operatorname{beta}\left(x\right) \le \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233176Ladder}.\operatorname{next}\left(s, x\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233176Ladder.label_next` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233176: six-colour complementary-pair exclusion on a three-row ladder*. URL: <https://oeis.org/A233176>.

*Commentary.*

The pair label is bounded by the updated scanner level.

**Definition 1.6 (Scanner over an arbitrary finite word).**

$$(\forall (s: \operatorname{Fin}\left(3\right)), (\forall (f: \operatorname{Fin}\left(0\right) \to \operatorname{Fin}\left(6\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233176Ladder}.\operatorname{endLevel}\left(s, f\right) = s))) \land (\forall (n: \operatorname{Nat}), (\forall (s: \operatorname{Fin}\left(3\right)), (\forall (f: \operatorname{Fin}\left((n) + (1)\right) \to \operatorname{Fin}\left(6\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233176Ladder}.\operatorname{endLevel}\left(s, f\right) = \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233176Ladder}.\operatorname{endLevel}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233176Ladder}.\operatorname{next}\left(s, f\left((0: \operatorname{Fin}\left((n) + (1)\right))\right)\right), \operatorname{Fin}.\operatorname{tail}\left(f\right)\right)))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233176Ladder.endLevel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233176: six-colour complementary-pair exclusion on a three-row ladder*. URL: <https://oeis.org/A233176>.

*Commentary.*

The two defining equations scan the empty word and a word with a first cell. The word length is arbitrary and independent of the number of array rows.

**Theorem 1.7 (A complete scan preserves the level order).**

$$\forall (n: \operatorname{Nat}), (\forall (s: \operatorname{Fin}\left(3\right)), (\forall (f: \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(6\right)), (s \le \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233176Ladder}.\operatorname{endLevel}\left(s, f\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233176Ladder.endLevel_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233176: six-colour complementary-pair exclusion on a three-row ladder*. URL: <https://oeis.org/A233176>.

*Commentary.*

The final level is at least the initial level.

**Theorem 1.8 (Encoding commutes with a complete scan).**

$$\forall (n: \operatorname{Nat}), (\forall (s: \operatorname{Fin}\left(3\right)), (\forall (f: \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(6\right)), (\forall (h: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{good}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233176Ladder}.\operatorname{seen}\left(s\right), f\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{finish}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233176Ladder}.\operatorname{seen}\left(s\right), f\right) = \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233176Ladder}.\operatorname{seen}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233176Ladder}.\operatorname{endLevel}\left(s, f\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233176Ladder.finish_seen` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233176: six-colour complementary-pair exclusion on a three-row ladder*. URL: <https://oeis.org/A233176>.

*Commentary.*

A good word gives the same final record in the Boolean and level encodings.

**Definition 1.9 (Column pair labels).**

$$\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233176Ladder}.\operatorname{Labels}\left(\right) = \left(\operatorname{Fin}\left(3\right) \to \operatorname{Fin}\left(3\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233176Ladder.Labels` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233176: six-colour complementary-pair exclusion on a three-row ladder*. URL: <https://oeis.org/A233176>.

*Commentary.*

A column of three cells carries one pair label per row.

**Definition 1.10 (Pair labels of a column).**

$$\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233251TriangleStrip}.\operatorname{Row}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233176Ladder}.\operatorname{pairs}\left(c\right) = (\lambda (i: \operatorname{Fin}\left(3\right)) \mapsto \operatorname{D5}.\operatorname{S3}.\operatorname{Observer}.\operatorname{Separation}.\operatorname{BooleanRankThreeK4}.\operatorname{beta}\left(c\left(i\right)\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233176Ladder.pairs` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233176: six-colour complementary-pair exclusion on a three-row ladder*. URL: <https://oeis.org/A233176>.

*Commentary.*

Each cell is sent to its complementary pair by BooleanRankThreeK4.beta.

**Definition 1.11 (Ternary digit extraction).**

$$\forall (k: \operatorname{Nat}), (\forall (d: \operatorname{Nat}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233176Ladder}.\operatorname{digit}\left(k, d\right) = (\operatorname{Fin}.\operatorname{mk}\left(\operatorname{Nat}.\operatorname{mod}\left(\operatorname{Nat}.\operatorname{div}\left(k, d\right), 3\right), \operatorname{Nat}.\operatorname{mod_{lt}}\left(\operatorname{Nat}.\operatorname{div}\left(k, d\right), (\operatorname{by} \operatorname{omega}: 0 < 3)\right)\right): \operatorname{Fin}\left(3\right))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233176Ladder.digit` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233176: six-colour complementary-pair exclusion on a three-row ladder*. URL: <https://oeis.org/A233176>.

*Commentary.*

Natural quotient and remainder produce a value in Fin 3, including when the divisor is zero.

**Theorem 1.12 (Repeated keys as integer weights).**

$$\forall (es: \operatorname{List}\left(\operatorname{Nat}\right)), (\forall (g: \operatorname{Nat} \to \operatorname{Int}), (\operatorname{List}.\operatorname{sum}\left(\operatorname{List}.\operatorname{map}\left(g, \operatorname{List}.\operatorname{flatMap}\left((\lambda (e: \operatorname{Nat}) \mapsto \operatorname{List}.\operatorname{replicate}\left(\operatorname{Nat}.\operatorname{mod}\left(e, 9\right), \operatorname{Nat}.\operatorname{div}\left(e, 9\right)\right)), es\right)\right)\right) = \operatorname{List}.\operatorname{sum}\left(\operatorname{List}.\operatorname{map}\left((\lambda (e: \operatorname{Nat}) \mapsto ((\operatorname{Nat}.\operatorname{cast}\left(\operatorname{Nat}.\operatorname{mod}\left(e, 9\right)\right): \operatorname{Int})) \cdot (g\left(\operatorname{Nat}.\operatorname{div}\left(e, 9\right)\right))), es\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233176Ladder.weighted_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233176: six-colour complementary-pair exclusion on a three-row ladder*. URL: <https://oeis.org/A233176>.

*Commentary.*

Each key e/9 is repeated e%9 times. The multiplicity is explicitly cast from natural numbers to integers before multiplication.

**Definition 1.13 (Row-major normalization).**

$$\forall (n: \operatorname{Nat}), (\forall (A: (\operatorname{Fin}\left(3\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(6\right)), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233176Ladder}.\operatorname{normal}\left(A\right)) \Leftrightarrow (\forall (p: (\operatorname{Fin}\left(3\right)) \times (\operatorname{Fin}\left(n\right))), ((((A\left(p\right) = (2: \operatorname{Fin}\left(6\right))) \lor ((A\left(p\right) = (3: \operatorname{Fin}\left(6\right))) \lor (A\left(p\right) = (4: \operatorname{Fin}\left(6\right))))) \Rightarrow (\exists (q: (\operatorname{Fin}\left(3\right)) \times (\operatorname{Fin}\left(n\right))), ((((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(q\right)\right)) \cdot (n)) + (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(q\right)\right)) < ((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(p\right)\right)) \cdot (n)) + (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(p\right)\right))) \land (A\left(q\right) = (1: \operatorname{Fin}\left(6\right)))))) \land ((A\left(p\right) = (3: \operatorname{Fin}\left(6\right))) \Rightarrow (\exists (q: (\operatorname{Fin}\left(3\right)) \times (\operatorname{Fin}\left(n\right))), ((((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(q\right)\right)) \cdot (n)) + (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(q\right)\right)) < ((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(p\right)\right)) \cdot (n)) + (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(p\right)\right))) \land (A\left(q\right) = (2: \operatorname{Fin}\left(6\right))))))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233176Ladder.normal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233176: six-colour complementary-pair exclusion on a three-row ladder*. URL: <https://oeis.org/A233176>.

*Commentary.*

Every 2, 3 or 4 has a strictly earlier 1; every 3 has a strictly earlier 2. The existential cell has the same typed finite domain as the current cell. Equal-rank cells cannot serve as predecessors.

**Definition 1.14 (Deciding the normalization).**

$$\forall (n: \operatorname{Nat}), (\forall (A: (\operatorname{Fin}\left(3\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(6\right)), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233176Ladder}.\operatorname{instDecidableNormal}\left(A\right): \operatorname{Decidable}\left((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233176Ladder}.\operatorname{normal}\left(A\right))\right)) = \operatorname{inferInstanceAs}\left((\operatorname{Decidable}\left((\forall (p: (\operatorname{Fin}\left(3\right)) \times (\operatorname{Fin}\left(n\right))), ((((A\left(p\right) = (2: \operatorname{Fin}\left(6\right))) \lor ((A\left(p\right) = (3: \operatorname{Fin}\left(6\right))) \lor (A\left(p\right) = (4: \operatorname{Fin}\left(6\right))))) \Rightarrow (\exists (q: (\operatorname{Fin}\left(3\right)) \times (\operatorname{Fin}\left(n\right))), ((((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(q\right)\right)) \cdot (n)) + (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(q\right)\right)) < ((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(p\right)\right)) \cdot (n)) + (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(p\right)\right))) \land (A\left(q\right) = (1: \operatorname{Fin}\left(6\right)))))) \land ((A\left(p\right) = (3: \operatorname{Fin}\left(6\right))) \Rightarrow (\exists (q: (\operatorname{Fin}\left(3\right)) \times (\operatorname{Fin}\left(n\right))), ((((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(q\right)\right)) \cdot (n)) + (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(q\right)\right)) < ((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(p\right)\right)) \cdot (n)) + (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(p\right)\right))) \land (A\left(q\right) = (2: \operatorname{Fin}\left(6\right))))))))\right))\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233176Ladder.instDecidableNormal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233176: six-colour complementary-pair exclusion on a three-row ladder*. URL: <https://oeis.org/A233176>.

*Commentary.*

The defining expression is inferInstanceAs for the displayed universally quantified conjunction of the two implications.

**Definition 1.15 (Literal array conditions).**

$$\forall (n: \operatorname{Nat}), (\forall (A: (\operatorname{Fin}\left(3\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(6\right)), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233176Ladder}.\operatorname{Legal}\left(A\right)) \Leftrightarrow ((\exists (j: \operatorname{Fin}\left(n\right)), ((\operatorname{Fin}.\operatorname{val}\left(j\right) = 0) \land (A\left(((0: \operatorname{Fin}\left(3\right)), j)\right) = (0: \operatorname{Fin}\left(6\right))))) \land ((\forall (j: \operatorname{Fin}\left(n\right)), (\forall (h: (\operatorname{Fin}.\operatorname{val}\left(j\right)) + (1) < n), (\forall (r: \operatorname{Fin}\left(3\right)), (\forall (s: \operatorname{Fin}\left(3\right)), (((\operatorname{Fin}.\operatorname{val}\left(r\right) \le (\operatorname{Fin}.\operatorname{val}\left(s\right)) + (1)) \land (\operatorname{Fin}.\operatorname{val}\left(s\right) \le (\operatorname{Fin}.\operatorname{val}\left(r\right)) + (1))) \Rightarrow ((A\left((r, j)\right) \ne A\left((s, (\operatorname{Fin}.\operatorname{mk}\left((\operatorname{Fin}.\operatorname{val}\left(j\right)) + (1), h\right): \operatorname{Fin}\left(n\right)))\right)) \land ((\operatorname{Fin}.\operatorname{val}\left(A\left((r, j)\right)\right)) + (\operatorname{Fin}.\operatorname{val}\left(A\left((s, (\operatorname{Fin}.\operatorname{mk}\left((\operatorname{Fin}.\operatorname{val}\left(j\right)) + (1), h\right): \operatorname{Fin}\left(n\right)))\right)\right)) \ne 5))))))) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233176Ladder}.\operatorname{normal}\left(A\right))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233176Ladder.Legal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233176: six-colour complementary-pair exclusion on a three-row ladder*. URL: <https://oeis.org/A233176>.

*Commentary.*

The first-cell existential is false at width zero. The two natural inequalities on row values express absolute row difference at most one. The next column is Fin.mk (j.val+1) h, retaining its bound proof.

**Definition 1.16 (The literal filtered count).**

$$\forall (n: \operatorname{Nat}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233176Ladder}.\operatorname{a}\left(n\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((\lambda (A: (\operatorname{Fin}\left(3\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(6\right)) \mapsto \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233176Ladder}.\operatorname{Legal}\left(A\right)), \operatorname{Finset}.\operatorname{univ}\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233176Ladder.a` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233176: six-colour complementary-pair exclusion on a three-row ladder*. URL: <https://oeis.org/A233176>.

*Commentary.*

Finset.univ ranges over all arrays, and the filter applies Legal literally. Thus a(0)=0. The positive-width coefficients begin 11,80,2688,78336.

**Theorem 1.17 (Initial coefficients).**

$$((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233176Ladder}.\operatorname{a}\left(0\right): \operatorname{Int}) = 0) \land (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233176Ladder}.\operatorname{a}\left(1\right): \operatorname{Int}) = 11) \land (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233176Ladder}.\operatorname{a}\left(2\right): \operatorname{Int}) = 80) \land (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233176Ladder}.\operatorname{a}\left(3\right): \operatorname{Int}) = 2688) \land (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233176Ladder}.\operatorname{a}\left(4\right): \operatorname{Int}) = 78336) \land (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233176Ladder}.\operatorname{a}\left(5\right): \operatorname{Int}) = 2469888) \land (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233176Ladder}.\operatorname{a}\left(6\right): \operatorname{Int}) = 76447744) \land (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233176Ladder}.\operatorname{a}\left(7\right): \operatorname{Int}) = 2385772544) \land (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233176Ladder}.\operatorname{a}\left(8\right): \operatorname{Int}) = 74291609600) \land (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233176Ladder}.\operatorname{a}\left(9\right): \operatorname{Int}) = 2315406802944) \land (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233176Ladder}.\operatorname{a}\left(10\right): \operatorname{Int}) = 72144847372288) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233176Ladder}.\operatorname{a}\left(11\right): \operatorname{Int}) = 2248141575290880)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233176Ladder.finite_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233176: six-colour complementary-pair exclusion on a three-row ladder*. URL: <https://oeis.org/A233176>.

*Commentary.*

The existing scanner consists of D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.Seen, allowed, advance, good and finish. Its records correspond to levels 0,1,2 according to which of colours one and two has been seen. The final top record starts the middle row, and the final middle record starts the bottom row. Five ordered records and the preceding three pair labels give 168 states in 21 classes. Finite continuation vectors determine the displayed coefficients.

**Theorem 1.18 (Barker's generating function).**

$$((((1) - ((8) \cdot (\operatorname{PowerSeries}.\operatorname{X}))) \cdot ((((1) - ((24) \cdot (\operatorname{PowerSeries}.\operatorname{X}))) - ((256) \cdot (\operatorname{PowerSeries}.\operatorname{X}^{2}))) + ((1024) \cdot (\operatorname{PowerSeries}.\operatorname{X}^{3})))) \cdot (\operatorname{PowerSeries}.\operatorname{mk}\left((\lambda (n: \operatorname{Nat}) \mapsto (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233176Ladder}.\operatorname{a}\left(n\right): \operatorname{Int}))\right)): \operatorname{PowerSeries}\left(\operatorname{Int}\right)) = (\operatorname{PowerSeries}.\operatorname{X}) \cdot (((((11) - ((272) \cdot (\operatorname{PowerSeries}.\operatorname{X}))) - ((576) \cdot (\operatorname{PowerSeries}.\operatorname{X}^{2}))) + ((20992) \cdot (\operatorname{PowerSeries}.\operatorname{X}^{3}))) - ((53248) \cdot (\operatorname{PowerSeries}.\operatorname{X}^{4})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233176Ladder.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin233176` (proved) by `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233176Ladder.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin233176","declaration_gid":"D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233176Ladder.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233176: six-colour complementary-pair exclusion on a three-row ladder*. URL: <https://oeis.org/A233176>.

*Commentary.*

The column transfer has 159 different nonzero state transitions. Its continuation vectors satisfy an order-eleven relation. Dividing the corresponding annihilating polynomial by z^4-32*z^3-64*z^2+3072*z-8192 gives z^7-16*z^6-256*z^5+3072*z^4+20480*z^3-98304*z^2-524288*z. The initial coefficients force the order-four residual to vanish from index six onward. Coefficient comparison gives the displayed identity. The natural array counts are cast to integers before PowerSeries.mk is applied.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233176Ladder.Labels`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233176Ladder.Legal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233176Ladder.a`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233176Ladder.advance_seen`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233176Ladder.digit`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233176Ladder.endLevel`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233176Ladder.endLevel_mono`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233176Ladder.finish_seen`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233176Ladder.finite_certificate`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233176Ladder.instDecidableNormal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233176Ladder.label_next`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233176Ladder.next`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233176Ladder.next_mono`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233176Ladder.normal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233176Ladder.pairs`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233176Ladder.result`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233176Ladder.seen`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233176Ladder.weighted_sum`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip](HardinA233175PairStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip](HardinA233251TriangleStrip.md)
- Dependency: [D5/S3/Observer/Separation/BooleanRankThreeK4](../../Observer/Separation/BooleanRankThreeK4.md)
