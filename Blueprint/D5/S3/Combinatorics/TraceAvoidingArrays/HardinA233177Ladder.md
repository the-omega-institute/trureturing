# Four-row complementary-pair ladders

## Abstract

Hardin's recurrence for the literal normalized four-row six-colour ladder.

Cells are Fin 4 times Fin n, with colour set Fin 6. Only bonds between consecutive columns are constrained: row indices may differ by at most one. A bond excludes equal colours and colours whose values sum to five. Vertical neighbours inside a column are free. The first cell is zero and the predecessor conditions use the strict row-major rank row.val*n+column.val.

**Definition 1.1 (Row-major predecessor conditions).**

$$\forall (n: \operatorname{Nat}), (\forall (A: (\operatorname{Fin}\left(4\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(6\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177Ladder}.\operatorname{normal}\left(A\right) = (\forall (p: (\operatorname{Fin}\left(4\right)) \times (\operatorname{Fin}\left(n\right))), ((((A\left(p\right) = (2: \operatorname{Fin}\left(6\right))) \lor ((A\left(p\right) = (3: \operatorname{Fin}\left(6\right))) \lor (A\left(p\right) = (4: \operatorname{Fin}\left(6\right))))) \Rightarrow (\exists (q: (\operatorname{Fin}\left(4\right)) \times (\operatorname{Fin}\left(n\right))), ((((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(q\right)\right)) \cdot (n)) + (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(q\right)\right)) < ((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(p\right)\right)) \cdot (n)) + (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(p\right)\right))) \land (A\left(q\right) = (1: \operatorname{Fin}\left(6\right)))))) \land ((A\left(p\right) = (3: \operatorname{Fin}\left(6\right))) \Rightarrow (\exists (q: (\operatorname{Fin}\left(4\right)) \times (\operatorname{Fin}\left(n\right))), ((((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(q\right)\right)) \cdot (n)) + (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(q\right)\right)) < ((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(p\right)\right)) \cdot (n)) + (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(p\right)\right))) \land (A\left(q\right) = (2: \operatorname{Fin}\left(6\right))))))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Ladder.normal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233177: complementary-pair exclusion on a four-row ladder*. URL: <https://oeis.org/A233177>.

*Commentary.*

Row-major predecessor conditions.

**Definition 1.2 (Literal array conditions).**

$$\forall (n: \operatorname{Nat}), (\forall (A: (\operatorname{Fin}\left(4\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(6\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177Ladder}.\operatorname{Legal}\left(A\right) = ((\exists (j: \operatorname{Fin}\left(n\right)), ((\operatorname{Fin}.\operatorname{val}\left(j\right) = 0) \land (A\left(((0: \operatorname{Fin}\left(4\right)), j)\right) = (0: \operatorname{Fin}\left(6\right))))) \land ((\forall (j: \operatorname{Fin}\left(n\right)), (\forall (h: (\operatorname{Fin}.\operatorname{val}\left(j\right)) + (1) < n), (\forall (r: \operatorname{Fin}\left(4\right)), (\forall (s: \operatorname{Fin}\left(4\right)), (((\operatorname{Fin}.\operatorname{val}\left(r\right) \le (\operatorname{Fin}.\operatorname{val}\left(s\right)) + (1)) \land (\operatorname{Fin}.\operatorname{val}\left(s\right) \le (\operatorname{Fin}.\operatorname{val}\left(r\right)) + (1))) \Rightarrow ((A\left((r, j)\right) \ne A\left((s, (\operatorname{Fin}.\operatorname{mk}\left((\operatorname{Fin}.\operatorname{val}\left(j\right)) + (1), h\right): \operatorname{Fin}\left(n\right)))\right)) \land ((\operatorname{Fin}.\operatorname{val}\left(A\left((r, j)\right)\right)) + (\operatorname{Fin}.\operatorname{val}\left(A\left((s, (\operatorname{Fin}.\operatorname{mk}\left((\operatorname{Fin}.\operatorname{val}\left(j\right)) + (1), h\right): \operatorname{Fin}\left(n\right)))\right)\right)) \ne 5))))))) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177Ladder}.\operatorname{normal}\left(A\right))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Ladder.Legal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233177: complementary-pair exclusion on a four-row ladder*. URL: <https://oeis.org/A233177>.

*Commentary.*

Literal array conditions.

**Definition 1.3 (The literal filtered count).**

$$\forall (n: \operatorname{Nat}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177Ladder}.\operatorname{a}\left(n\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((\lambda (A: (\operatorname{Fin}\left(4\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(6\right)) \mapsto \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177Ladder}.\operatorname{Legal}\left(A\right)), \operatorname{Finset}.\operatorname{univ}\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Ladder.a` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233177: complementary-pair exclusion on a four-row ladder*. URL: <https://oeis.org/A233177>.

*Commentary.*

The literal filtered count.

**Theorem 1.4 (The canonical-form counting bridge).**

$$\forall (n: \operatorname{Nat}), ((2 \le n) \Rightarrow ((48) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177Ladder}.\operatorname{a}\left(n\right): \operatorname{Int})) = ((16: \operatorname{Int})^{n}) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177PairTransfer}.\operatorname{L}\left(n\right): \operatorname{Int})) + (6))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Ladder.counting_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233177: complementary-pair exclusion on a four-row ladder*. URL: <https://oeis.org/A233177>.

*Commentary.*

The canonical-form counting bridge.

The beta-label identifies the pairs {0,5}, {1,4}, {2,3}; the side is an independent Boolean choice. Normalization introduces pair labels in first-appearance order and fixes the first side of each used pair to the smaller colour. A canonical pattern using k labels therefore has 2^(4*n-k) lifts. At width at least two a proper pattern uses two or three labels, and every relabelling orbit has six members. If one label is omitted, adjacent entries of a column must agree: a common neighbour in another column excludes both differing labels. Each column is then constant and the two labels alternate. The six such patterns have exactly one canonical member. If C is the number of canonical proper patterns, L=6*C and a=2^(4*n-3)*(C+1). This gives the displayed bridge for every width at least two.

**Theorem 1.5 (The first permitted recurrence instance).**

$$(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177Ladder}.\operatorname{a}\left(9\right): \operatorname{Int}) = (((((((64) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177Ladder}.\operatorname{a}\left(8\right): \operatorname{Int}))) + ((3328) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177Ladder}.\operatorname{a}\left(7\right): \operatorname{Int})))) - ((77824) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177Ladder}.\operatorname{a}\left(6\right): \operatorname{Int})))) - ((1441792) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177Ladder}.\operatorname{a}\left(5\right): \operatorname{Int})))) + ((28311552) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177Ladder}.\operatorname{a}\left(4\right): \operatorname{Int})))) + ((33554432) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177Ladder}.\operatorname{a}\left(3\right): \operatorname{Int})))) - ((1073741824) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177Ladder}.\operatorname{a}\left(2\right): \operatorname{Int})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Ladder.finite_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233177: complementary-pair exclusion on a four-row ladder*. URL: <https://oeis.org/A233177>.

*Commentary.*

The first permitted recurrence instance.

**Theorem 1.6 (Hardin's shifted integer recurrence).**

$$\forall (n: \operatorname{Nat}), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177Ladder}.\operatorname{a}\left((n) + (9)\right): \operatorname{Int}) = (((((((64) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177Ladder}.\operatorname{a}\left((n) + (8)\right): \operatorname{Int}))) + ((3328) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177Ladder}.\operatorname{a}\left((n) + (7)\right): \operatorname{Int})))) - ((77824) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177Ladder}.\operatorname{a}\left((n) + (6)\right): \operatorname{Int})))) - ((1441792) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177Ladder}.\operatorname{a}\left((n) + (5)\right): \operatorname{Int})))) + ((28311552) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177Ladder}.\operatorname{a}\left((n) + (4)\right): \operatorname{Int})))) + ((33554432) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177Ladder}.\operatorname{a}\left((n) + (3)\right): \operatorname{Int})))) - ((1073741824) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233177Ladder}.\operatorname{a}\left((n) + (2)\right): \operatorname{Int}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Ladder.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin233177` (proved) by `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Ladder.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin233177","declaration_gid":"D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Ladder.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233177: complementary-pair exclusion on a four-row ladder*. URL: <https://oeis.org/A233177>.

*Commentary.*

Hardin's shifted integer recurrence.

The pair-pattern transfer has fourteen column classes. Its sextic tail polynomial, multiplied by x-1, gives the recurrence for L+6. Multiplication by 16^n scales the coefficient at lag j by 16^j. The finite base instance covers index nine, while the shifted tail relation covers all larger indices. Writing the index as n+9 makes the condition index>8 explicit. Counts are cast to Int before subtraction. Width one is exceptional for the counting bridge.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Ladder.Legal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Ladder.a`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Ladder.counting_bridge`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Ladder.finite_certificate`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Ladder.normal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Ladder.result`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](HardinA233177Canonical.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer](HardinA233177PairTransfer.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip](HardinA233251TriangleStrip.md)
- Dependency: [D5/S3/Observer/Separation/BooleanRankThreeK4](../../Observer/Separation/BooleanRankThreeK4.md)
