# Literal model and coefficient convention

## Abstract

The literal width-four eight-colour rectangle, complementary pairs and ordinary colourings.

**Definition 1.1 (Contained bonds).**

$$\forall (n: \operatorname{Nat}), (\forall (v: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(4\right))), (\forall (w: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(4\right))), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233198PairFibres}.\operatorname{Edge}\left(v, w\right)) \Leftrightarrow (((\operatorname{Prod}.\operatorname{fst}\left(v\right) = \operatorname{Prod}.\operatorname{fst}\left(w\right)) \land (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(w\right)\right) = (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(v\right)\right)) + (1))) \lor (((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(w\right)\right) = (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(v\right)\right)) + (1)) \land (\operatorname{Prod}.\operatorname{snd}\left(v\right) = \operatorname{Prod}.\operatorname{snd}\left(w\right))) \lor ((\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(w\right)\right) = (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(v\right)\right)) + (1)) \land (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(v\right)\right) = (\operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(w\right)\right)) + (1))))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233198LiteralModel.Edge` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233198: normalized eight-colour arrays of width four*. URL: <https://oeis.org/A233198>.

*Commentary.*

The vertical row increases by one. On the antidiagonal the column decreases by one. Every endpoint already belongs to the finite rectangle; main-diagonal and wraparound constraints are absent.

**Definition 1.2 (Strict earlier-colour prerequisites).**

$$\forall (V: \operatorname{Type}), (\forall (r: V \to \operatorname{Nat}), (\forall (f: V \to \operatorname{Fin}\left(8\right)), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233198PairFibres}.\operatorname{Normal}\left(r, f\right)) \Leftrightarrow (\forall (v: V), ((((2 \le \operatorname{Fin}.\operatorname{val}\left(f\left(v\right)\right)) \land (\operatorname{Fin}.\operatorname{val}\left(f\left(v\right)\right) \le 6)) \Rightarrow (\exists (w: V), ((r\left(w\right) < r\left(v\right)) \land (f\left(w\right) = (1: \operatorname{Fin}\left(8\right)))))) \land ((((f\left(v\right) = 3) \lor ((f\left(v\right) = 4) \lor (f\left(v\right) = 5))) \Rightarrow (\exists (w: V), ((r\left(w\right) < r\left(v\right)) \land (f\left(w\right) = (2: \operatorname{Fin}\left(8\right)))))) \land ((f\left(v\right) = 4) \Rightarrow (\exists (w: V), ((r\left(w\right) < r\left(v\right)) \land (f\left(w\right) = (3: \operatorname{Fin}\left(8\right))))))))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233198LiteralModel.Normal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233198: normalized eight-colour arrays of width four*. URL: <https://oeis.org/A233198>.

*Commentary.*

Each existential predecessor has strictly smaller rank. There is no requirement that a colour occur.

**Definition 1.3 (The literal arrays).**

$$\forall (n: \operatorname{Nat}), (\forall (f: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(4\right)) \to \operatorname{Fin}\left(8\right)), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233198PairFibres}.\operatorname{Legal}\left(f\right)) \Leftrightarrow ((\exists (h: 0 < n), (f\left((\operatorname{Fin}.\operatorname{mk}\left(0, h\right), 0)\right) = 0)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233198PairFibres}.\operatorname{Normal}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233198PairFibres}.\operatorname{rank}\left(\right), f\right)) \land (\forall (v: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(4\right))), (\forall (w: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(4\right))), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233198PairFibres}.\operatorname{Edge}\left(v, w\right)) \Rightarrow ((f\left(v\right) \ne f\left(w\right)) \land ((\operatorname{Fin}.\operatorname{val}\left(f\left(v\right)\right)) + (\operatorname{Fin}.\operatorname{val}\left(f\left(w\right)\right)) \ne 7)))))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233198LiteralModel.Legal` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233198: normalized eight-colour arrays of width four*. URL: <https://oeis.org/A233198>.

*Commentary.*

The top-left existential rejects height zero. The two bond conditions concern inequality and natural sum seven.

**Definition 1.4 (Literal cardinality).**

$$\forall (n: \operatorname{Nat}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233198PairFibres}.\operatorname{a}\left(n\right) = \operatorname{Nat}.\operatorname{card}\left(\operatorname{Subtype}\left((\lambda (f: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(4\right)) \to \operatorname{Fin}\left(8\right)) \mapsto \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233198PairFibres}.\operatorname{Legal}\left(f\right))\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233198LiteralModel.a` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233198: normalized eight-colour arrays of width four*. URL: <https://oeis.org/A233198>.

*Commentary.*

Nat.card counts the subtype of all functions satisfying Legal. The domain has n rows and four columns.

**Definition 1.5 (Positive-height coefficient encoding).**

$$\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233198PairFibres}.\operatorname{A}\left(\right) = \operatorname{PowerSeries}.\operatorname{mk}\left((\lambda (n: \operatorname{Nat}) \mapsto \operatorname{ite}\left(n = 0, 0, (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233198PairFibres}.\operatorname{a}\left(n\right): \operatorname{Rat})\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233198LiteralModel.A` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233198: normalized eight-colour arrays of width four*. URL: <https://oeis.org/A233198>.

*Commentary.*

The power series has rational coefficients. Degree zero is explicitly zero and every positive coefficient is the literal count.

**Definition 1.6 (Complementary pairs).**

$$\forall (x: \operatorname{Fin}\left(8\right)), (\operatorname{Fin}.\operatorname{val}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233198PairFibres}.\operatorname{pair}\left(x\right)\right) = \operatorname{ite}\left(\operatorname{Fin}.\operatorname{val}\left(x\right) < 4, \operatorname{Fin}.\operatorname{val}\left(x\right), \operatorname{Nat}.\operatorname{sub}\left(7, \operatorname{Fin}.\operatorname{val}\left(x\right)\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233198LiteralModel.pair` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233198: normalized eight-colour arrays of width four*. URL: <https://oeis.org/A233198>.

*Commentary.*

The pair label is the smaller member of the complementary pair. Two colours are allowed on a bond exactly when their pair labels differ.

**Definition 1.7 (Order of first use).**

$$\forall (V: \operatorname{Type}), (\forall (r: V \to \operatorname{Nat}), (\forall (p: V \to \operatorname{Fin}\left(4\right)), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233198PairFibres}.\operatorname{PairNormal}\left(r, p\right)) \Leftrightarrow (\forall (v: V), (((2 \le \operatorname{Fin}.\operatorname{val}\left(p\left(v\right)\right)) \Rightarrow (\exists (w: V), ((r\left(w\right) < r\left(v\right)) \land (p\left(w\right) = (1: \operatorname{Fin}\left(4\right)))))) \land ((p\left(v\right) = 3) \Rightarrow (\exists (w: V), ((r\left(w\right) < r\left(v\right)) \land (p\left(w\right) = (2: \operatorname{Fin}\left(4\right)))))))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233198LiteralModel.PairNormal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233198: normalized eight-colour arrays of width four*. URL: <https://oeis.org/A233198>.

*Commentary.*

An occurrence of pair two or three requires an earlier pair one. An occurrence of pair three also requires an earlier pair two. The anchor fixes pair zero at the least cell.

**Definition 1.8 (Proper pair maps).**

$$\forall (n: \operatorname{Nat}), (\forall (p: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(4\right)) \to \operatorname{Fin}\left(4\right)), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233198PairFibres}.\operatorname{PairLegal}\left(p\right)) \Leftrightarrow ((\exists (h: 0 < n), (p\left((\operatorname{Fin}.\operatorname{mk}\left(0, h\right), 0)\right) = 0)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233198PairFibres}.\operatorname{PairNormal}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233198PairFibres}.\operatorname{rank}\left(\right), p\right)) \land (\forall (v: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(4\right))), (\forall (w: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(4\right))), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233198PairFibres}.\operatorname{Edge}\left(v, w\right)) \Rightarrow (p\left(v\right) \ne p\left(w\right)))))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233198LiteralModel.PairLegal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233198: normalized eight-colour arrays of width four*. URL: <https://oeis.org/A233198>.

*Commentary.*

The same literal edge relation is used for the pair map. First-use requirements allow higher pairs to remain absent.

**Definition 1.9 (First occurrence in a pair).**

$$\forall (V: \operatorname{Type}), (\forall (r: V \to \operatorname{Nat}), (\forall (p: V \to \operatorname{Fin}\left(4\right)), (\forall (v: V), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233198PairFibres}.\operatorname{First}\left(r, p, v\right)) \Leftrightarrow (\forall (w: V), ((r\left(w\right) < r\left(v\right)) \Rightarrow (p\left(w\right) \ne p\left(v\right))))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233198LiteralModel.First` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233198: normalized eight-colour arrays of width four*. URL: <https://oeis.org/A233198>.

*Commentary.*

The comparison uses the supplied natural rank function.

**Definition 1.10 (The independent binary positions).**

$$\forall (n: \operatorname{Nat}), (\forall (p: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(4\right)) \to \operatorname{Fin}\left(4\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233198PairFibres}.\operatorname{Free}\left(p\right) = \operatorname{Subtype}\left((\lambda (v: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(4\right))) \mapsto \neg(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233198PairFibres}.\operatorname{First}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233198PairFibres}.\operatorname{rank}\left(\right), p, v\right)))\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233198LiteralModel.Free` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233198: normalized eight-colour arrays of width four*. URL: <https://oeis.org/A233198>.

*Commentary.*

A free cell has an earlier cell with the same pair label. The first member of each used pair is forced to be its smaller colour.

**Definition 1.11 (Literal fibre cardinality).**

$$\forall (n: \operatorname{Nat}), (\forall (p: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(4\right)) \to \operatorname{Fin}\left(4\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233198PairFibres}.\operatorname{fibreCount}\left(p\right) = \operatorname{Nat}.\operatorname{card}\left(\operatorname{Subtype}\left((\lambda (f: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(4\right)) \to \operatorname{Fin}\left(8\right)) \mapsto (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233198PairFibres}.\operatorname{Legal}\left(f\right)) \land ((\lambda (v: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(4\right))) \mapsto \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233198PairFibres}.\operatorname{pair}\left(f\left(v\right)\right)) = p))\right)\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233198LiteralModel.fibreCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233198: normalized eight-colour arrays of width four*. URL: <https://oeis.org/A233198>.

*Commentary.*

The fibre consists of the literal arrays whose pointwise pair map equals p.

**Definition 1.12 (Ordinary colourings on the same graph).**

$$\forall (q: \operatorname{Nat}), (\forall (n: \operatorname{Nat}), (\forall (f: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(4\right)) \to \operatorname{Fin}\left(q\right)), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233198PairFibres}.\operatorname{Proper}\left(f\right)) \Leftrightarrow (\forall (v: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(4\right))), (\forall (w: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(4\right))), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233198PairFibres}.\operatorname{Edge}\left(v, w\right)) \Rightarrow (f\left(v\right) \ne f\left(w\right))))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233198LiteralModel.Proper` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233198: normalized eight-colour arrays of width four*. URL: <https://oeis.org/A233198>.

*Commentary.*

The finite colour set has q labels. Every literal contained edge is retained. These ordinary maps have no anchor or earlier-colour prerequisites.

**Definition 1.13 (The labelled colouring count).**

$$\forall (q: \operatorname{Nat}), (\forall (n: \operatorname{Nat}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233198PairFibres}.\operatorname{ordinaryCount}\left(q, n\right) = \operatorname{Nat}.\operatorname{card}\left(\operatorname{Subtype}\left((\lambda (f: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(4\right)) \to \operatorname{Fin}\left(q\right)) \mapsto \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233198PairFibres}.\operatorname{Proper}\left(f\right))\right)\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233198LiteralModel.ordinaryCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233198: normalized eight-colour arrays of width four*. URL: <https://oeis.org/A233198>.

*Commentary.*

All proper functions are counted, including functions that omit labels.

**Definition 1.14 (The ordinary colouring series).**

$$\forall (q: \operatorname{Nat}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233198PairFibres}.\operatorname{ordinarySeries}\left(q\right) = \operatorname{PowerSeries}.\operatorname{mk}\left((\lambda (n: \operatorname{Nat}) \mapsto \operatorname{ite}\left(n = 0, 0, (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233198PairFibres}.\operatorname{ordinaryCount}\left(q, n\right): \operatorname{Rat})\right))\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233198LiteralModel.ordinarySeries` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233198: normalized eight-colour arrays of width four*. URL: <https://oeis.org/A233198>.

*Commentary.*

The coefficient at zero is zero. Positive coefficients count the same contained horizontal, vertical and antidiagonal graph.

**Theorem 1.15 (The exact pair fibre).**

$$\forall (n: \operatorname{Nat}), (\forall (p: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(4\right)) \to \operatorname{Fin}\left(4\right)), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233198PairFibres}.\operatorname{PairLegal}\left(p\right)) \Rightarrow (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233198PairFibres}.\operatorname{fibreCount}\left(p\right) = 2^{\operatorname{Nat}.\operatorname{card}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233198PairFibres}.\operatorname{Free}\left(p\right)\right)})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233198LiteralModel.literal_fibre_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233198: normalized eight-colour arrays of width four*. URL: <https://oeis.org/A233198>.

*Commentary.*

Fix a proper ordered pair map. Assign its smaller colour at each first occurrence and either complementary colour at every other cell. Least-rank representatives supply all literal earlier-colour requirements. Conversely the literal prerequisites force the smaller first representatives. These constructions are inverse and identify the fibre with all Boolean assignments to Free p.

**Theorem 1.16 (One forced cell per used pair).**

$$\forall (n: \operatorname{Nat}), (\forall (p: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(4\right)) \to \operatorname{Fin}\left(4\right)), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233198PairFibres}.\operatorname{PairLegal}\left(p\right)) \Rightarrow (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233198PairFibres}.\operatorname{fibreCount}\left(p\right) = 2^{\operatorname{Nat}.\operatorname{sub}\left((4) \cdot (n), \operatorname{Nat}.\operatorname{card}\left(\operatorname{Set}.\operatorname{range}\left(p\right)\right)\right)})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233198LiteralModel.literal_fibre_power` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233198: normalized eight-colour arrays of width four*. URL: <https://oeis.org/A233198>.

*Commentary.*

The first cells are in bijection with the range of the pair map. Distinct first cells cannot have the same pair because row-major rank is injective. Every used pair has a least-rank representative. There are four times n cells altogether.

**Theorem 1.17 (The disjoint fibre sum).**

$$\forall (n: \operatorname{Nat}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233198PairFibres}.\operatorname{a}\left(n\right) = \operatorname{Finset}.\operatorname{sum}\left(\operatorname{Finset}.\operatorname{univ}, (\lambda (p: \operatorname{Subtype}\left((\lambda (p: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(4\right)) \to \operatorname{Fin}\left(4\right)) \mapsto \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233198PairFibres}.\operatorname{PairLegal}\left(p\right))\right)) \mapsto 2^{\operatorname{Nat}.\operatorname{sub}\left((4) \cdot (n), \operatorname{Nat}.\operatorname{card}\left(\operatorname{Set}.\operatorname{range}\left(\operatorname{Subtype}.\operatorname{val}\left(p\right)\right)\right)\right)})\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233198LiteralModel.literal_count_by_pairs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233198: normalized eight-colour arrays of width four*. URL: <https://oeis.org/A233198>.

*Commentary.*

Every literal array determines a unique legal pair map. Summation over all such maps includes every possible number of used pairs.

**Theorem 1.18 (Injective labels on the used pairs).**

$$\forall (q: \operatorname{Nat}), (\forall (n: \operatorname{Nat}), ((q \le 4) \Rightarrow ((0 < n) \Rightarrow (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233198PairFibres}.\operatorname{ordinaryCount}\left(q, n\right) = \operatorname{Finset}.\operatorname{sum}\left(\operatorname{Finset}.\operatorname{univ}, (\lambda (p: \operatorname{Subtype}\left((\lambda (p: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(4\right)) \to \operatorname{Fin}\left(4\right)) \mapsto \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233198PairFibres}.\operatorname{PairLegal}\left(p\right))\right)) \mapsto \operatorname{Nat}.\operatorname{descFactorial}\left(q, \operatorname{Nat}.\operatorname{card}\left(\operatorname{Set}.\operatorname{range}\left(\operatorname{Subtype}.\operatorname{val}\left(p\right)\right)\right)\right))\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233198LiteralModel.ordinary_count_by_pairs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233198: normalized eight-colour arrays of width four*. URL: <https://oeis.org/A233198>.

*Commentary.*

Order the used colour classes by their least row-major ranks. Missing labels are ordered after every actual cell. The resulting canonical pair map satisfies the anchor and first-use conditions. Two such pair maps with the same equality classes agree: at a first disagreement, the smaller label must already have occurred in the other map. Injective assignments of q labels to the used pairs are therefore in bijection with all proper q-colourings. The falling factorial counts these assignments even when some labels are unused.

**Theorem 1.19 (The complete weighted count).**

$$\forall (n: \operatorname{Nat}), ((0 < n) \Rightarrow ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233198PairFibres}.\operatorname{a}\left(n\right): \operatorname{Rat}) = (16^{\operatorname{Nat}.\operatorname{sub}\left(n, 1\right)}) \cdot (((\frac{(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233198PairFibres}.\operatorname{ordinaryCount}\left(4, n\right): \operatorname{Rat})}{24}) + (\frac{(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233198PairFibres}.\operatorname{ordinaryCount}\left(3, n\right): \operatorname{Rat})}{6})) + (\frac{(5) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{ComplementaryPairs}.\operatorname{HardinA233198PairFibres}.\operatorname{ordinaryCount}\left(2, n\right): \operatorname{Rat}))}{4}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233198LiteralModel.literal_ordinary_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233198: normalized eight-colour arrays of width four*. URL: <https://oeis.org/A233198>.

*Commentary.*

Every positive-height graph has a horizontal edge, so each legal pair map uses two, three or four pairs. For each of these three possibilities, the Boolean fibre weight equals the stated weighted falling-factorial combination. Summation gives the identity without an orbit division or a surjectivity assumption.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233198LiteralModel.A`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233198LiteralModel.Edge`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233198LiteralModel.First`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233198LiteralModel.Free`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233198LiteralModel.Legal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233198LiteralModel.Normal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233198LiteralModel.PairLegal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233198LiteralModel.PairNormal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233198LiteralModel.Proper`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233198LiteralModel.a`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233198LiteralModel.fibreCount`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233198LiteralModel.literal_count_by_pairs`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233198LiteralModel.literal_fibre_card`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233198LiteralModel.literal_fibre_power`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233198LiteralModel.literal_ordinary_count`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233198LiteralModel.ordinaryCount`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233198LiteralModel.ordinarySeries`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233198LiteralModel.ordinary_count_by_pairs`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233198LiteralModel.pair`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip](../HardinA233196Strip.md)
