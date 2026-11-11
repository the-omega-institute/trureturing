# Literal arrays and seven boundary classes

## Abstract

Hardin's recurrence for literal normalized five-column diagonal strips.

Rows are functions on Fin 5 with values in Fin 6. The horizontal predicate and its decision procedure belong to HardinA233253TriangleStrip. Boundary and Valid belong to HardinA233254TriangleStrip. The labels, boundaryClass and firstCount belong to HardinA233126SquareStrip. All declaration names are fully qualified. Fin.val converts a finite index or colour to Nat. The pair labels have fibres {0,5}, {1,4}, {2,3}.

**Definition 1.1 (Both diagonal exclusions).**

$$\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{Row}), (\forall (d: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{Row}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233171DiagonalStrip}.\operatorname{bonds}\left(c, d\right) = \forall (j: \operatorname{Fin}\left(4\right)), (((c\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right) \ne d\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right)) \land ((\operatorname{Fin}.\operatorname{val}\left(c\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right)\right)) + (\operatorname{Fin}.\operatorname{val}\left(d\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right)\right)) \ne 5)) \land ((c\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right) \ne d\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right)) \land ((\operatorname{Fin}.\operatorname{val}\left(c\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right)\right)) + (\operatorname{Fin}.\operatorname{val}\left(d\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right)\right)) \ne 5)))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233171DiagonalStrip.bonds` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233171: normalized six-colour five-column arrays with both diagonal exclusions*. URL: <https://oeis.org/A233171>.

*Commentary.*

Both diagonals join consecutive rows; no vertical or wraparound bond is imposed.

**Definition 1.2 (The literal filtered count).**

$$\forall (n: \operatorname{Nat}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233171DiagonalStrip}.\operatorname{a}\left(n\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left(((A: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(5\right)) \to \operatorname{Fin}\left(6\right)) \mapsto (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233251TriangleStrip}.\operatorname{widthLegal}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{rowLegal}, \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233171DiagonalStrip}.\operatorname{bonds}, A\right))), (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left((\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(5\right)) \to \operatorname{Fin}\left(6\right)\right))\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233171DiagonalStrip.a` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233171: normalized six-colour five-column arrays with both diagonal exclusions*. URL: <https://oeis.org/A233171>.

*Commentary.*

The filter is over all array functions. The owner widthLegal fixes the first cell to zero, checks horizontal bonds and the displayed diagonals, and applies widthNormal at (false,false). For every occurrence of 2, 3 or 4 there is an earlier 1, and for every 3 an earlier 2, in strict row-major order. Colours may be absent. There is no orbit divisor. At height zero the first-cell existential is false.

**Definition 1.3 (Diagonal label compatibility).**

$$\forall (p: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{Boundary}), (\forall (c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{Row}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233171DiagonalStrip}.\operatorname{compatible}\left(p, c\right) = \forall (j: \operatorname{Fin}\left(4\right)), ((p\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right) \ne \operatorname{D5}.\operatorname{S3}.\operatorname{Observer}.\operatorname{Separation}.\operatorname{BooleanRankThreeK4}.\operatorname{beta}\left(c\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right)\right)) \land (p\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right) \ne \operatorname{D5}.\operatorname{S3}.\operatorname{Observer}.\operatorname{Separation}.\operatorname{BooleanRankThreeK4}.\operatorname{beta}\left(c\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right)\right)))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233171DiagonalStrip.compatible` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233171: normalized six-colour five-column arrays with both diagonal exclusions*. URL: <https://oeis.org/A233171>.

*Commentary.*

Every diagonal bond excludes the preceding complementary-pair label.

**Definition 1.4 (The seven-class transfer).**

$$\forall (i: \operatorname{Fin}\left(7\right)), (\forall (k: \operatorname{Fin}\left(7\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233171DiagonalStrip}.\operatorname{transfer}\left(i, k\right) = (![![32, 32, 64, 32, 32, 0, 32], ![0, 96, 128, 64, 64, 0, 64], ![0, 64, 128, 32, 32, 0, 64], ![0, 64, 64, 64, 64, 32, 0], ![0, 32, 32, 32, 64, 32, 0], ![0, 0, 0, 32, 64, 32, 0], ![0, 64, 128, 0, 0, 0, 64]]\left(i\right)\left(k\right): \operatorname{Int})))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233171DiagonalStrip.transfer` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233171: normalized six-colour five-column arrays with both diagonal exclusions*. URL: <https://oeis.org/A233171>.

*Commentary.*

Source classes index rows and destination classes index columns. Class zero has not yet seen colour 2. The remaining classes use the owner's six label-permutation and reversal shapes. Their sizes are 6,12,6,12,6,6.

**Definition 1.5 (Exact continuation counts).**

$$\forall (s: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{Seen}), (\forall (p: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233254TriangleStrip}.\operatorname{Boundary}), (\forall (k: \operatorname{Fin}\left(7\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233171DiagonalStrip}.\operatorname{classCount}\left(s, p, k\right) = \sum_{c: \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{Row}} (((\operatorname{if} ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233253TriangleStrip}.\operatorname{rowLegal}\left(c\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233171DiagonalStrip}.\operatorname{compatible}\left(p, c\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{good}\left(s, c\right)) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233126SquareStrip}.\operatorname{boundaryClass}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233175PairStrip}.\operatorname{finish}\left(s, c\right), \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233126SquareStrip}.\operatorname{labels}\left(c\right)\right) = k)))) \operatorname{then} (1) \operatorname{else} (0)): \operatorname{Int})))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233171DiagonalStrip.classCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233171: normalized six-colour five-column arrays with both diagonal exclusions*. URL: <https://oeis.org/A233171>.

*Commentary.*

The sum ranges over the original individual colour rows with the original scanner.

**Theorem 1.6 (Hardin's recurrence for every height at least eight).**

$$\forall (n: \operatorname{Nat}), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233171DiagonalStrip}.\operatorname{a}\left((n) + (8)\right): \operatorname{Int}) = (((((((480) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233171DiagonalStrip}.\operatorname{a}\left((n) + (7)\right): \operatorname{Int}))) - ((60416) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233171DiagonalStrip}.\operatorname{a}\left((n) + (6)\right): \operatorname{Int})))) + ((1966080) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233171DiagonalStrip}.\operatorname{a}\left((n) + (5)\right): \operatorname{Int})))) + ((22020096) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233171DiagonalStrip}.\operatorname{a}\left((n) + (4)\right): \operatorname{Int})))) - ((1845493760) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233171DiagonalStrip}.\operatorname{a}\left((n) + (3)\right): \operatorname{Int})))) + ((22548578304) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233171DiagonalStrip}.\operatorname{a}\left((n) + (2)\right): \operatorname{Int})))) - ((68719476736) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233171DiagonalStrip}.\operatorname{a}\left((n) + (1)\right): \operatorname{Int}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233171DiagonalStrip.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin233171` (proved) by `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233171DiagonalStrip.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin233171","declaration_gid":"D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233171DiagonalStrip.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233171: normalized six-colour five-column arrays with both diagonal exclusions*. URL: <https://oeis.org/A233171>.

*Commentary.*

The width-independent literal counting bridge and exact scanner fibres give the displayed class transfer. The owner's compatibility-free row_valid supplies boundary validity. The private finite_certificate proves the diagonal graph's class transfer and is used in the induction identifying all continuations with powers of this transfer. The reused first-row distribution is (8,0,8,4,8,4,4). Its eighth Krylov row is the stated integer linear combination of its first seven rows. The numerical premises are finite_certificate, distribution_step for consecutive row products, and distribution_relation for this integer relation; all feed result. Multiplying this identity by every continuation vector proves the recurrence for all n+8. Thus the literal count, defined independently of the recurrence, satisfies the displayed order-seven relation.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233171DiagonalStrip.a`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233171DiagonalStrip.bonds`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233171DiagonalStrip.classCount`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233171DiagonalStrip.compatible`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233171DiagonalStrip.result`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233171DiagonalStrip.transfer`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233126SquareStrip](HardinA233126SquareStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip](HardinA233175PairStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip](HardinA233251TriangleStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233253TriangleStrip](HardinA233253TriangleStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233254TriangleStrip](HardinA233254TriangleStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge](HardinA233255LiteralBridge.md)
- Dependency: [D5/S3/Observer/Separation/BooleanRankThreeK4](../../Observer/Separation/BooleanRankThreeK4.md)
