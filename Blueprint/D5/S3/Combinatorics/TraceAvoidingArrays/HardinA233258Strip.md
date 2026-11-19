# Three-row complementary-pair exclusion

## Abstract

Hardin's recurrence and Barker's generating function for literal three-row colourings.

Cells are Fin 3 times Fin n, with colour set Fin 6. A bond joins cells in consecutive columns when their row indices are equal or the old row is one greater than the new row. Each bond excludes equal colours and colours summing to five. The top left colour is zero; first occurrences obey the strict row-major rank r*n+j, as defined by HardinA233176Ladder.normal.

**Definition 1.1 (Literal array conditions).**

$$\forall (n: \operatorname{Nat}), (\forall (A: (\operatorname{Fin}\left(3\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(6\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233258Strip}.\operatorname{Legal}\left(A\right) = ((\exists (j: \operatorname{Fin}\left(n\right)), ((\operatorname{Fin}.\operatorname{val}\left(j\right) = 0) \land (A\left(((0: \operatorname{Fin}\left(3\right)), j)\right) = (0: \operatorname{Fin}\left(6\right))))) \land ((\forall (j: \operatorname{Fin}\left(n\right)), (\forall (h: (\operatorname{Fin}.\operatorname{val}\left(j\right)) + (1) < n), (\forall (r: \operatorname{Fin}\left(3\right)), (\forall (s: \operatorname{Fin}\left(3\right)), (((r = s) \lor (\operatorname{Fin}.\operatorname{val}\left(r\right) = (\operatorname{Fin}.\operatorname{val}\left(s\right)) + (1))) \Rightarrow ((A\left((r, j)\right) \ne A\left((s, (\operatorname{Fin}.\operatorname{mk}\left((\operatorname{Fin}.\operatorname{val}\left(j\right)) + (1), h\right): \operatorname{Fin}\left(n\right)))\right)) \land ((\operatorname{Fin}.\operatorname{val}\left(A\left((r, j)\right)\right)) + (\operatorname{Fin}.\operatorname{val}\left(A\left((s, (\operatorname{Fin}.\operatorname{mk}\left((\operatorname{Fin}.\operatorname{val}\left(j\right)) + (1), h\right): \operatorname{Fin}\left(n\right)))\right)\right)) \ne 5))))))) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233176Ladder}.\operatorname{normal}\left(A\right))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258Strip.Legal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233258: three-row horizontal and antidiagonal pair exclusion*. URL: <https://oeis.org/A233258>.

*Commentary.*

Literal array conditions.

**Definition 1.2 (The literal filtered array count).**

$$\forall (n: \operatorname{Nat}), (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233258Strip}.\operatorname{a}\left(n\right) = (\operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((\lambda (A: (\operatorname{Fin}\left(3\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(6\right)) \mapsto \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233258Strip}.\operatorname{Legal}\left(A\right)), (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left((\operatorname{Fin}\left(3\right)) \times (\operatorname{Fin}\left(n\right)) \to \operatorname{Fin}\left(6\right)\right))\right)\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258Strip.a` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233258: three-row horizontal and antidiagonal pair exclusion*. URL: <https://oeis.org/A233258>.

*Commentary.*

The literal filtered array count.

**Theorem 1.3 (The canonical-form counting bridge).**

$$\forall (n: \operatorname{Nat}), ((2 \le n) \Rightarrow ((48) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233258Strip}.\operatorname{a}\left(n\right): \operatorname{Int})) = ((8: \operatorname{Int})^{n}) \cdot (((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233258PairTransfer}.\operatorname{L}\left(n\right): \operatorname{Int})) + (6))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258Strip.counting_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233258: three-row horizontal and antidiagonal pair exclusion*. URL: <https://oeis.org/A233258>.

*Commentary.*

The canonical-form counting bridge.

The beta-label identifies {0,5}, {1,4} and {2,3}. The canonical first-occurrence theorems apply to the cells with their row-major linear order. A canonical pattern using k labels has 2^(3*n-k) normalized lifts. At width at least two a proper pattern uses two or three labels and its relabelling orbit has six members. When a label is omitted, consecutive rows in each column have a common neighbour in an adjacent column, forcing equality. Every column is constant and the two labels alternate. There is exactly one canonical pattern of this kind. If C counts canonical proper patterns, L=6*C and a=2^(3*n-3)*(C+1), yielding the bridge.

**Theorem 1.4 (The width-six recurrence instance).**

$$(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233258Strip}.\operatorname{a}\left(6\right): \operatorname{Int}) = (((48) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233258Strip}.\operatorname{a}\left(5\right): \operatorname{Int}))) - ((448) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233258Strip}.\operatorname{a}\left(4\right): \operatorname{Int})))) + ((1024) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233258Strip}.\operatorname{a}\left(3\right): \operatorname{Int})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258Strip.finite_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233258: three-row horizontal and antidiagonal pair exclusion*. URL: <https://oeis.org/A233258>.

*Commentary.*

The width-six recurrence instance.

**Theorem 1.5 (The recurrence and exact integer power-series identity).**

$$(\forall (n: \operatorname{Nat}), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233258Strip}.\operatorname{a}\left((n) + (6)\right): \operatorname{Int}) = (((48) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233258Strip}.\operatorname{a}\left((n) + (5)\right): \operatorname{Int}))) - ((448) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233258Strip}.\operatorname{a}\left((n) + (4)\right): \operatorname{Int})))) + ((1024) \cdot ((\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233258Strip}.\operatorname{a}\left((n) + (3)\right): \operatorname{Int}))))) \land ((((1) - ((8) \cdot ((\operatorname{PowerSeries}.\operatorname{X}: \operatorname{PowerSeries}\left(\operatorname{Int}\right))))) \cdot (((1) - ((40) \cdot ((\operatorname{PowerSeries}.\operatorname{X}: \operatorname{PowerSeries}\left(\operatorname{Int}\right))))) + ((128) \cdot ((\operatorname{PowerSeries}.\operatorname{X}: \operatorname{PowerSeries}\left(\operatorname{Int}\right))^{2})))) \cdot (\operatorname{PowerSeries}.\operatorname{mk}\left((\lambda (n: \operatorname{Nat}) \mapsto (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233258Strip}.\operatorname{a}\left(n\right): \operatorname{Int}))\right)) = ((\operatorname{PowerSeries}.\operatorname{X}: \operatorname{PowerSeries}\left(\operatorname{Int}\right))) \cdot (((((11) - ((392) \cdot ((\operatorname{PowerSeries}.\operatorname{X}: \operatorname{PowerSeries}\left(\operatorname{Int}\right))))) + ((3072) \cdot ((\operatorname{PowerSeries}.\operatorname{X}: \operatorname{PowerSeries}\left(\operatorname{Int}\right))^{2}))) - ((8192) \cdot ((\operatorname{PowerSeries}.\operatorname{X}: \operatorname{PowerSeries}\left(\operatorname{Int}\right))^{3}))) + ((16384) \cdot ((\operatorname{PowerSeries}.\operatorname{X}: \operatorname{PowerSeries}\left(\operatorname{Int}\right))^{4}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258Strip.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin233258` (proved) by `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258Strip.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin233258","declaration_gid":"D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258Strip.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233258: three-row horizontal and antidiagonal pair exclusion*. URL: <https://oeis.org/A233258>.

*Commentary.*

The recurrence and exact integer power-series identity.

Scaling L(n)+6 by 8^n multiplies the coefficient at lag j by 8^j, giving coefficients 48,-448,1024. The index n+6 covers every width at least six. The initial counts at widths zero through five are 0,11,136,4672,166400,6049792. Coefficient comparison in PowerSeries Int gives Barker's identity; its denominator has constant coefficient one. The width-one count is taken directly from the literal finite filter.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258Strip.Legal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258Strip.a`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258Strip.counting_bridge`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258Strip.finite_certificate`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258Strip.result`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233176Ladder](HardinA233176Ladder.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](HardinA233177Canonical.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Ladder](HardinA233177Ladder.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip](HardinA233251TriangleStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258PairTransfer](HardinA233258PairTransfer.md)
- Dependency: [D5/S3/Observer/Separation/BooleanRankThreeK4](../../Observer/Separation/BooleanRankThreeK4.md)
