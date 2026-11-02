# Irwin's hook-sum conjecture for OEIS A138099

## Abstract

The row-flattened triangle equals each hook-sum increment of the square spiral.

OEIS A138099, revision 26, NAME and Irwin FORMULA block (unpaginated). Coordinates are horizontal and vertical integers, with the vertical coordinate increasing downwards. The first cell is the origin; directions are west, south, east, north and leg lengths are 1, 1, 2, 2, 3, 3, and so on. The diagrams retain their actual occupied positions. All Nat.div and Nat.mod operations below are natural quotient and remainder; natural subtraction is truncated. Hook-sum subtraction is performed after casting both sums to the integers.

**Definition 1.1 (Triangle entries).**

$$\forall (k : \mathbb{N}), \forall (j : \mathbb{N}), \operatorname{triangleEntry}\left(k, j\right) = j + \operatorname{Nat.div}\left(k, 2\right)$$

*Formalization.* `D5/S3/Combinatorics/Polyomino/IrwinA138099HookSum.triangleEntry` (`✓ std3`).

*Citation.* Paul Curtz and Benedict W. J. Irwin (2016). *OEIS A138099: irregular triangle and Irwin's hook-sum conjecture*. URL: <https://oeis.org/A138099>.

*Commentary.*

Irregular triangle read by rows: T(n,k) = k + floor(n/2), 1 <= k <= ceiling(n/2). Here k is the source's row n and j is its column k. The formula is used at 1 <= k and 1 <= j <= (k+1)/2.

**Definition 1.2 (Cumulative row lengths).**

$$\forall (k : \mathbb{N}), \operatorname{trianglePrefix}\left(k\right) = (\operatorname{Finset.range}\left(k\right)).sum\left((i : \mathbb{N}) \mapsto \operatorname{Nat.div}\left(i + 2, 2\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Polyomino/IrwinA138099HookSum.trianglePrefix` (`✓ std3`).

*Citation.* Paul Curtz and Benedict W. J. Irwin (2016). *OEIS A138099: irregular triangle and Irwin's hook-sum conjecture*. URL: <https://oeis.org/A138099>.

*Commentary.*

Irregular triangle read by rows: T(n,k) = k + floor(n/2), 1 <= k <= ceiling(n/2). Row i+1 has (i+2)/2 entries, so trianglePrefix k counts the entries in rows 1 through k. The sum for k=0 is empty.

**Definition 1.3 (The sequence read by rows).**

$$\forall (a : \mathbb{N} \to \mathbb{N}), (\operatorname{IsSourceSequence}\left(a\right)) \Leftrightarrow (\forall (k : \mathbb{N}), (1 \le k) \Rightarrow (\forall (j : \mathbb{N}), (1 \le j) \Rightarrow ((j \le \operatorname{Nat.div}\left(k + 1, 2\right)) \Rightarrow (a\left(\operatorname{trianglePrefix}\left(k - 1\right) + j\right) = \operatorname{triangleEntry}\left(k, j\right)))))$$

*Formalization.* `D5/S3/Combinatorics/Polyomino/IrwinA138099HookSum.IsSourceSequence` (`✓ std3`).

*Citation.* Paul Curtz and Benedict W. J. Irwin (2016). *OEIS A138099: irregular triangle and Irwin's hook-sum conjecture*. URL: <https://oeis.org/A138099>.

*Commentary.*

Irregular triangle read by rows: T(n,k) = k + floor(n/2), 1 <= k <= ceiling(n/2). Indices start at one, as in the entry's offset 1,2. The value at index zero is unrestricted.

**Definition 1.4 (The four leg directions).**

$$\forall (leg : \mathbb{N}), \operatorname{legDirection}\left(leg\right) = \operatorname{match} \operatorname{Nat.mod}\left(leg, 4\right) \operatorname{with} \begin{aligned}0 \mapsto (-1, 0)\\1 \mapsto (0, 1)\\2 \mapsto (1, 0)\\\operatorname{otherwise} \mapsto (0, -1)\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/Polyomino/IrwinA138099HookSum.legDirection` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul Curtz and Benedict W. J. Irwin (2016). *OEIS A138099: irregular triangle and Irwin's hook-sum conjecture*. URL: <https://oeis.org/A138099>.

*Commentary.*

The four cases describe west, south, east and north respectively. They repeat with period four.

**Definition 1.5 (Position and leg counters).**

$$WalkState : Type; cell : (\mathbb{Z} \times \mathbb{Z}); leg : \mathbb{N}; used : \mathbb{N}$$

*Formalization.* `D5/S3/Combinatorics/Polyomino/IrwinA138099HookSum.WalkState` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul Curtz and Benedict W. J. Irwin (2016). *OEIS A138099: irregular triangle and Irwin's hook-sum conjecture*. URL: <https://oeis.org/A138099>.

*Commentary.*

WalkState has exactly the three fields cell, leg and used, of the displayed types. The field used counts steps already taken on the current leg.

**Definition 1.6 (One step and a possible turn).**

$$\forall (s : WalkState), \operatorname{advance}\left(s\right) = \operatorname{let} d : (\mathbb{Z} \times \mathbb{Z}) := \operatorname{legDirection}\left(s.leg\right); \operatorname{let} p : (\mathbb{Z} \times \mathbb{Z}) := (s.cell.1 + d.1, s.cell.2 + d.2); \operatorname{ite}\left(s.used + 1 = \operatorname{Nat.div}\left(s.leg, 2\right) + 1, \langle p, s.leg + 1, 0 \rangle, \langle p, s.leg, s.used + 1 \rangle\right)$$

*Formalization.* `D5/S3/Combinatorics/Polyomino/IrwinA138099HookSum.advance` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul Curtz and Benedict W. J. Irwin (2016). *OEIS A138099: irregular triangle and Irwin's hook-sum conjecture*. URL: <https://oeis.org/A138099>.

*Commentary.*

The direction d determines the next position p. A completed leg advances the leg counter and resets used; otherwise used increases by one. Every leg has positive length.

**Definition 1.7 (The literal unit-step walk).**

$$(\operatorname{walk}\left(0\right) = \langle (0, 0), 0, 0 \rangle) \land (\forall (n : \mathbb{N}), \operatorname{walk}\left(n + 1\right) = \operatorname{advance}\left(\operatorname{walk}\left(n\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/Polyomino/IrwinA138099HookSum.walk` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul Curtz and Benedict W. J. Irwin (2016). *OEIS A138099: irregular triangle and Irwin's hook-sum conjecture*. URL: <https://oeis.org/A138099>.

*Commentary.*

Cell zero is (0,0). Applying advance repeatedly gives the cells of the displayed spiral in their insertion order.

**Definition 1.8 (Spiral diagrams).**

$$\forall (T : \mathbb{N} \to \operatorname{Finset}\left((\mathbb{Z} \times \mathbb{Z})\right)), (\operatorname{IsSourceSpiral}\left(T\right)) \Leftrightarrow ((T\left(0\right) = \emptyset) \land (\forall (n : \mathbb{N}), T\left(n + 1\right) = \operatorname{insert}\left(\operatorname{walk}\left(n\right).cell, T\left(n\right)\right)))$$

*Formalization.* `D5/S3/Combinatorics/Polyomino/IrwinA138099HookSum.IsSourceSpiral` (`✓ std3`).

*Citation.* Paul Curtz and Benedict W. J. Irwin (2016). *OEIS A138099: irregular triangle and Irwin's hook-sum conjecture*. URL: <https://oeis.org/A138099>.

*Commentary.*

Conjecture: a(n) = HookSum(T(n))-HookSum(T(n-1)), where HookSum(A) is the sum of all hooks across a tableau A, and T(n) are the spiraling sequence of tableaux: The source's diagram, in its unpaginated FORMULA block, starts Empty, o, oo. Here T 0 is empty and T(n+1) inserts cell n of the walk. No reordering of rows or cells is performed.

**Definition 1.9 (Ordinary hooks in occupied cells).**

$$\forall (D : \operatorname{Finset}\left((\mathbb{Z} \times \mathbb{Z})\right)), \forall (c : (\mathbb{Z} \times \mathbb{Z})), \operatorname{hookLength}\left(D, c\right) = 1 + ((D).filter\left((d : (\mathbb{Z} \times \mathbb{Z})) \mapsto (d.2 = c.2) \land (c.1 < d.1)\right)).card + ((D).filter\left((d : (\mathbb{Z} \times \mathbb{Z})) \mapsto (d.1 = c.1) \land (c.2 < d.2)\right)).card$$

*Formalization.* `D5/S3/Combinatorics/Polyomino/IrwinA138099HookSum.hookLength` (`✓ std3`).

*Citation.* Paul Curtz and Benedict W. J. Irwin (2016). *OEIS A138099: irregular triangle and Irwin's hook-sum conjecture*. URL: <https://oeis.org/A138099>.

*Commentary.*

Conjecture: a(n) = HookSum(T(n))-HookSum(T(n-1)), where HookSum(A) is the sum of all hooks across a tableau A, and T(n) are the spiraling sequence of tableaux: The ordinary hook contains its own cell, the occupied cells strictly to its right in its row, and the occupied cells strictly below it in its column. The formula is used for c in D when summing hooks; holes are allowed.

**Definition 1.10 (The sum of all hooks).**

$$\forall (D : \operatorname{Finset}\left((\mathbb{Z} \times \mathbb{Z})\right)), \operatorname{hookSum}\left(D\right) = (D).sum\left((c : (\mathbb{Z} \times \mathbb{Z})) \mapsto \operatorname{hookLength}\left(D, c\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Polyomino/IrwinA138099HookSum.hookSum` (`✓ std3`).

*Citation.* Paul Curtz and Benedict W. J. Irwin (2016). *OEIS A138099: irregular triangle and Irwin's hook-sum conjecture*. URL: <https://oeis.org/A138099>.

*Commentary.*

Conjecture: a(n) = HookSum(T(n))-HookSum(T(n-1)), where HookSum(A) is the sum of all hooks across a tableau A, and T(n) are the spiraling sequence of tableaux: This finite sum uses the occupied cells themselves, including the empty sum zero.

**Definition 1.11 (The source assertion with existence).**

$$(claim) \Leftrightarrow ((\exists (a : \mathbb{N} \to \mathbb{N}), \operatorname{IsSourceSequence}\left(a\right)) \land ((\exists (T : \mathbb{N} \to \operatorname{Finset}\left((\mathbb{Z} \times \mathbb{Z})\right)), \operatorname{IsSourceSpiral}\left(T\right)) \land (\forall (a : \mathbb{N} \to \mathbb{N}), \forall (T : \mathbb{N} \to \operatorname{Finset}\left((\mathbb{Z} \times \mathbb{Z})\right)), (\operatorname{IsSourceSequence}\left(a\right)) \Rightarrow ((\operatorname{IsSourceSpiral}\left(T\right)) \Rightarrow (\forall (n : \mathbb{N}), (1 \le n) \Rightarrow ((a\left(n\right) : \mathbb{Z}) = (\operatorname{hookSum}\left(T\left(n\right)\right) : \mathbb{Z}) - (\operatorname{hookSum}\left(T\left(n - 1\right)\right) : \mathbb{Z})))))))$$

*Formalization.* `D5/S3/Combinatorics/Polyomino/IrwinA138099HookSum.claim` (`✓ std3`).

*Citation.* Paul Curtz and Benedict W. J. Irwin (2016). *OEIS A138099: irregular triangle and Irwin's hook-sum conjecture*. URL: <https://oeis.org/A138099>.

*Commentary.*

Conjecture: a(n) = HookSum(T(n))-HookSum(T(n-1)), where HookSum(A) is the sum of all hooks across a tableau A, and T(n) are the spiraling sequence of tableaux: This is the complete sentence in Irwin's unpaginated FORMULA block. The arithmetic and spiral sequences both exist, and the identity holds for every pair of such sequences and every positive index. The first two conjuncts assert existence rather than assume it.

**Theorem 1.12 (The hook-sum identity at every positive index).**

$$(\exists (a : \mathbb{N} \to \mathbb{N}), \operatorname{IsSourceSequence}\left(a\right)) \land ((\exists (T : \mathbb{N} \to \operatorname{Finset}\left((\mathbb{Z} \times \mathbb{Z})\right)), \operatorname{IsSourceSpiral}\left(T\right)) \land (\forall (a : \mathbb{N} \to \mathbb{N}), \forall (T : \mathbb{N} \to \operatorname{Finset}\left((\mathbb{Z} \times \mathbb{Z})\right)), (\operatorname{IsSourceSequence}\left(a\right)) \Rightarrow ((\operatorname{IsSourceSpiral}\left(T\right)) \Rightarrow (\forall (n : \mathbb{N}), (1 \le n) \Rightarrow ((a\left(n\right) : \mathbb{Z}) = (\operatorname{hookSum}\left(T\left(n\right)\right) : \mathbb{Z}) - (\operatorname{hookSum}\left(T\left(n - 1\right)\right) : \mathbb{Z}))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Polyomino/IrwinA138099HookSum.result` (`✓ std3`). ∎

*Resolves.* `Problems/irwin-a138099` (proved) by `D5/S3/Combinatorics/Polyomino/IrwinA138099HookSum.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"irwin-a138099","declaration_gid":"D5/S3/Combinatorics/Polyomino/IrwinA138099HookSum.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul Curtz and Benedict W. J. Irwin (2016). *OEIS A138099: irregular triangle and Irwin's hook-sum conjecture*. URL: <https://oeis.org/A138099>.

*Commentary.*

Inserting a fresh cell increases the total hook sum by one plus the old row and column sizes. After m squared cells the walk fills an m by m square. Its next m cells form one boundary strip and its next m+1 cells form the other. Their increments are m+j, exactly the entries of source rows 2m and 2m+1. The first singleton is handled separately. Row addresses also construct a source arithmetic sequence, and the insertion recursion constructs and uniquely determines the source spiral.

## References

- Truth anchor: `D5/S3/Combinatorics/Polyomino/IrwinA138099HookSum.IsSourceSequence`
- Truth anchor: `D5/S3/Combinatorics/Polyomino/IrwinA138099HookSum.IsSourceSpiral`
- Truth anchor: `D5/S3/Combinatorics/Polyomino/IrwinA138099HookSum.WalkState`
- Truth anchor: `D5/S3/Combinatorics/Polyomino/IrwinA138099HookSum.advance`
- Truth anchor: `D5/S3/Combinatorics/Polyomino/IrwinA138099HookSum.claim`
- Truth anchor: `D5/S3/Combinatorics/Polyomino/IrwinA138099HookSum.hookLength`
- Truth anchor: `D5/S3/Combinatorics/Polyomino/IrwinA138099HookSum.hookSum`
- Truth anchor: `D5/S3/Combinatorics/Polyomino/IrwinA138099HookSum.legDirection`
- Truth anchor: `D5/S3/Combinatorics/Polyomino/IrwinA138099HookSum.result`
- Truth anchor: `D5/S3/Combinatorics/Polyomino/IrwinA138099HookSum.triangleEntry`
- Truth anchor: `D5/S3/Combinatorics/Polyomino/IrwinA138099HookSum.trianglePrefix`
- Truth anchor: `D5/S3/Combinatorics/Polyomino/IrwinA138099HookSum.walk`
