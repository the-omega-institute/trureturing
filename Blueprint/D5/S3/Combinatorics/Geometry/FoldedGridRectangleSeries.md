# Rectangles in an alternately folded grid

## Abstract

The actual endpoint rectangle counts satisfy both of Barker's generating-function and recurrence conjectures.

OEIS A096222 counts rectangular placements in the array whose sides are powers of two with exponents floor(n/2) and ceiling(n/2). Natural division Nat.div is floor division, so the second exponent is Nat.div(n+1,2). Rectangles at different positions are distinct. All natural indices, including zero, are retained.

**Definition 1.1 (Literal endpoint count).**

$$\forall n \in \operatorname{Nat},\; \operatorname{a}\left(n\right) = (let r:\operatorname{Nat}=2^{\operatorname{Nat}.\operatorname{div}\left(n, 2\right)}; (let s:\operatorname{Nat}=2^{\operatorname{Nat}.\operatorname{div}\left(n + 1, 2\right)}; \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{product}\left(\operatorname{Finset}.\operatorname{filter}\left((\lambda p:\operatorname{Nat} \times \operatorname{Nat} \mapsto p.1 < p.2), \operatorname{Finset}.\operatorname{product}\left(\operatorname{Finset}.\operatorname{range}\left(r + 1\right), \operatorname{Finset}.\operatorname{range}\left(r + 1\right)\right)\right), \operatorname{Finset}.\operatorname{filter}\left((\lambda p:\operatorname{Nat} \times \operatorname{Nat} \mapsto p.1 < p.2), \operatorname{Finset}.\operatorname{product}\left(\operatorname{Finset}.\operatorname{range}\left(s + 1\right), \operatorname{Finset}.\operatorname{range}\left(s + 1\right)\right)\right)\right)\right)))$$

*Formalization.* `D5/S3/Combinatorics/Geometry/FoldedGridRectangleSeries.a` (`✓ std3`).

*Citation.* Colin Barker; Bill Liebeskind (2020). *OEIS A096222: rectangles in an alternately folded grid*. URL: <https://oeis.org/A096222/internal?rev=13>.

*Commentary.*

Each filtered product chooses two natural grid-line indices in increasing order, from zero through the side length inclusive. The outer product chooses the horizontal and vertical intervals independently. Thus its elements are exactly ((x0,x1),(y0,y1)) with x0<x1<=r and y0<y1<=s. Its cardinality is the number of placements. The source says: In this sequence we count the rectangles in an a X b array of squares, where a=2^floor(n/2) and b=2^ceiling(n/2).

**Definition 1.2 (Formal generating series).**

$$(A:\operatorname{PowerSeries}\left(\operatorname{Rat}\right)) = \operatorname{PowerSeries}.\operatorname{mk}\left((\lambda n:\operatorname{Nat} \mapsto (\operatorname{a}\left(n\right):\operatorname{Rat}))\right)$$

*Formalization.* `D5/S3/Combinatorics/Geometry/FoldedGridRectangleSeries.A` (`✓ std3`).

*Citation.* Colin Barker; Bill Liebeskind (2020). *OEIS A096222: rectangles in an alternately folded grid*. URL: <https://oeis.org/A096222/internal?rev=13>.

*Commentary.*

PowerSeries.mk assigns coefficient a(n), cast to the rationals, at every natural n. This is a formal series over the rationals; no analytic convergence is required.

**Definition 1.3 (The complete joint assertion).**

$$claim \Leftrightarrow ((A = (1 - 3 \cdot \operatorname{PowerSeries}.\operatorname{X} - 9 \cdot \operatorname{PowerSeries}.\operatorname{X}^{2} + 24 \cdot \operatorname{PowerSeries}.\operatorname{X}^{3}) \cdot (\left(1 - 2 \cdot \operatorname{PowerSeries}.\operatorname{X}\right) \cdot \left(1 - 4 \cdot \operatorname{PowerSeries}.\operatorname{X}\right) \cdot \left(1 - 8 \cdot \operatorname{PowerSeries}.\operatorname{X}^{2}\right))^{-1}) \land (\forall n \in \operatorname{Nat},\; 4 \le n \Rightarrow (\operatorname{a}\left(n\right):\operatorname{Int}) = 6 \cdot (\operatorname{a}\left(n - 1\right):\operatorname{Int}) - 48 \cdot (\operatorname{a}\left(n - 3\right):\operatorname{Int}) + 64 \cdot (\operatorname{a}\left(n - 4\right):\operatorname{Int})))$$

*Formalization.* `D5/S3/Combinatorics/Geometry/FoldedGridRectangleSeries.claim` (`✓ std3`).

*Citation.* Colin Barker; Bill Liebeskind (2020). *OEIS A096222: rectangles in an alternately folded grid*. URL: <https://oeis.org/A096222/internal?rev=13>.

*Commentary.*

Barker's complete Start/End block asserts both the displayed generating function and the integer recurrence for n>3. The latter is precisely 4<=n on natural indices. Both conjuncts concern the same endpoint count. Integer casts precede the signed subtraction.

**Theorem 1.4 (Both identities hold).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/FoldedGridRectangleSeries.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Colin Barker; Bill Liebeskind (2020). *OEIS A096222: rectangles in an alternately folded grid*. URL: <https://oeis.org/A096222/internal?rev=13>.

*Commentary.*

Finset.card_product_filter_lt counts each ordered endpoint pair by a binomial coefficient. Nat.cast_choose_two gives the source's product of triangular numbers. Splitting the half exponents into their two parity cases proves the recurrence by polynomial normalization. Multiplication of A by the denominator gives numerator coefficients 1,-3,-9,24 at indices zero through three and zero thereafter, using that recurrence. The denominator has constant coefficient one and is therefore a unit in PowerSeries Rat; PowerSeries.eq_mul_inv_iff_mul_eq gives the formal quotient. In particular a(0)=1, a(1)=3, a(2)=9 and a(3)=30. The count formula, the conjectural quotient and recurrence, and their existing implementations are attributed in the source note.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/FoldedGridRectangleSeries.A`
- Truth anchor: `D5/S3/Combinatorics/Geometry/FoldedGridRectangleSeries.a`
- Truth anchor: `D5/S3/Combinatorics/Geometry/FoldedGridRectangleSeries.claim`
- Truth anchor: `D5/S3/Combinatorics/Geometry/FoldedGridRectangleSeries.result`
