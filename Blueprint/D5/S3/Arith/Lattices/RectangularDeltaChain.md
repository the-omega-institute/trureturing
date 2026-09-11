# Longest Integer Chains in a Rectangle

## Abstract

An integer progression in a finite rectangle has an attained maximum length.

Let P be a finite coordinate set, L a family of natural side lengths, and d an integer direction. A chain of n points from a has coordinates a(p) + j d(p) between zero and L(p) for every j in {0,...,n-1} and every p. Unless stated otherwise, assume explicitly that some coordinate of d is nonzero.

Write M for one plus the minimum of floor(L(p)/|d(p)|) over the nonzero coordinates. The corner c has c(p)=L(p) if d(p)<0 and c(p)=0 otherwise. Lengths count points, including the initial point; the empty chain has length zero.

**Theorem 1.1 (Each moving coordinate bounds the point count).**

$$\operatorname{Chain}(L,d,a,n) \land d_{p} \neq 0 \Rightarrow n \le 1+\lfloor \frac{L_{p}}{\Vert d_{p} \Vert} \rfloor$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/RectangularDeltaChain.chain_length_le_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Codex implementation worker (2026). *Maximum integer progression length in a rectangular window*. URL: <https://github.com/the-omega-institute/trureturing>.

*Commentary.*

For any chosen p with d(p) nonzero, the difference between the first and last points has magnitude (n-1)|d(p)| and cannot exceed L(p). The empty chain also satisfies the bound.

**Theorem 1.2 (The smallest coordinate quotient bounds every chain).**

$$\operatorname{Chain}(L,d,a,n) \Rightarrow n \le M$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/RectangularDeltaChain.chain_length_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Codex implementation worker (2026). *Maximum integer progression length in a rectangular window*. URL: <https://github.com/the-omega-institute/trureturing>.

*Commentary.*

Applying the coordinate bound to every moving coordinate and taking their finite minimum gives the common upper bound M.

**Theorem 1.3 (The sign-selected corner attains the bound).**

$$\operatorname{Chain}(L,d,c,M)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/RectangularDeltaChain.corner_chain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Codex implementation worker (2026). *Maximum integer progression length in a rectangular window*. URL: <https://github.com/the-omega-institute/trureturing>.

*Commentary.*

For j<M each displacement magnitude j|d(p)| is at most L(p). Positive coordinates increase from zero, negative coordinates decrease from L(p), and zero coordinates remain zero. Every one of these M points therefore lies in the rectangle.

**Theorem 1.4 (Exactly the lengths up to M occur).**

$$(\exists a, \operatorname{Chain}(L,d,a,n)) \iff n \le M$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/RectangularDeltaChain.exists_chain_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Codex implementation worker (2026). *Maximum integer progression length in a rectangular window*. URL: <https://github.com/the-omega-institute/trureturing>.

*Commentary.*

Every shorter length is obtained by taking an initial segment of the corner chain; the upper bound excludes all larger lengths.

**Theorem 1.5 (The greatest attainable point count).**

$$mmax = 1+\operatorname{min}_{d_{p} \neq 0} \lfloor \frac{L_{p}}{\Vert d_{p} \Vert} \rfloor$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/RectangularDeltaChain.longest_chain_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Codex implementation worker (2026). *Maximum integer progression length in a rectangular window*. URL: <https://github.com/the-omega-institute/trureturing>.

*Commentary.*

The theorem asserts that M is the greatest element of the set of attainable chain lengths: it belongs to that set and bounds every member. Attainment and the universal bound concern the same rectangle and direction.

**Theorem 1.6 (Zero direction admits every sequence length).**

$$(\forall p, d_{p} = 0) \Rightarrow \forall n, \operatorname{Chain}(L,d,0,n)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/RectangularDeltaChain.zero_direction_unbounded` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Codex implementation worker (2026). *Maximum integer progression length in a rectangular window*. URL: <https://github.com/the-omega-institute/trureturing>.

*Commentary.*

If every direction component is zero, the sequence based at the lower corner satisfies the window bounds for every natural length. These sequences repeat one point, which explains the explicit nonzero-coordinate hypothesis in the maximum-length formula.

## References

- Truth anchor: `D5/S3/Arith/Lattices/RectangularDeltaChain.chain_length_le`
- Truth anchor: `D5/S3/Arith/Lattices/RectangularDeltaChain.chain_length_le_coordinate`
- Truth anchor: `D5/S3/Arith/Lattices/RectangularDeltaChain.corner_chain`
- Truth anchor: `D5/S3/Arith/Lattices/RectangularDeltaChain.exists_chain_iff`
- Truth anchor: `D5/S3/Arith/Lattices/RectangularDeltaChain.longest_chain_length`
- Truth anchor: `D5/S3/Arith/Lattices/RectangularDeltaChain.zero_direction_unbounded`
