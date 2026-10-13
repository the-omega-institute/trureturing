# Native Alternating Switching Polygons

## Abstract

The literal native T and E switching words close, and their actual prefix traces have no repeated vertex before return.

Configurations are actual permutations of Fin(m+1), and right multiplication acts on positions. The reversals a, b and c have lengths m+1, m and m-1. Put B=bc. The halfword is the list [a,c] followed by m-2 copies of [b,c], flattened. The T word repeats this halfword twice; the complete E word consists of m copies of [b,c]. All repetition here preserves the literal generator list. The trace is scanl of right multiplication, so it records every actual prefix product.

**Theorem 1.1 (The Exact Halfword Endpoint).**

$$\forall m \in \mathrm{Nat},\; 3 \le m \Rightarrow \mathrm{prod}\left(\mathrm{tHalfWord}\left(m\right)\right) = \mathrm{swap}\left(0, \mathrm{last}\left(m\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeSwitches.native_t_halfword_swap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m at least three, the halfword product is precisely the swap of positions zero and m. The proof computes every power of bc on each native position, and then applies a and c. It does not assume an endpoint matching or a finite enumeration.

**Theorem 1.2 (The Complete T Polygon Is Simple).**

$$\forall m \in \mathrm{Nat},\; 3 \le m \Rightarrow \left(\mathrm{prod}\left(\mathrm{tWord}\left(m\right)\right) = 1 \land \mathrm{Nodup}\left(\mathrm{dropLast}\left(\mathrm{scanl}\left(\mathrm{rightMultiply}, 1, \mathrm{tWord}\left(m\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeSwitches.native_t_simple_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The T product is identity and its prefix trace with the final return removed has no repeats. Writing tau for the endpoint swap, the trace before return is [1,a], the paired interior ports, [tau,tau*a], and the tau-left-translates of the same interior ports. The last-label-zero group has native coordinates (m-2,false), (m-1,true), and both orientations at all indices below m-2. The existing coordinateEquiv proves they are distinct. Left multiplication by tau preserves distinctness and moves their last label to m, which separates the two groups.

**Theorem 1.3 (Every Complete E Supplier Is Simple).**

$$\forall m \in \mathrm{Nat},\; 3 \le m \Rightarrow \left(\forall z \in \mathrm{Configuration}\left(m\right),\; \mathrm{prod}\left(\mathrm{eWord}\left(m\right)\right) = 1 \land \left(\mathrm{scanl}\left(\mathrm{rightMultiply}, z, \mathrm{eWord}\left(m\right)\right) = \mathrm{append}\left(\mathrm{flatten}\left(\mathrm{ofFn}\left(\mathrm{pairAtGap}\left(z, m\right)\right)\right), \mathrm{singleton}\left(z\right)\right) \land \mathrm{Nodup}\left(\mathrm{dropLast}\left(\mathrm{scanl}\left(\mathrm{rightMultiply}, z, \mathrm{eWord}\left(m\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeSwitches.native_e_simple_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every starting configuration z, the complete E word has product identity. Its actual trace is the ordered flattened list [z*B^j,z*B^j*b], for j in Fin(m), followed by z. Each pair has the two different native reflection coordinates at one gap; different gaps have different coordinates. The existing coordinateEquiv therefore proves no repeat before the return.

These results establish actual native switching polygons. They do not establish that a toggled factor is connected, that each cut belongs to a different complete native circle, or that the three-generator Cayley graph has a Hamilton cycle. Those support and splicing obligations must be proved separately.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeSwitches.native_e_simple_trace`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeSwitches.native_t_halfword_swap`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeSwitches.native_t_simple_trace`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversalZeroStarComplement](../PrefixReversalZeroStarComplement.md)
