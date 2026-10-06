# Two-Sided Cut Witnesses

## Abstract

Missing and extra observation cuts give opposite failures on actual Fibonacci sources.

For positive widths m at most M, q(M,n) is the initial M-digit window of the canonical Fibonacci expansion of n. The tuple sigma(m,S,n) contains the m-digit windows of n+t for the retained natural times t in S. K(m,S) is the union of the inclusive intervals [t+1,t+G(m)], where G(L)=F(L+2). All coordinates of a tuple come from the same natural source.

**Theorem 1.1 (Actual sources beyond every bound).**

$$\forall m,M,B \in \mathbb{N}, \forall S \subseteq \mathbb{N} \text{finite}, 1 \le m \le M \implies ((\exists k \in \operatorname{Icc}\left(1, \operatorname{G}\left(M\right)\right), \neg (k \in \operatorname{K}\left(m, S\right))) \implies (\exists a,b \in \mathbb{N}, B < a \land B < b \land \sigma_{m,S}(a) = \sigma_{m,S}(b) \land \operatorname{q}\left(M, a\right) \neq \operatorname{q}\left(M, b\right))) \land ((\exists k \in \operatorname{K}\left(m, S\right), \neg (k \in \operatorname{Icc}\left(1, \operatorname{G}\left(M\right)\right))) \implies (\exists a,b \in \mathbb{N}, B < a \land B < b \land \operatorname{q}\left(M, a\right) = \operatorname{q}\left(M, b\right) \land \sigma_{m,S}(a) \neq \sigma_{m,S}(b)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/SparseCutTwoSidedWitness.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The statement holds for every finite S, including the empty set, and every natural bound B. A missing target cut gives two sources above B with the same observation tuple and different target windows. An extra observation cut gives two sources above B with the same target window and different observation tuples.

At a missing cut, finitely many open coordinate arcs contain a common neighborhood. The target labels on its two sides differ. At an extra cut, one target arc contains a neighborhood, while a retained coordinate changes label between the two sides. Small open collars give both sides positive length, also at the circle seam. The golden rotation visits each side beyond B and avoids every endpoint. If several coordinates share an extra cut, a change in any one coordinate distinguishes the tuples.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SparseCutTwoSidedWitness.result`
- Dependency: [D5/S1/Digit/Infinite/SparseWindowMutualDetermination](../../../S1/Digit/Infinite/SparseWindowMutualDetermination.md)
