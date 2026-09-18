# Exact Consecutive Cyclic-Stack Fibres

## Abstract

The consecutive cyclic [123] stack has the exact even and odd fibres conjectured by Zhan and Bie.

The stack is top-first. For each incoming value, it repeatedly pops the top entry exactly when the incoming value and the top two stack entries form one of the consecutive patterns 123, 231, or 312, then pushes the incoming value. The residual stack is flushed top-first. This literal convention maps 3124 to 4213, as in Figure 3 of the source.

**Theorem 1.1 (The full even and odd fibres).**

$$\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(length\left(fibre\left(2 \cdot m\right)\right) = 1 \land length\left(fibre\left(2 \cdot m + 1\right)\right) = m + 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/CyclicStackPreimages.zhan_bie_conjectures_3_4` (`✓ std3`). ∎

*Citation.* Alex Zhan and Stella Bie (2026). *Cyclic-Pattern-Avoiding Stacks*. URL: <https://math.colgate.edu/~integers/aa15/aa15.pdf>.

*Commentary.*

For m at least two, fibre(n) is the complete list of permutations of 1 through n whose output is (1,...,floor(n/2),n,...,floor(n/2)+1). The two conjuncts therefore cover every n at least four: the even fibre has one element, and the odd fibre has m+1 elements, equal to ceiling(n/2). The proof classifies every successful input rather than only constructing the displayed number of witnesses.

## References

- Truth anchor: `D5/S1/Words/Patterns/CyclicStackPreimages.zhan_bie_conjectures_3_4`
