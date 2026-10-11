# Remote Vector Compensation

## Abstract

Every legal finite prefix and complete modular Fibonacci composition have a common finite realization with a nonzero remote tail.

L and B are arbitrary natural numbers, including zero. The word p is any legal low-to-high binary word of length L: no two adjacent letters are one. The modulus m is any positive natural number, including one, and r is any pair in ZMod(m) squared. LegalDigits is the space of infinite binary addresses without adjacent ones; finiteTail means that all sufficiently high bits are zero. P(L,b) is the existing low-prefix projection. The external unit position has digit zero and is not part of the address.

**Definition 1.1 (Actual source composition).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/RemoteVectorCompensation.sourceComposition`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/RemoteVectorCompensation.sourceComposition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

x(b) is the finite-support sum of atomicBlock(j)=M^j alpha over occupied positions j of b, where M(a,c)=(c,a+c) and alpha=(1,0). The coordinates are nonnegative integers, included in the integer lattice. For an eventually zero address this sum is finite. Its totalized value on an address that is not eventually zero is not interpreted as a source composition; the realization theorem requires finiteTail(b). rho(m,x) reduces both coordinates modulo m.

**Theorem 1.2 (Joint realization beyond any bound).**

$$\forall L, p \in \operatorname{X}\left(L\right), m > 0, r \in \operatorname{ZMod}\left(m\right)^{2}, B, \exists b \in LegalDigits, (\operatorname{finiteTail}\left(b\right)) \land (\operatorname{P}\left(L, b\right) = p) \land (\operatorname{rho}\left(m, \operatorname{x}\left(b\right)\right) = r) \land (\forall j, ((L \leq j) \land (\operatorname{bit}\left(b, j\right) = 1)) \implies B < j) \land (\exists j, (L \leq j) \land (B < j) \land (\operatorname{bit}\left(b, j\right) = 1))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/RemoteVectorCompensation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose a return period T at least three for the Fibonacci step modulo m and a sufficiently distant multiple N of T. Subtract the prefix composition from the target vector. If its two least nonnegative coordinates are a and c, place a+m ones at N+iT and then c ones at N+(a+m+j)T+1. The two groups contribute (a,0) and (0,c) modulo m; the additional m positions have zero modular contribution. Consecutive occupied positions within a group are T apart, and the transition between groups is T+1 apart. The gap after the prefix is at least two. Thus one eventually zero legal address realizes the entire vector, retains the prefix, and has at least one occupied position beyond B.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/RemoteVectorCompensation.result`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/RemoteVectorCompensation.sourceComposition`
- Dependency: [D5/S1/Digit/Infinite/ClosedObservationCommonTailWidthModel](../../../S1/Digit/Infinite/ClosedObservationCommonTailWidthModel.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/GraftAffineClosure](GraftAffineClosure.md)
