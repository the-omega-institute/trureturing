# Constructive Zeckendorf Future Equivalence

## Abstract

Actual legal continuations determine the unit-scaling quotient of a Fibonacci residue state.

Words are read least-significant first, with no adjacent true bits. Arbitrary high zero padding and the empty word are allowed. The modular theorem uses ZMod M for M at least two, including composite moduli. The two weight rows have explicit Bezout certificates, as actual consecutive Fibonacci rows do.

**Definition 1.1 (Consecutive-weight clock).**

$$\forall z \in \operatorname{Prod}\left(R, R\right), \operatorname{And}\left(\operatorname{advance}\left(0, z\right) = z, \forall n \in \mathbb{N}, \operatorname{advance}\left(n + 1, z\right) = \operatorname{advance}\left(n, \operatorname{pair}\left(\operatorname{snd}\left(z\right), \operatorname{fst}\left(z\right) + \operatorname{snd}\left(z\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/ZeckendorfFutureKernel.advance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

advance 0 is the identity and advance (n+1) at (u,v) is advance n at (v,u+v). This definition requires only addition in its coefficient type.

**Definition 1.2 (Actual weighted value of the remaining word).**

$$\forall u \in R, \forall v \in R, \operatorname{And}\left(\operatorname{value}\left(u, v, \operatorname{nil}\left(\right)\right) = 0, \forall b \in \operatorname{Bool}\left(\right), \forall w \in \operatorname{List}\left(\operatorname{Bool}\left(\right)\right), \operatorname{value}\left(u, v, \operatorname{cons}\left(b, w\right)\right) = \operatorname{ite}\left(b, u, 0\right) + \operatorname{value}\left(v, u + v, w\right)\right)$$

*Formalization.* `D5/S3/Arith/ZeckendorfFutureKernel.value` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The empty word has value zero. A first bit b contributes u when true and zero otherwise, and the remaining word uses weights (v,u+v). Starting at (F_2,F_3) gives the ordinary least-significant-first Fibonacci value, reduced in the coefficient ring.

**Definition 1.3 (Boundary-aware admissibility).**

$$\forall previous \in \operatorname{Bool}\left(\right), \operatorname{And}\left(\operatorname{legal}\left(previous, \operatorname{nil}\left(\right)\right), \forall b \in \operatorname{Bool}\left(\right), \forall w \in \operatorname{List}\left(\operatorname{Bool}\left(\right)\right), \operatorname{Iff}\left(\operatorname{legal}\left(previous, \operatorname{cons}\left(b, w\right)\right), \operatorname{And}\left(\operatorname{Not}\left(\operatorname{And}\left(previous = \operatorname{true}\left(\right), b = \operatorname{true}\left(\right)\right)\right), \operatorname{legal}\left(b, w\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/ZeckendorfFutureKernel.legal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The incoming previous bit is part of the state. An empty continuation is legal; a nonempty word is legal exactly when its first bit does not form eleven with the incoming bit and its tail is legal with that first bit as the new boundary.

**Definition 1.4 (The complete divisibility future).**

$$\forall previous \in \operatorname{Bool}\left(\right), \forall r \in \operatorname{ZMod}\left(M\right), \forall u \in \operatorname{ZMod}\left(M\right), \forall v \in \operatorname{ZMod}\left(M\right), \forall rp \in \operatorname{ZMod}\left(M\right), \forall up \in \operatorname{ZMod}\left(M\right), \forall vp \in \operatorname{ZMod}\left(M\right), \operatorname{Iff}\left(\operatorname{sameFuture}\left(previous, r, u, v, rp, up, vp\right), \forall w \in \operatorname{List}\left(\operatorname{Bool}\left(\right)\right), \operatorname{Iff}\left(\operatorname{And}\left(\operatorname{legal}\left(previous, w\right), r + \operatorname{value}\left(u, v, w\right) = 0\right), \operatorname{And}\left(\operatorname{legal}\left(previous, w\right), rp + \operatorname{value}\left(up, vp, w\right) = 0\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/ZeckendorfFutureKernel.sameFuture` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a common incoming bit, two triples (r,u,v) and (r',u',v') are equivalent when every finite continuation has the same legal-and-zero-residue acceptance answer. This is an entire future-language condition, not equality of a current output.

**Theorem 1.5 (Constructive saturation and exact fixed-boundary quotient).**

$$\forall M \in \mathbb{N}, \forall T \in \mathbb{N}, \forall previous \in \operatorname{Bool}\left(\right), \forall r \in \operatorname{ZMod}\left(M\right), \forall u \in \operatorname{ZMod}\left(M\right), \forall v \in \operatorname{ZMod}\left(M\right), \forall rp \in \operatorname{ZMod}\left(M\right), \forall up \in \operatorname{ZMod}\left(M\right), \forall vp \in \operatorname{ZMod}\left(M\right), \forall e \in \operatorname{ZMod}\left(M\right), \forall f \in \operatorname{ZMod}\left(M\right), \forall ep \in \operatorname{ZMod}\left(M\right), \forall fp \in \operatorname{ZMod}\left(M\right), \operatorname{Implies}\left(\operatorname{And}\left(\operatorname{Le}\left(2, M\right), \operatorname{And}\left(\operatorname{Le}\left(3, T\right), \operatorname{And}\left(\operatorname{castToZMod}\left(M, \operatorname{NatFib}\left(T\right)\right) = 0, \operatorname{And}\left(\operatorname{castToZMod}\left(M, \operatorname{NatFib}\left(T + 1\right)\right) = 1, \operatorname{And}\left(e \cdot u + f \cdot v = 1, ep \cdot up + fp \cdot vp = 1\right)\right)\right)\right)\right), \operatorname{And}\left(\forall A \in \operatorname{ZMod}\left(M\right), \forall B \in \operatorname{ZMod}\left(M\right), \exists w \in \operatorname{List}\left(\operatorname{Bool}\left(\right)\right), \operatorname{And}\left(\forall b \in \operatorname{Bool}\left(\right), \operatorname{legal}\left(b, w\right), \forall x \in \operatorname{ZMod}\left(M\right), \forall y \in \operatorname{ZMod}\left(M\right), \operatorname{value}\left(x, y, w\right) = A \cdot x + B \cdot y\right), \operatorname{Iff}\left(\operatorname{sameFuture}\left(previous, r, u, v, rp, up, vp\right), \exists a \in \operatorname{ZMod}\left(M\right), \exists aInv \in \operatorname{ZMod}\left(M\right), \operatorname{And}\left(a \cdot aInv = 1, \operatorname{And}\left(rp = a \cdot r, \operatorname{And}\left(up = a \cdot u, vp = a \cdot v\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ZeckendorfFutureKernel.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For M at least two and T at least three, assume the literal Fibonacci return F_T=0,F_(T+1)=1 in ZMod M, and e*u+f*v=1 and e'*u'+f'*v'=1. First, every pair of coefficient residues A,B is realized by one actual word legal after either incoming bit, with value A*x+B*y for every initial weight row (x,y). Second, the full future equivalence holds exactly when a single unit scales all three residue coordinates.

The proof derives the full weight-clock return from the actual Fibonacci recurrence. Two guarded words of length 2T place their only one at position T or T+1, then return the clock. Concatenating their powers programs every coefficient pair while respecting admissibility. Three resulting affine zero tests construct the common scalar, and the second Bezout row constructs its inverse. Homogeneity of the original word evaluation proves the reverse implication.

The common incoming bit is explicit. The separate-boundary distinction, reachability, exact state count, probability-law lift and WSS rank-growth consequences are established separately in the existing Wieferich interface note. This theorem does not use an initial-depth-one hypothesis.

## References

- Truth anchor: `D5/S3/Arith/ZeckendorfFutureKernel.advance`
- Truth anchor: `D5/S3/Arith/ZeckendorfFutureKernel.legal`
- Truth anchor: `D5/S3/Arith/ZeckendorfFutureKernel.result`
- Truth anchor: `D5/S3/Arith/ZeckendorfFutureKernel.sameFuture`
- Truth anchor: `D5/S3/Arith/ZeckendorfFutureKernel.value`
