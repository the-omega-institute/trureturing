# Positive Fibonacci Graft Words

## Abstract

Nonnegative Fibonacci coefficients give short forward graft words.

**Definition 1.1 (A positive representative).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/PositiveGraftShortWords.offset`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/PositiveGraftShortWords.offset` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

offset(H,c) is zero for c=0, H+1 for c=1, and c otherwise.

**Definition 1.2 (The common step horizon).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/PositiveGraftShortWords.horizon`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/PositiveGraftShortWords.horizon` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

horizon(H) is the least k>=1 with H<=F(k+4).

**Definition 1.3 (The graft budget).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/PositiveGraftShortWords.graftBound`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/PositiveGraftShortWords.graftBound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

graftBound(K)=1+(K+2)/2, using natural-number division.

**Definition 1.4 (Eliminating the auxiliary unit weight).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/PositiveGraftShortWords.graftCoefficients`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/PositiveGraftShortWords.graftCoefficients` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For occupied indices s, write epsilon(i)=1 if i belongs to s and zero otherwise. The coefficients are d(0)=epsilon(3)+1-epsilon(2), d(1)=epsilon(4)+epsilon(2), and d(j)=epsilon(j+3) for j>=2.

**Definition 1.5 (A chronological block word).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/PositiveGraftShortWords.blockWord`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/PositiveGraftShortWords.blockWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

blockWord(d,0) consists of d(0) true letters. blockWord(d,k+1) prepends d(k+1) true letters and one false letter to blockWord(d,k). True grafts (1,0); false applies the Fibonacci step.

**Theorem 1.6 (Positive coefficients and exact common-direction words).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/PositiveGraftShortWords.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/PositiveGraftShortWords.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural modulus H>1, K=horizon(H) is the least positive index with H<=F(K+4). Set gamma=graftBound(K)=1+ceil((K+1)/2). For every natural c<H there is a sequence d of nonnegative integers. When c=0, every coefficient is zero. Otherwise d is graftCoefficients of the occupied indices in the canonical representation of offset(H,c)-2. Coefficients above K vanish, d(0),d(1)<=2, and d(j)<=1 for every j>=2. The sum of d(j)F(j+3), for 0<=j<=K, equals offset(H,c). The sum of the coefficients is at most gamma.

For both k=K and k=K+1, the same coefficients define the chronological word G^d(k),R,G^d(k-1),R,...,R,G^d(0). It has exactly k false letters R and at most gamma true letters G. Each repetition denotes that many individual letters. For every actual initial state v in Nat^2, run((1,0),blockWord(d,k),v) equals step^k(v) plus the sum, for 0<=j<=k, of d(j) times atomicBlock(j)=step^j(1,0). Its quantity equals quantity(step^k(v))+offset(H,c), and its terminal readout is gcd(quantity(step^k(v))+c,H).

Canonical occupied indices lie between two and K+3 and differ by at least two. Reserving one weight-two graft replaces the auxiliary weight one by nonnegative coefficients at weights two and three. The weighted sum increases by exactly two, while the graft count becomes one plus the number of occupied indices at least three. Pairing these K+1 positions bounds that count by ceil((K+1)/2): the map i to floor((i-3)/2) is injective on the nonadjacent support. Descending block induction then puts each graft through exactly j subsequent steps. The quantity of atomicBlock(j) is F(j+3), giving the exact scalar equality. The representative H+1 for c=1 gives the same gcd as one. Every prefix acts within Nat^2, including the zero initial state and zero offset.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/PositiveGraftShortWords.blockWord`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/PositiveGraftShortWords.graftBound`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/PositiveGraftShortWords.graftCoefficients`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/PositiveGraftShortWords.horizon`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/PositiveGraftShortWords.offset`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/PositiveGraftShortWords.result`
- Dependency: [D5/S0/Conventions/WDigits](../../../S0/Conventions/WDigits.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/GraftAffineClosure](GraftAffineClosure.md)
