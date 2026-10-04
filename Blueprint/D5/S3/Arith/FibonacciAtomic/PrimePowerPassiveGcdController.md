# Prime-Power Passive Gcd Acquisition

## Abstract

One finite deterministic tree uses paid positive-time answers from each original source to determine its complete gcd future.

**Definition 1.1 (The original-source channel).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/PrimePowerPassiveGcdController.read`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/PrimePowerPassiveGcdController.read` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural p,e, positive time q and any natural pair v, read(p,e,q,v) is GlobalGcdSampling.actualGcd(p^e,q.val,v). A history records each selected positive time with its actual natural answer.

**Definition 1.2 (Actual children with an omitted final test).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/PrimePowerPassiveGcdController.children`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/PrimePowerPassiveGcdController.children` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural threshold, rank and phase, a continuation next, and natural n,j, children tests time phase+j*rank+1 when n is positive. A threshold-divisible actual reply selects next(phase+j*rank); otherwise the next child is tested. When n is zero it selects next(phase+j*rank) without recording a reply.

**Definition 1.3 (A surviving parent phase).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/PrimePowerPassiveGcdController.continuation`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/PrimePowerPassiveGcdController.continuation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural p,content,fuel,d,phase, zero fuel stops. At positive fuel, a stagnant rank lift queries phase+1 and continues at that same phase exactly when the actual answer is divisible by p^(content+d+1). A miss stops. A growing lift tests p-1 children of rank zeroRank(p^d); each selected representative continues with precision d+1 and one less fuel. Repeated times are queried again and counted again.

**Definition 1.4 (A paid first-threshold scan).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/PrimePowerPassiveGcdController.firstLayer`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/PrimePowerPassiveGcdController.firstLayer` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a natural threshold, continuation next, and natural n,phase, zero n stops. Otherwise time phase+1 is queried. A divisible actual reply selects next(phase); a miss decreases n and advances phase.

**Definition 1.5 (Paid content and phase initialization).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/PrimePowerPassiveGcdController.protocol`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/PrimePowerPassiveGcdController.protocol` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural p,e the tree first queries times 1 and 2. The gcd of the two answers is the content label. A label equal to p^e stops. A label p^c with c<e scans times 1 through zeroRank(p), then continues from its first threshold hit with e-c-1 remaining lifts. Every other label stops. These choices depend on p,e and the actual history alone.

**Theorem 1.6 (One bounded tree determines the entire positive future).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/PrimePowerPassiveGcdController.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/PrimePowerPassiveGcdController.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural prime p and every natural e>=1, there exists one tree T over positive natural times with natural answers. For every natural pair v, the length of runPassiveProtocol read T v is at most zeroRank(p)+(e-1)*(p-1)+2. For every two natural pairs v,w, equality of their complete actual transcripts implies actualGcd(p^e,k,v)=actualGcd(p^e,k,w) for every positive natural k. The same tree is used for all sources, including the zero pair, saturated content and all exceptional or stagnant rank lifts. The bound counts queries and makes no optimality or maximum-index claim.

The first two paid answers recover capped content through the consecutive quantity gcd invariant. Division by that content occurs only in the proof. The normalized pair is primitive, while every channel continues to read the original source. The first-layer scan either finds a parent hit or certifies that no higher threshold can occur.

Induction on the remaining lifts proves the count and history-fiber future agreement jointly. At a growth lift the primitive parent has one threshold child, so all tested misses imply membership of the omitted child. This inference supplies only membership. At a stagnant lift the current representative is actually queried; a miss extinguishes the threshold globally. Each lift costs at most p-1 actual queries, including repeats. At termination agreement at all remaining prime-power thresholds gives equality of every actual future gcd.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/PrimePowerPassiveGcdController.children`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/PrimePowerPassiveGcdController.continuation`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/PrimePowerPassiveGcdController.firstLayer`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/PrimePowerPassiveGcdController.protocol`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/PrimePowerPassiveGcdController.read`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/PrimePowerPassiveGcdController.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling](GlobalGcdSampling.md)
- Dependency: [D5/S3/ConceptDynamics/Experiment/PassiveAdaptiveTranscriptUpperBound](../../ConceptDynamics/Experiment/PassiveAdaptiveTranscriptUpperBound.md)
