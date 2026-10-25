# Effective short positive probes

## Abstract

A public finite compiler implements every shifted terminal gcd in two consecutive Fibonacci directions using only short positive replacement and graft words.

The actual source is any natural pair v=(a,b), including (0,0). The original calls are R(a,b)=(b,a+b) and G(a,b)=(a+1,b). A Boolean word is chronological: true means R and false means G. Run(W,v) is TerminalGcdAcquisitionCost.runWord, not an independently assumed simulator. Quantity is q(a,b)=2a+3b. A terminal read returns gcd(q Run(W,v),H). A word contains no read instruction: its execution precedes one separately paid current read.

**Definition 1.1 (The original least direction).**

$$(\forall H \in \operatorname{Nat}\left(\right), \operatorname{K}\left(H\right) = \operatorname{min}\left(\operatorname{positiveFibDirections}\left(H\right)\right))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PositiveProbeCompiler.direction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

K(H)=direction(H) is the least k>=1 with H<=fib(k+4). The terminating natural-number search uses the unbounded Fibonacci sequence; it does not select a direction from the unknown source. The convention is fib(0)=0, fib(1)=1.

**Definition 1.2 (The graft allowance).**

$$(\forall H \in \operatorname{Nat}\left(\right), \operatorname{Gamma}\left(H\right) = 1+\operatorname{floorDiv}\left(\operatorname{K}\left(H\right)+2, 2\right))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PositiveProbeCompiler.graftBound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Gamma(H)=graftBound(H)=1+floor((K(H)+2)/2), equivalently 1+ceil((K(H)+1)/2). This counts individual original graft calls.

**Definition 1.3 (An executable shift representative).**

$$(\forall H \in \operatorname{Nat}\left(\right), (\forall c \in \operatorname{Nat}\left(\right), \operatorname{t}\left(H, c\right) = \operatorname{ite}\left(\operatorname{mod}\left(c, H\right) = 0, 0, \operatorname{ite}\left(\operatorname{mod}\left(c, H\right) = 1, H+1, \operatorname{mod}\left(c, H\right)\right)\right)))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PositiveProbeCompiler.positiveLift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let d=c mod H. The representative t(H,c) is zero when d=0, H+1 when d=1, and d otherwise. For H>1 a nonzero representative lies between 2 and H+1. In particular an offset of one never requests an unavailable unit-weight action.

**Definition 1.4 (A finite list of available weights).**

$$(\forall H \in \operatorname{Nat}\left(\right), (\forall c \in \operatorname{Nat}\left(\right), \operatorname{Z}\left(H, c\right) = \operatorname{ite}\left(\operatorname{mod}\left(c, H\right) = 0, \operatorname{nil}\left(\right), \operatorname{append}\left(\operatorname{filterNotTwo}\left(\operatorname{zeckendorf}\left((\operatorname{t}\left(H, c\right)-2)\right)\right), \operatorname{singleton}\left(\operatorname{ite}\left(\operatorname{containsTwo}\left(\operatorname{zeckendorf}\left((\operatorname{t}\left(H, c\right)-2)\right)\right), 4, 3\right)\right)\right)\right)))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PositiveProbeCompiler.weights` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Z(H,c)=weights(H,c) is empty when c mod H=0. Otherwise let z=Nat.zeckendorf(t(H,c)-2), the existing descending list of occupied Fibonacci indices. Remove index 2, then append index 4 if z contains 2, or index 3 otherwise. The filter removes the auxiliary weight fib(2)=1. The appended weight replaces the reserved 2 together with that auxiliary 1 by 3 when necessary. Repeated indices 3 or 4 are permitted: they mean repeated graft calls, not a larger primitive.

**Definition 1.5 (Chronological emission from descending weights).**

$$((\forall k \in \operatorname{Nat}\left(\right), \operatorname{E}\left(k, \operatorname{nil}\left(\right)\right) = \operatorname{repeatR}\left(k\right)) \land (\forall k \in \operatorname{Nat}\left(\right), (\forall i \in \operatorname{Nat}\left(\right), (\forall l \in \operatorname{ListNat}\left(\right), \operatorname{E}\left(k, \operatorname{cons}\left(i, l\right)\right) = \operatorname{append}\left(\operatorname{repeatR}\left((k-(i-3))\right), \operatorname{consG}\left(\operatorname{E}\left((i-3), l\right)\right)\right)))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PositiveProbeCompiler.emit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

E(k,l)=emit(k,l) treats k as the number of replacements still to emit. For an empty list it emits R repeated k times. For i::l it emits R repeated k-(i-3) times, then one G, then E(i-3,l). All subtractions in this total definition are truncated natural subtractions. On the lists used by the theorem, 3<=i<=k+3 and the indices descend, so the displayed gaps are the exact nonnegative numbers of intervening R calls.

**Definition 1.6 (The public compiler).**

$$(\forall H \in \operatorname{Nat}\left(\right), (\forall k \in \operatorname{Nat}\left(\right), (\forall c \in \operatorname{Nat}\left(\right), \operatorname{W}\left(H, k, c\right) = \operatorname{E}\left(k, \operatorname{Z}\left(H, c\right)\right))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PositiveProbeCompiler.compile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

W(H,k,c)=compile(H,k,c)=E(k,Z(H,c)). Its inputs are public natural numbers, and its output is an explicit finite Boolean list. It uses the computable Nat.find and Nat.zeckendorf constructions and structural list recursion. No classical choice of a test tree, source coordinate, entry residue, reset, inverse service or factorial-period word enters this definition.

**Theorem 1.7 (Both directions and every shifted terminal reply).**

$$(\forall H \in \operatorname{Nat}\left(\right), (1 < H) \implies ((1 \le \operatorname{K}\left(H\right) \land H \le \operatorname{fib}\left(\operatorname{K}\left(H\right)+4\right) \land (\forall j \in \operatorname{Nat}\left(\right), ((1 \le j \land H \le \operatorname{fib}\left(j+4\right))) \implies (\operatorname{K}\left(H\right) \le j)) \land (\forall k \in \operatorname{Nat}\left(\right), (\forall c \in \operatorname{Nat}\left(\right), ((k = \operatorname{K}\left(H\right) \lor k = \operatorname{K}\left(H\right)+1)) \implies ((\operatorname{descending}\left(\operatorname{Z}\left(H, c\right)\right) \land (\forall i \in \operatorname{Nat}\left(\right), (\operatorname{member}\left(i, \operatorname{Z}\left(H, c\right)\right)) \implies ((3 \le i \land i \le \operatorname{K}\left(H\right)+3))) \land \operatorname{sumFib}\left(\operatorname{Z}\left(H, c\right)\right) = \operatorname{t}\left(H, c\right) \land \operatorname{countR}\left(\operatorname{W}\left(H, k, c\right)\right) = k \land \operatorname{countG}\left(\operatorname{W}\left(H, k, c\right)\right) = \operatorname{length}\left(\operatorname{Z}\left(H, c\right)\right) \land \operatorname{countG}\left(\operatorname{W}\left(H, k, c\right)\right) \le \operatorname{Gamma}\left(H\right) \land (\forall v \in \operatorname{NatPair}\left(\right), (\operatorname{q}\left(\operatorname{Run}\left(\operatorname{W}\left(H, k, c\right), v\right)\right) = \operatorname{q}\left(\operatorname{iterateR}\left(k, v\right)\right)+\operatorname{t}\left(H, c\right) \land \operatorname{gcd}\left(\operatorname{q}\left(\operatorname{Run}\left(\operatorname{W}\left(H, k, c\right), v\right)\right), H\right) = \operatorname{gcd}\left(\operatorname{q}\left(\operatorname{iterateR}\left(k, v\right)\right)+c, H\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PositiveProbeCompiler.effective_short_compiler` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every H>1, K is exactly the original least positive direction. For either k=K or k=K+1, and every natural requested shift c, Z is descending, each index lies between 3 and K+3, and its Fibonacci sum is t(H,c). The emitted word has exactly k replacements and exactly length(Z) grafts, at most Gamma(H). Every actual natural pair satisfies the integer endpoint-quantity identity and the shifted terminal gcd identity displayed below. Thus all representatives of every residue shift are covered by the same public compiler.

The existing Zeckendorf theorem supplies the finite sum and nonadjacency. Since t-2<H<=fib(K+4), each occupied index is at most K+3. After removing index 2 the remaining indices range from 3 to K+3 with gaps at least two, hence their number is at most floor((K+2)/2). Appending one index gives the graft bound. When index 2 was present, index 3 was absent, so appending 4 preserves descending order. Otherwise appending 3 does. This also covers K=1, the empty representation and the offsets zero and one.

An emitted graft with index i has exactly i-3 replacements remaining after it. The existing original quantity law gives q R^(i-3)(1,0)=fib(i). Induction on the descending weight list proves the actual integer quantity identity and makes the replacement counts telescope to k. Reduction of t modulo H then gives the complete gcd reply. All prefixes are actual applications of R and G to natural pairs; zero is in the same domain. The direction K+1 adds an initial replacement while preserving every graft's remaining replacement count.

The compiler produces a word for a caller to execute serially on its retained source handle, consuming each fixed acknowledgement before the next call. Its correctness holds for every current integer entry, so a later acquisition scheduler can invoke it at any cut having the required residue. The separately paid current gcd port, exclusive source control, authentic binding and rights, service completion and sufficient finite backing remain premises of actual execution. This result supplies no hardware realization or source-service price.

The effective common-direction digit and CRT scheduler, its earned reply tape, positive closing trajectory, same-run totals, entry decoder and installed synchronized continuation are separate constructions. No bit-work, bit-space or total-resource optimum is asserted here. Local binary input handling, arithmetic, word storage and emission, acknowledgements, source services and backing must still be charged in the full acquisition contract.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PositiveProbeCompiler.compile`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PositiveProbeCompiler.direction`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PositiveProbeCompiler.effective_short_compiler`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PositiveProbeCompiler.emit`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PositiveProbeCompiler.graftBound`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PositiveProbeCompiler.positiveLift`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PositiveProbeCompiler.weights`
- Dependency: [D5/S1/Digit/GoldenZeckendorfLanguage](../../../../S1/Digit/GoldenZeckendorfLanguage.md)
- Dependency: [D5/S3/Analytic/GoldenEulerBetaZeckendorf](../../../Analytic/GoldenEulerBetaZeckendorf.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling](../GlobalGcdSampling.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/TerminalGcdAcquisitionCost](../TerminalGcdAcquisitionCost.md)
