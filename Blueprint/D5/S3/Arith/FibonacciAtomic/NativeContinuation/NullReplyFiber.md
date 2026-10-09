# Natural Fibonacci Window Histories and the Null Reply Fiber

## Abstract

The complete natural source histories of the existing high-to-low reader determine the exact appended-null zero fiber.

Window is the existing five-letter alphabet. Its null, low, high, ends and middle letters have printed low-to-high bits 000, 100, 001, 101 and 010. The existing reader processes windows in the order of the list, rejects when the prior seam and the current high bit are both true, and otherwise replaces the seam by the current low bit. Its clock is three Fibonacci steps S(a,b)=(a+2b,2a+3b), and its quantity is q(a,b)=2a+3b. At modulus zero its coefficient carrier is the integers, with no reduction.

**Definition 1.1 (The complete high-to-low bit history).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/NullReplyFiber.highBits`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/NullReplyFiber.highBits` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

highBits(w) concatenates the reversal of each letter's existing bit list, without reversing the window list. Every window contributes three bits. Thus legal(s,highBits(w)) imposes the incoming high boundary s and every actual seam, while leaving the last seam free. The empty word, leading null windows and all-null words retain their original positions.

**Definition 1.2 (Natural window contributions).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/NullReplyFiber.bitComposition`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/NullReplyFiber.bitComposition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

bitComposition(b) is the pair (value(1,0,bits(b)),value(0,1,bits(b))) of the existing Fibonacci bit evaluations over the natural numbers. In the order null, low, high, ends, middle these pairs are (0,0), (1,0), (1,1), (2,1), (0,1). They are the natural contributions of the same letters, rather than contributions of another alphabet.

**Definition 1.3 (Guarded natural source histories).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/NullReplyFiber.NativeHistory`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/NullReplyFiber.NativeHistory` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

NativeHistory(s,c,w,t,d) is a relation, not an additional reader. An empty word has final seam s and composition c. For a word b followed by v, require that s and last(b) are not both true, then use NativeHistory(first(b),S(c)+bitComposition(b),v,t,d). The initial and final compositions are natural pairs. This retains each source letter and the actual seam at each prefix, with no leading-letter restriction or terminal test.

**Theorem 1.4 (Exact realization by the existing reader).**

$$\forall s: Bool, (\forall c: \mathbb{N} \times \mathbb{N}, (\forall w: \operatorname{List}\left(Window\right), (((\operatorname{R}\left(s, c, w\right) = none) \iff (\neg \operatorname{legal}\left(s, \operatorname{highBits}\left(w\right)\right))) \land (\forall t: Bool, (\forall x: \mathbb{Z} \times \mathbb{Z}, ((\operatorname{R}\left(s, c, w\right) = \operatorname{some}\left((t, x)\right)) \iff (\exists d: \mathbb{N} \times \mathbb{N}, ((\operatorname{NativeHistory}\left(s, c, w, t, d\right)) \land (x = \operatorname{residue}\left(0, d\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/NativeContinuation/NullReplyFiber.native_execution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

R(s,c,w) abbreviates the existing rawMachine(0).toDFA.evalFrom(some(s,residue(0,c)),w). The map residue(0,d) is the coordinatewise natural-to-integer cast. The formula includes both the error equivalence and the equivalence for every candidate successful seam and integer composition.

Word induction identifies the actual guard with bit legality. The natural bit contributions cast to the existing reader's five displacements, and three natural Fibonacci steps cast to its clock. A rejected prefix remains error for every remaining letter. A successful prefix therefore has natural coordinates following the displayed source recurrence; conversely each such source history realizes that same successful state. The assertion holds for every natural initial composition and either incoming seam.

**Theorem 1.5 (The exact zero fiber of actual null continuation).**

$$\forall w: \operatorname{List}\left(Window\right), ((\operatorname{task}\left(0, \operatorname{append}\left(w, [zero]\right)\right) = \operatorname{some}\left(0\right)) \iff (\forall b: Window, ((b \in w) \implies (b = zero))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/NativeContinuation/NullReplyFiber.null_reply_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

task(0,w) is the existing immediate output from seam false and composition (0,0). The appended letter is the existing zero window. Its guard is always legal on a live state, it sets the seam to false, and it performs the full clock before returning qS(c)=8a+13b on a natural composition c=(a,b). It leaves error absorbing.

The exact realization supplies natural coordinates for every successful input. The updated natural composition vanishes precisely when both the prior composition and the current window contribution vanish. Induction on the source history therefore forces every preceding letter to be null when the final composition is zero. Since 8a+13b is zero on the natural cone only at (0,0), the actual appended-null reply is zero precisely on all-null words. The equivalence ranges over every finite input word, including illegal words and the empty word; illegal words return none. On the complete legal words of any fixed length it identifies the zero-reply event with the single all-null source. It does not state a probability law or a spectral relation.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/NullReplyFiber.NativeHistory`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/NullReplyFiber.bitComposition`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/NullReplyFiber.highBits`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/NullReplyFiber.native_execution`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/NullReplyFiber.null_reply_zero_iff`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ImmediateWindowStateCapacity](../ImmediateWindowStateCapacity.md)
