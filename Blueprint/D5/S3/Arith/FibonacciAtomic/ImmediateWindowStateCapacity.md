# Exact Immediate Fibonacci Window State Capacity

## Abstract

The complete high-to-low five-window task has exact minimal reachable modular state capacity.

Fix a natural modulus m at least two. Window bits are printed low to high, but windows arrive high to low. The unit bit is fixed at zero. Empty words and high-end null padding are legal. Every finite prefix immediately produces a residue; an illegal prefix produces a distinct absorbing error label. There is no End symbol and no requirement that the highest window be nonzero.

**Definition 1.1 (The three-bit Fibonacci clock).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ImmediateWindowStateCapacity.clock`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ImmediateWindowStateCapacity.clock` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

S(x)=M^3 x, where M(a,b)=(b,a+b). Thus S(a,b)=(a+2b,2a+3b), and the quantity is q(a,b)=2a+3b.

**Definition 1.2 (Window contributions).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ImmediateWindowStateCapacity.displacement`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ImmediateWindowStateCapacity.displacement` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The windows null, [2], [3], [25], [5] have printed bits 000, 100, 010, 101, 001 and displacements (0,0), (1,0), (0,1), (2,1), (1,1), respectively, in ZMod(m)^2.

**Definition 1.3 (Legal affine updates and absorbing errors).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ImmediateWindowStateCapacity.rawTransition`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ImmediateWindowStateCapacity.rawTransition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A live state is (s,x). The seam s is the low bit of the previously read higher window. Reject when s and the next window's high bit are both one; otherwise update x to Sx+d and the seam to the new window's low bit. Error remains error under every window.

**Definition 1.4 (Immediate residue or error).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ImmediateWindowStateCapacity.rawOutput`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ImmediateWindowStateCapacity.rawOutput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A live state outputs qx modulo m. The error state outputs none, distinct from every some(r) for r in ZMod(m).

**Definition 1.5 (The initialized complete reader).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ImmediateWindowStateCapacity.rawMachine`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ImmediateWindowStateCapacity.rawMachine` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The start state is seam zero and composition (0,0); every input letter uses rawTransition and every reached state is observed by rawOutput.

**Definition 1.6 (The finite-word output task).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ImmediateWindowStateCapacity.task`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ImmediateWindowStateCapacity.task` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

T_m(w) is the output of rawMachine(m) after reading the entire finite word w from left to right. Correctness for all words includes correctness at every prefix, at the empty word and after any error.

**Definition 1.7 (The two sufficient quantity observations).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ImmediateWindowStateCapacity.windowObserve`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ImmediateWindowStateCapacity.windowObserve` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

O_m(a,b)=(qx,qSx)=(2a+3b,8a+13b). The kernel is exactly the pairs (a,0) with 2a=0.

**Definition 1.8 (The actual observation image).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ImmediateWindowStateCapacity.Observation`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ImmediateWindowStateCapacity.Observation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

I_m is the range of O_m on ZMod(m)^2. It has m^2/gcd(m,2) elements. For even m it is a proper subset of ZMod(m)^2, so independent arbitrary readout pairs are not states.

**Definition 1.9 (The complete behavior states).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ImmediateWindowStateCapacity.SummaryState`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ImmediateWindowStateCapacity.SummaryState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Q_m consists of one error state and the pairs (s,z) with s in {0,1} and z in I_m.

**Definition 1.10 (A reader on the actual image).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ImmediateWindowStateCapacity.summaryMachine`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ImmediateWindowStateCapacity.summaryMachine` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The start state reduces the raw start. To update a live image state, choose a composition representing z, apply the raw transition, and reduce the result. The output is the first coordinate of z, or error. Equality of the two observations is preserved by every legal affine update, so the choice of representative does not affect the result.

**Definition 1.11 (Exact state count).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ImmediateWindowStateCapacity.capacity`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ImmediateWindowStateCapacity.capacity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

N(m)=2m^2/gcd(m,2)+1, with natural-number division. The gcd divides m^2, so this is an integer; N(2)=5.

**Theorem 1.12 (Exact upper and lower bounds).**

$$\forall m, ((m \in \operatorname{Nats}\left(\right)) \land \\(2 \leq m)) \implies ((\operatorname{FiniteState}\left(\operatorname{Q}\left(m\right)\right)) \land \\(\operatorname{card}\left(\operatorname{Q}\left(m\right)\right) = \operatorname{N}\left(m\right)) \land \\(\exists M, (\operatorname{Correct}\left(M, \operatorname{T}\left(m\right)\right)) \land \\(\forall x, (x \in \operatorname{Q}\left(m\right)) \implies (\exists w, \operatorname{eval}\left(M, w\right) = x))) \land \\(\forall S, (\operatorname{FiniteState}\left(S\right)) \implies (\forall M, (\operatorname{Correct}\left(M, \operatorname{T}\left(m\right)\right)) \implies (\operatorname{N}\left(m\right) \leq \operatorname{card}\left(S\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ImmediateWindowStateCapacity.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the formula, card denotes cardinality, FiniteState(S) means S is a finite state type, M ranges over deterministic output automata on the five windows with outputs Option(ZMod(m)), Correct(M,T_m) means equality of outputs on every finite word, and eval(M,w) is the state reached from the designated start. In the upper clause M has states Q_m; in the lower clause M has states S. The task is the same in both bounds.

On seam zero, null, [3] and [5] are affine permutations. Since the residue set is finite, inverse permutations are positive repetitions of the same legal window. Combining these words realizes translations by (0,1) and (1,0), hence every composition on seam zero. Appending [2] reaches every composition on seam one. The word [2][5] reaches error.

The observation kernel has gcd(m,2) elements by the cyclic-group two-torsion count. Its fibers give m^2/gcd(m,2) image states at each seam. Word induction proves that the image machine implements T_m everywhere. Every one of its states is reachable.

The empty suffix distinguishes different present outputs and error from live states. A null suffix distinguishes different second observations. A [5] suffix distinguishes the two seams by legality versus error. Reachable representatives and these common suffixes form a distinguishing family, forcing every correct machine to have at least N(m) states. The image machine attains that bound.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ImmediateWindowStateCapacity.Observation`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ImmediateWindowStateCapacity.SummaryState`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ImmediateWindowStateCapacity.capacity`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ImmediateWindowStateCapacity.clock`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ImmediateWindowStateCapacity.displacement`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ImmediateWindowStateCapacity.rawMachine`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ImmediateWindowStateCapacity.rawOutput`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ImmediateWindowStateCapacity.rawTransition`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ImmediateWindowStateCapacity.result`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ImmediateWindowStateCapacity.summaryMachine`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ImmediateWindowStateCapacity.task`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ImmediateWindowStateCapacity.windowObserve`
- Dependency: [D5/S0/Automata/DFAOStateLowerBound](../../../S0/Automata/DFAOStateLowerBound.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/GraftAffineClosure](GraftAffineClosure.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/LiteralWindowEnd](LiteralWindowEnd.md)
