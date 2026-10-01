# Fibonacci Atomic Action State Capacity

## Abstract

A seam-preserving atomic action restores the complete modular state capacity.

Fix a natural modulus m at least two. The input alphabet consists of the five high-to-low Fibonacci windows together with one atomic action mu. The window transitions are the complete legal affine reader, including the absorbing error state. The atomic action applies one Fibonacci step to the composition and leaves the historical seam unchanged.

**Definition 1.1 (The extended alphabet).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/AtomicActionStateCapacity.Action`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/AtomicActionStateCapacity.Action` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An input is either a five-window symbol or the atomic action mu.

**Definition 1.2 (Window and atomic transitions).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/AtomicActionStateCapacity.atomicTransition`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/AtomicActionStateCapacity.atomicTransition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Window symbols use the raw affine transition. On a live state (s,x), mu sends it to (s,Mx), and mu preserves the error state.

**Definition 1.3 (The initialized extended reader).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/AtomicActionStateCapacity.atomicMachine`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/AtomicActionStateCapacity.atomicMachine` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The reader starts at seam zero and composition (0,0), and evaluates every finite extended word.

**Definition 1.4 (The extended finite-word task).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/AtomicActionStateCapacity.atomicTask`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/AtomicActionStateCapacity.atomicTask` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The task is the immediate output after every finite word over the five windows and mu.

**Definition 1.5 (Complete state count).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/AtomicActionStateCapacity.capacity`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/AtomicActionStateCapacity.capacity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

N(m)=2m^2+1, counting both seam values for every composition and one error state.

**Theorem 1.6 (Exact minimal capacity after adding mu).**

$$\forall m, ((m \in \operatorname{Nats}\left(\right)) \land \\(2 \leq m)) \implies ((\operatorname{FiniteState}\left(\operatorname{RawState}\left(m\right)\right)) \land \\(\operatorname{card}\left(\operatorname{RawState}\left(m\right)\right) = \operatorname{N}\left(m\right)) \land \\(\exists M, (\operatorname{Correct}\left(M, \operatorname{T}\left(m\right)\right)) \land \\(\forall q, (q \in \operatorname{RawState}\left(m\right)) \implies (\exists w, \operatorname{eval}\left(M, w\right) = q))) \land \\(\forall S, (\operatorname{FiniteState}\left(S\right)) \implies (\forall M, (\operatorname{Correct}\left(M, \operatorname{T}\left(m\right)\right)) \implies (\operatorname{N}\left(m\right) \leq \operatorname{card}\left(S\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/AtomicActionStateCapacity.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m at least two, the raw state type is finite and has exactly N(m) states. The initialized extended reader is correct on every finite word and every raw state is reachable.

The present quantity and the quantity after one mu action are the two linear forms (2,3) and (3,5). Their determinant is one, so they recover both composition coordinates over every ZMod(m). The empty continuation and one mu therefore distinguish any two live states with different compositions. A high window distinguishes the two seam values, and the empty word distinguishes the error state from every live state.

Reachable histories together with these common distinguishing continuations form a finite distinguishing family. The general output-automaton lower-bound theorem then forces every correct finite-state reader to have at least N(m) states, while the raw reader attains this bound.

Explanatory boundaries from the source: for odd moduli, the original window summary already recovers the composition; for even moduli, adding mu strictly refines the original quotient. Closure under the three-bit window clock does not establish closure under the atomic clock. These are explanations, not independent Lean clauses of result.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/AtomicActionStateCapacity.Action`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/AtomicActionStateCapacity.atomicMachine`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/AtomicActionStateCapacity.atomicTask`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/AtomicActionStateCapacity.atomicTransition`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/AtomicActionStateCapacity.capacity`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/AtomicActionStateCapacity.result`
- Dependency: [D5/S0/Automata/DFAOStateLowerBound](../../../S0/Automata/DFAOStateLowerBound.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/ImmediateWindowStateCapacity](ImmediateWindowStateCapacity.md)
