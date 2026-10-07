# Shared Triangular Slot Implementation

## Abstract

One-bit terminal pairs can be shared in every legal stationary triangular table.

**Definition 1.1 (Stationary legal actions).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.Table`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.Table` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each m, a table fixes one action at each aggregate state. At every 0 <= r < e <= m with e positive, the action satisfies the triangular legality conditions. The aggregate state and its successor are those of reduced triangular paths, including zero residual self-loops.

**Definition 1.2 (Original active slots).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.Slot`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.Slot` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A slot has coordinates (e,r,k) with 0 <= e <= m, 0 <= r < e and 0 <= k < r. The last condition excludes r=0. Thus these are exactly the triples 1 <= r < e <= m and 0 <= k < r.

**Definition 1.3 (Aggregate coordinates).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.aggregate`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.aggregate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The aggregate of (e,r,k) is (r,e).

**Definition 1.4 (Two immediate children).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.Immediate`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.Immediate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A slot is immediate precisely when e <= 2r and k < floor(e/2). In an odd layer e=2j+1, k=j is excluded.

**Definition 1.5 (Shared and singleton activities).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.SharedActive`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.SharedActive` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The shared active carrier is the disjoint union of P_k for k < floor(m/2) and one V_(r,e,k) for every non-immediate original slot. Terminals form a separate copy of Fin(m).

The color map is Sum.getRight?: activities have color none, and terminal i has color some(i). Thus terminal colors are distinct. The index i in Fin(m) denotes source label i+1.

**Definition 1.6 (Original root).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.root`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.root` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every m >= 2 the root is the active slot (1,m,0).

**Definition 1.7 (Length of the ordered output list).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.outputCount`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.outputCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For the one action the output count q is e; for zero(h) it is h. In particular h=0 gives an empty list.

**Definition 1.8 (Ordered labels).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.outputLabel`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.outputLabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At zero-based list position z, the one action outputs label index z, while zero(h) outputs e-h+z. These correspond to the one-based lists (1,...,e) and (e-h+1,...,e).

**Definition 1.9 (Original paid-bit transition).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.originalStep`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.originalStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At (r,e,k), read one bit u and set z=2k+u. If z<q, return the label at ordered list position z. Otherwise continue at (r',e',z-q), using the prescribed aggregate successor. This branch satisfies z-q<r', so zero residual states are never active slots. Terminals have absorbing auxiliary transitions and do not consume further paid bits.

**Definition 1.10 (Immediate-pair projection).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.projection`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.projection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every immediate slot of index k projects to P_k. Every other slot projects to its own singleton V_(r,e,k). Each terminal projects to the terminal with the same label.

**Definition 1.11 (Fixed ordered shared transitions).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.sharedStep`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.sharedStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two children of P_k are terminal indices 2k and 2k+1. A singleton uses the projection of its original successor. Terminal transitions remain absorbing.

**Definition 1.12 (Prefixes of a stream).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.trace`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.trace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a transition delta, start s, stream omega and natural n, trace is the state after the first n bits, in their order.

**Definition 1.13 (First stopping response).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.FirstStop`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.FirstStop` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

FirstStop(delta,c,s,omega,i,n) means the state after n bits has terminal color some(i), and every shorter prefix has activity color none. An initially terminal state stops at length zero.

**Definition 1.14 (Paid prefix length).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.charged`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.charged` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The charge through prefix length n counts exactly those positions j<n whose source state is active. Each such edge costs one bit; absorbing terminal extensions cost zero.

**Definition 1.15 (Nontermination).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.Nonstop`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.Nonstop` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Nonstop means every finite prefix has activity color none. It is a property of the same actual infinite stream.

**Definition 1.16 (Root-reachable activities).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.ReachableActive`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.ReachableActive` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

These are shared activities that occur after a finite input word from the projected root. Unreachable activities contribute to the full carrier count but not to this restriction.

**Definition 1.17 (General sufficient activity bound).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.bound`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.bound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

B(m)=m(m-1)(m+1)/6 minus the sum of floor(e/2)^2 for e=0,...,m, plus floor(m/2). The zero summand makes this the same sum as e=1,...,m. All divisions are natural-number divisions; the subtracted count does not exceed the original slot count.

**Theorem 1.18 (Complete stream preservation and activity count).**

$$(\forall m: \mathbb{N}, (m \ge 2) \implies ((\forall f: \operatorname{Table}\left(m\right), (\exists pi: \operatorname{Original}\left(m\right) \to \operatorname{Shared}\left(m\right), (\exists delta: \operatorname{Shared}\left(m\right) \to \operatorname{Fin}\left(2\right) \to \operatorname{Shared}\left(m\right), (\operatorname{Surjective}\left(pi\right)) \land \\((\forall s: \operatorname{Original}\left(m\right), \operatorname{color}\left(\operatorname{pi}\left(s\right)\right) = \operatorname{color}\left(s\right))) \land \\((\forall s: \operatorname{Original}\left(m\right), (\forall u: \operatorname{Fin}\left(2\right), \operatorname{pi}\left(\operatorname{originalStep}\left(f, s, u\right)\right) = \operatorname{delta}\left(\operatorname{pi}\left(s\right), u\right)))) \land \\((\forall omega: \mathbb{N} \to \operatorname{Fin}\left(2\right), (\forall i: \operatorname{Fin}\left(m\right), (\forall n: \mathbb{N}, \operatorname{FirstStop}\left(\operatorname{originalStep}\left(f\right), color, \operatorname{root}\left(m\right), omega, i, n\right) \iff \operatorname{FirstStop}\left(delta, color, \operatorname{pi}\left(\operatorname{root}\left(m\right)\right), omega, i, n\right))))) \land \\((\forall omega: \mathbb{N} \to \operatorname{Fin}\left(2\right), (\forall n: \mathbb{N}, \operatorname{charged}\left(\operatorname{originalStep}\left(f\right), color, \operatorname{root}\left(m\right), omega, n\right) = \operatorname{charged}\left(delta, color, \operatorname{pi}\left(\operatorname{root}\left(m\right)\right), omega, n\right)))) \land \\((\forall omega: \mathbb{N} \to \operatorname{Fin}\left(2\right), (\forall i: \operatorname{Fin}\left(m\right), (\forall n: \mathbb{N}, (\operatorname{FirstStop}\left(\operatorname{originalStep}\left(f\right), color, \operatorname{root}\left(m\right), omega, i, n\right)) \implies (\operatorname{charged}\left(\operatorname{originalStep}\left(f\right), color, \operatorname{root}\left(m\right), omega, n\right) = n))))) \land \\((\forall omega: \mathbb{N} \to \operatorname{Fin}\left(2\right), \operatorname{Nonstop}\left(\operatorname{originalStep}\left(f\right), color, \operatorname{root}\left(m\right), omega\right) \iff \operatorname{Nonstop}\left(delta, color, \operatorname{pi}\left(\operatorname{root}\left(m\right)\right), omega\right))) \land \\(\operatorname{Finite}\left(\operatorname{Shared}\left(m\right)\right)) \land \\(\operatorname{card}\left(\operatorname{SharedActive}\left(m\right)\right) = \operatorname{B}\left(m\right)) \land \\(\operatorname{card}\left(\operatorname{ReachableActive}\left(delta, \operatorname{pi}\left(\operatorname{root}\left(m\right)\right)\right)\right) \le \operatorname{B}\left(m\right)) \land \\(\operatorname{card}\left(\operatorname{Fin}\left(m\right)\right) = m) \land \\((\forall q: \mathbb{N}, (q \ge 1) \implies ((\operatorname{B}\left(2 \cdot q\right) = \frac{2 \cdot q^{3}+q}{3}) \land \\(\operatorname{B}\left(2 \cdot q+1\right) = \frac{2 \cdot q^{3}+3 \cdot q^{2}+4 \cdot q}{3})))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m >= 2 and every legal stationary table f, there are a surjective projection pi and a fixed ordered transition delta on a finite shared carrier. The projection preserves activity and every terminal label, and it commutes with each bit transition. For every infinite stream, the first terminal label and stopping length agree, all prefix charges agree, and nontermination agrees. At a first stop of length n, the original charge is n; hence so is the shared charge. The full shared activity carrier has exactly B(m) states, its root-reachable activity carrier has at most B(m), and there are m terminals.

At a fixed layer e, write j=floor(e/2). The immediate slots are in bijection with Fin(j) times Fin(j): the first coordinate selects r=e-j,...,e-1 and the second selects k=0,...,j-1. Thus j^2 original slots are replaced. Every P_k has an original representative with e=2(k+1) and r=k+1. The ordered terminal pair is independent of which representative is used. Summing the remaining singletons and adding the shared pairs gives B(m). The even and odd endpoints yield the two displayed cubic formulas. This is a sufficient bound, with no minimality or sharpness assertion.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.FirstStop`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.Immediate`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.Nonstop`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.ReachableActive`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.SharedActive`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.Slot`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.Table`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.aggregate`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.bound`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.charged`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.originalStep`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.outputCount`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.outputLabel`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.projection`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.result`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.root`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.sharedStep`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation.trace`
- Dependency: [D5/S3/Arith/FibonacciAtomic/TriangularPathNormalization](TriangularPathNormalization.md)
