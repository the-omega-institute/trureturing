# Exact transition count of machine 3626

## Abstract

The signed Moebius and totient divisor sum counts every transition of the one-sided machine on every positive binary input.

The external question is Peter Bala's conjecture in OEIS A393210, also recorded in A069517; the alias pair is one question. Its unchanged prospective registration is https://github.com/the-omega-institute/trureturing/issues/25808#issuecomment-6587694551. The scope is every positive natural input, with no finite cutoff, tape bound or counter width.

**Definition 1.1 (Two machine states).**

Lean statement: `D5/S0/Computability/BinaryMachine/Machine3626.State`

*Formalization.* `D5/S0/Computability/BinaryMachine/Machine3626.State` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala; Sean A. Irvine; Stephen Wolfram (2026). *OEIS A393210: halting time for Wolfram machine 3626*. URL: <https://oeis.org/A393210>.

*Commentary.*

State has exactly the constructors A and B; termination is a boundary crossing, rather than a third state.

**Definition 1.2 (Unbounded half-tape configuration).**

Lean statement: `D5/S0/Computability/BinaryMachine/Machine3626.Cfg`

*Formalization.* `D5/S0/Computability/BinaryMachine/Machine3626.Cfg` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala; Sean A. Irvine; Stephen Wolfram (2026). *OEIS A393210: halting time for Wolfram machine 3626*. URL: <https://oeis.org/A393210>.

*Commentary.*

Cfg contains state : State, left : List Bool, and right : List Bool. The head scans the first left bit. Absent left bits are implicit blank zero. The right list records cells between the head and the fixed right boundary. Both list lengths are unbounded.

**Definition 1.3 (Right move and boundary crossing).**

Lean statement: `D5/S0/Computability/BinaryMachine/Machine3626.exitRight`

*Formalization.* `D5/S0/Computability/BinaryMachine/Machine3626.exitRight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala; Sean A. Irvine; Stephen Wolfram (2026). *OEIS A393210: halting time for Wolfram machine 3626*. URL: <https://oeis.org/A393210>.

*Commentary.*

For writtenLeft : List Bool and right : List Bool, exitRight writtenLeft [] is none. For right = b :: rest it is some (Cfg.mk State.B (b :: writtenLeft) rest). This consumes the nearest right cell and enters B after writing; none denotes the actual boundary crossing.

**Definition 1.4 (Literal transition semantics).**

Lean statement: `D5/S0/Computability/BinaryMachine/Machine3626.step`

*Formalization.* `D5/S0/Computability/BinaryMachine/Machine3626.step` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala; Sean A. Irvine; Stephen Wolfram (2026). *OEIS A393210: halting time for Wolfram machine 3626*. URL: <https://oeis.org/A393210>.

*Commentary.*

Cfg has a state A or B and two unbounded Boolean lists. The left list begins at the scanned cell and continues toward the most significant end; absent cells are implicit blank zero. The right list records the finite distance to the fixed right boundary. The four simultaneous read/write/state/move rules are A0 to A0L, A1 to B1R, B0 to A1L, and B1 to B0R. exitRight returns none precisely when a right move crosses the boundary; otherwise its result has state B. There is no separate halt state.

**Definition 1.5 (Counted first boundary crossing).**

Lean statement: `D5/S0/Computability/BinaryMachine/Machine3626.Trace`

*Formalization.* `D5/S0/Computability/BinaryMachine/Machine3626.Trace` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala; Sean A. Irvine; Stephen Wolfram (2026). *OEIS A393210: halting time for Wolfram machine 3626*. URL: <https://oeis.org/A393210>.

*Commentary.*

Trace.zero counts zero transitions at a configuration. Trace.cons adds one nonhalting transition to a trace from its successor. Trace.crossing counts exactly one transition whose result is none. No constructor continues a trace after none, so Trace t c none records the first boundary crossing at transition t, rather than merely a visit to a terminal state.

**Definition 1.6 (Positive binary input at the right edge).**

$$\forall n: \mathbb{N}, \operatorname{initial}\left(n\right) = \operatorname{Cfg}.\operatorname{mk}\left(\operatorname{State}.\operatorname{A}, \operatorname{Nat}.\operatorname{bits}\left(n\right), \operatorname{List}.\operatorname{nil}\right)$$

*Formalization.* `D5/S0/Computability/BinaryMachine/Machine3626.initial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala; Sean A. Irvine; Stephen Wolfram (2026). *OEIS A393210: halting time for Wolfram machine 3626*. URL: <https://oeis.org/A393210>.

*Commentary.*

Nat.bits is least-significant-bit first. The head scans that bit in state A at the right boundary; the empty right list fixes the actual boundary. Blank cells extend infinitely to the left of the most significant digit. The final result excludes n = 0.

**Definition 1.7 (Zeros before the first one).**

$$\forall k: \mathbb{N}, \forall higher: \operatorname{List}\left(Bool\right), \operatorname{block}\left(k, higher\right) = \operatorname{List}.\operatorname{append}\left(\operatorname{List}.\operatorname{replicate}\left(k, false\right), \operatorname{List}.\operatorname{cons}\left(true, higher\right)\right)$$

*Formalization.* `D5/S0/Computability/BinaryMachine/Machine3626.block` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala; Sean A. Irvine; Stephen Wolfram (2026). *OEIS A393210: halting time for Wolfram machine 3626*. URL: <https://oeis.org/A393210>.

*Commentary.*

The block contains k zero bits followed by its first one and arbitrary higher bits. The lists have no fixed maximum length.

**Theorem 1.8 (A restoring block crosses in the exact count).**

$$\forall k: \mathbb{N}, \forall higher: \operatorname{List}\left(Bool\right), \operatorname{Trace}\left(4 \cdot 2^{k} - 3, \operatorname{Cfg}.\operatorname{mk}\left(\operatorname{State}.\operatorname{A}, \operatorname{block}\left(k, higher\right), \operatorname{List}.\operatorname{nil}\right), none\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/BinaryMachine/Machine3626.block_first_crossing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala; Sean A. Irvine; Stephen Wolfram (2026). *OEIS A393210: halting time for Wolfram machine 3626*. URL: <https://oeis.org/A393210>.

*Commentary.*

The recursive trace restores the lower block after each of two smaller traversals and then exits. Its transition count satisfies T(0) = 1 and T(k+1) = 2 T(k) + 3. Solving this recurrence gives 4 times 2 to the k minus 3. Higher cells remain arbitrary. The last crossing transition is included.

**Theorem 1.9 (Every positive input has the required operational trace).**

$$\forall n: \mathbb{N}, 0 < n \Rightarrow \exists k: \mathbb{N}, \exists higher: \operatorname{List}\left(Bool\right), \operatorname{Nat}.\operatorname{bits}\left(n\right) = \operatorname{block}\left(k, higher\right) \land \operatorname{Trace}\left(4 \cdot 2^{k} - 3, \operatorname{initial}\left(n\right), none\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/BinaryMachine/Machine3626.positive_input_first_crossing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala; Sean A. Irvine; Stephen Wolfram (2026). *OEIS A393210: halting time for Wolfram machine 3626*. URL: <https://oeis.org/A393210>.

*Commentary.*

Binary recursion finds the first one of every positive input. The restoring-block trace then supplies the actual first boundary crossing. This operational theorem is a live prerequisite of the exact arithmetic result.

**Theorem 1.10 (Exact signed Moebius and totient formula).**

$$\forall n: \mathbb{N}, 0 < n \Rightarrow \exists t: \mathbb{N}, \operatorname{Trace}\left(t, \operatorname{initial}\left(n\right), none\right) \land (t: \mathbb{Z}) = \sum_{d \in \operatorname{Nat}.\operatorname{divisors}\left(n\right)} (\sum_{e \in \operatorname{Nat}.\operatorname{divisors}\left(d\right)} (0 - 1)^{e + 1} \cdot \operatorname{ArithmeticFunction}.\operatorname{moebius}\left(e\right))^{2} \cdot (\operatorname{Nat}.\operatorname{totient}\left(d\right): \mathbb{Z})$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/BinaryMachine/Machine3626.result` (`✓ std3`). ∎

*Resolves.* `Problems/bala-machine3626-exact-halting-time` (proved) by `D5/S0/Computability/BinaryMachine/Machine3626.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bala-machine3626-exact-halting-time","declaration_gid":"D5/S0/Computability/BinaryMachine/Machine3626.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala; Sean A. Irvine; Stephen Wolfram (2026). *OEIS A393210: halting time for Wolfram machine 3626*. URL: <https://oeis.org/A393210>.

*Commentary.*

The source sentence is: Conjecture: a(n) = Sum_{d | n} m(d)^2 * phi(d), where m(n) = Sum_{d | n} (-1)^(d+1) * moebius(d) = A069517(n) and phi(n) denotes Euler's totient function A000010(n). Cf. A296306. This is the conjecture line in OEIS A393210, revision 18. For every natural n greater than zero there exists a transition count t with Trace t (initial n) none and the displayed integer equality. Both divisor sums range over all positive divisors; powers of minus one, Moebius values, the square and the outer sum are interpreted in the integers. The totient and the natural transition count are cast to integers. The proof uses the published arithmetic multiplicativity and prime-power values through pinned Mathlib's Moebius and totient results. Odd prime factors contribute one to the outer divisor transform; the 2-power factor contributes 4 times 2 to the k minus 3, matching the same binary prefix used by the operational trace. This is a symbolic theorem for all positive inputs. It makes no claim for input zero or for another machine or boundary convention.

## References

- Truth anchor: `D5/S0/Computability/BinaryMachine/Machine3626.Cfg`
- Truth anchor: `D5/S0/Computability/BinaryMachine/Machine3626.State`
- Truth anchor: `D5/S0/Computability/BinaryMachine/Machine3626.Trace`
- Truth anchor: `D5/S0/Computability/BinaryMachine/Machine3626.block`
- Truth anchor: `D5/S0/Computability/BinaryMachine/Machine3626.block_first_crossing`
- Truth anchor: `D5/S0/Computability/BinaryMachine/Machine3626.exitRight`
- Truth anchor: `D5/S0/Computability/BinaryMachine/Machine3626.initial`
- Truth anchor: `D5/S0/Computability/BinaryMachine/Machine3626.positive_input_first_crossing`
- Truth anchor: `D5/S0/Computability/BinaryMachine/Machine3626.result`
- Truth anchor: `D5/S0/Computability/BinaryMachine/Machine3626.step`
