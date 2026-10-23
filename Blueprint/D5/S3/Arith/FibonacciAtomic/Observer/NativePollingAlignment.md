# Native polling alignment

## Abstract

NativePollingAlignment

A source is a finite nonempty ordered Boolean tree. The true leaf is alpha and the false leaf is beta. Substitution sends alpha to beta and beta to the ordered pair of beta and alpha, and acts on both children of every branch. The right clock is zero on alpha, one on beta, and two plus the right child's clock on a branch. An address bit false means left and true means right; rights K is the literal consisting of K right edges.

The complete program has four nonterminal controls, poll, firstUpdate, secondUpdate and route, and two terminal controls done false and done true. Poll reads rights K. Alpha selects done false, beta selects done true, absence selects firstUpdate, and branch selects poll. The first two retry controls each perform one genuine substitution update. Route then performs a root Read and selects poll for every reply. The root Read is a separate native action and does not change the source. Both done controls halt.

**Theorem 1.1 (Exact terminal bit and update epoch).**

$$\forall K: Nat, (\forall u: Source, ((\operatorname{rightClock}\left(u\right) \leq 2K + 1) \implies (\forall b: Bool, (\forall N: Nat, ((\operatorname{Run}\left(\operatorname{program}\left(K\right), \operatorname{observations}\left(u\right), poll, 0, \operatorname{done}\left(b\right), N\right)) \iff ((b = \operatorname{decide}\left(\operatorname{mod}\left(\operatorname{rightClock}\left(u\right), 2\right) = 1\right)) \land (N = 2(K - \operatorname{div}\left(\operatorname{rightClock}\left(u\right), 2\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativePollingAlignment.native_polling_alignment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The observation field at epoch j is the literal readout of the j-fold substituted original source u. Run starts at poll and epoch zero, and retains each Read and each Update of the displayed program. Its terminal epoch N counts real updates. For every source whose initial right clock is at most twice K plus one, a run reaches done b precisely for the displayed bit and update count. This includes K equal to zero and either clock parity.

Write the initial clock as twice its quotient by two plus its remainder. While a retry remains, the clock at the polling Read is below twice K, so the actual reply is absent. Two updates advance that clock by two; the intervening root Read only routes control. Induction on the number of remaining retries reaches clock twice K plus its original remainder. Its reply is alpha or beta, selecting the asserted terminal bit. Determinism of native runs identifies every halt endpoint with this constructed endpoint.

The clock promise is essential to this conclusion: branch at the pilot is an unsupported hold. The result describes the concrete same-source control program and its update epoch. It supplies no one-bit encoding, physical execution service, or theorem about recovery of all original leaf labels. In particular, the root routing Read is retained rather than contracted into an update.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativePollingAlignment.native_polling_alignment`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout](DelayedOriginalReadout.md)
- Dependency: [D5/S3/ObserverMemory/Algorithms/NativeExecutionTransport](../../../ObserverMemory/Algorithms/NativeExecutionTransport.md)
