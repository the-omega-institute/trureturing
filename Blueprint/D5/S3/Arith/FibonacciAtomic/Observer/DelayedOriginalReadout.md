# Guarded original-address recovery

## Abstract

Two current physical probes recover any original literal reply at any certified epoch.

Sources are all nonempty finite ordered full binary trees on Boolean leaves. True is alpha, false is beta; substitution sends alpha to beta and beta to pair(beta,alpha), preserving pairs. An address is a Boolean list, with false for left and true for right. Readout is the existing four-valued address-first observation. No source size, original shape, image membership, or original address presence is supplied to the program.

**Definition 1.1 (Right-spine clock).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.rightClock`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.rightClock` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Alpha has clock zero, beta has clock one, and pair(x,y) has clock two plus the clock of y. The clock and all subtrees in correctness statements are mathematical quantities, not extra observation ports.

**Definition 1.2 (Physical right suffix).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.rights`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.rights` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

rights(s) is the finite list of s true entries, generated from the known integer s.

**Theorem 1.3 (Exact epoch shift).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.right_clock_iterate`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.right_clock_iterate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural N and native source u, the clock of substitution iterated N times on u equals rightClock(u)+N. The proof starts with the one-step structural recursion.

**Theorem 1.4 (Four exact clock intervals).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.right_clock_readout`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.right_clock_readout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural s and source u, reading rights(s) is absent exactly when rightClock(u)<2s, alpha exactly when rightClock(u)=2s, beta exactly when rightClock(u)=2s+1, and branch exactly when rightClock(u) is at least 2s+2.

**Theorem 1.5 (Original nodes and newly born nodes).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.address_clock_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.address_clock_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every N,p,u, if subtree(p,u)=some(x), then there is a current subtree y at p whose clock is rightClock(x)+N. If subtree(p,u)=none, every currently present subtree y at p has rightClock(y) at most N. No current-presence condition is assumed. In one substitution, a new left beta or right alpha has clock at most one, and all longer extensions of an old leaf remain absent. Iterating this one-step bound avoids selecting a birth time.

**Definition 1.6 (Half-epoch ceiling).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.halfCeil`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.halfCeil` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

halfCeil(N)=N/2+N%2 is the ceiling of N/2 for natural N, including zero.

**Definition 1.7 (Total inverse table).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.decodeLabel`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.decodeLabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At even N the table returns its input reply, including the total absent default. At odd N, absent becomes alpha, alpha becomes beta, and either beta or branch becomes branch.

**Definition 1.8 (Historical-presence test).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.guardAccept`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.guardAccept` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For even N accept every reply except absent. For odd N accept exactly beta and branch. This test is applied at the parent followed by rights(N/2+1).

**Theorem 1.9 (Exact original-presence guard).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.original_presence_guard`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.original_presence_guard` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all N,a,d,u, the physical guard at a followed by rights(N/2+1), read on substitution iterated N times on u, accepts if and only if the original reply at a followed by the single edge d is not absent. A parent that originally exists as a branch has clock at least N+2. An original leaf parent has clock N or N+1. A parent born later has clock at most N. These cases include a parent that is still absent.

**Definition 1.10 (Source-free fixed list).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.originalQueries`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.originalQueries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For N=0 the list is [p]. For positive N and the root p=[], it is [rights(halfCeil(N))]. Otherwise it is the ordered two-entry list [dropLast(p) followed by rights(N/2+1), p followed by rights(halfCeil(N))]. Coincident entries remain two physical calls.

**Definition 1.11 (Total reply-list decoder).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.originalDecode`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.originalDecode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At N=0 return the first reply, defaulting to absent. At a positive epoch and the root, apply decodeLabel to the first reply. At a nonroot, inspect the first guard and second label replies, rejecting to absent if the guard fails; a list with fewer than two entries also returns absent. Extra entries do not affect the result.

**Theorem 1.12 (All-source literal recovery).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.original_decoder_correct`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.original_decoder_correct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural N, every finite address p, and every native source u, mapping actual current readout over originalQueries(N,p) and applying originalDecode(N,p) gives readout(p,u). Original absence, nodes born after epoch zero, and the root are included.

**Definition 1.13 (Finite physical query chain).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.queryChain`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.queryChain` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The empty query list stops. A list q::qs requests q, receives its actual reply, and continues with the chain for qs. The continuation is independent of that reply, while the chronological transcript retains it.

**Definition 1.14 (Ordered actual evidence).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.listTrace`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.listTrace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

listTrace(qs,u) maps every list occurrence q to the dependent pair of q and its actual readout on u. Ordered repetitions remain separate entries.

**Definition 1.15 (Computable history controller).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.listController`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.listController` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

With a fixed physical list qs and total terminal function finish, index qs by the consumed new history length. If there is a next address, submit it; otherwise return finish(history). This total finite controller does not use the noncomputable residual-tree selector.

**Theorem 1.16 (Finite-chain and controller agreement).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.fixed_list_execution`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.fixed_list_execution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every output type L, finite qs, total finish and native u, runPassiveProtocol(readout,queryChain(qs),u)=listTrace(qs,u). Executing listController with fuel length(qs)+1 from the empty new transcript returns that same transcript and finish of it. Projecting its addresses gives qs exactly, and its chronological length is length(qs).

**Theorem 1.17 (Effective bounded physical service).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.original_decoder_service`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.original_decoder_service` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fixed-list controller terminates on the actual current source substitution iterated N times on u and returns the original reply at p. Its chronological transcript length is at most two. Every generated physical address has length at most length(p)+halfCeil(N). If N=0 or p is the root, the physical list has exactly one entry.

For an originally present prefix a with subtree(a,u)=some(z), the separate original-presence transport theorem must give subtree(a,rho^N(u))=some(rho^N(z)). The existing appended-readout clause of actual_address_geometry then identifies the response at a followed by q with the response at q on rho^N(z). The program receives a,N,p, not z. Current presence alone cannot supply this premise: beta has no original left child, but its first image has a left beta.

The empty transcript here is the local input of a new finite query chain. It does not discard an already retained mixed-epoch history, reset the source, or certify that a physical read or substitution occurred. Interpreting each request as a lawful read of the same stationary register is a separate operational connection. No lower query bound or minimum-budget claim follows from this construction.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.address_clock_bounds`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.decodeLabel`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.fixed_list_execution`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.guardAccept`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.halfCeil`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.listController`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.listTrace`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.originalDecode`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.originalQueries`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.original_decoder_correct`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.original_decoder_service`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.original_presence_guard`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.queryChain`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.rightClock`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.right_clock_iterate`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.right_clock_readout`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.rights`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity](../ActualLeafHistoryRigidity.md)
