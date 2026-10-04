# Fresh Coarse Divergence and Saturated Shared Histories

## Abstract

Coarse-observable actual tree strategies separate distinct nonconflicting positives at a fresh nonleaf query, forcing saturated shared histories to incur two nonleaf payments on one input.

Sources, addresses, four-valued replies, globally correct strategies, terminal histories and paid sets are the original actual-tree objects. A strategy terminates correctly on every finite source from the same empty initial history. No uniform fuel bound, source description, or finite-family promise is assumed. The coarse readout is the existing leafLabel: alpha is some(true), beta is some(false), while branch and absent both give none. L(W) denotes the existing leafAddresses(W).

**Definition 1.1 (Coarse reply map).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualCoarseReadoutHistory.kappa`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualCoarseReadoutHistory.kappa` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Kappa sends alpha to some(true), beta to some(false), and both branch and absent to none. The reply carrier is Option Bool.

**Definition 1.2 (Chronological coarse histories).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualCoarseReadoutHistory.kappa_hist`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualCoarseReadoutHistory.kappa_hist` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

KappaHist maps each original report to its address and coarse reply. It preserves order, length and repeated requests. The coarse history carrier H is the existing dependent history type over Address with constant response type Option Bool.

**Definition 1.3 (Coarse-observable original policies).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualCoarseReadoutHistory.CoarseObservable`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualCoarseReadoutHistory.CoarseObservable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A policy p is coarse-observable when p(a)=p(b) whenever kappaHist(a)=kappaHist(b), for all raw histories a and b, including histories not reached on any source. The strategy, execution and fee definitions are unchanged.

**Theorem 1.4 (Fresh divergence and saturated nonleaf excess).**

$$\forall pi: \operatorname{Strategy}\left(\right), ((\operatorname{O}\left(\operatorname{policy}\left(pi\right)\right)) \implies (\forall U: \operatorname{Source}\left(\right), (\forall V: \operatorname{Source}\left(\right), (\forall h: H, (((\operatorname{Positive}\left(U\right)) \land (\operatorname{Positive}\left(V\right)) \land (U \neq V) \land (\operatorname{NC}\left(U, V\right)) \land (\operatorname{prefix}\left(h, \operatorname{T}\left(pi, U\right)\right)) \land (\operatorname{prefix}\left(h, \operatorname{T}\left(pi, V\right)\right))) \implies (\exists s: H, (\exists q: \operatorname{Address}\left(\right), ((\operatorname{prefix}\left(\operatorname{concat}\left(\operatorname{concat}\left(h, s\right), \operatorname{one}\left(\operatorname{report}\left(q, \operatorname{leafLabel}\left(U, q\right)\right)\right)\right), \operatorname{T}\left(pi, U\right)\right)) \land (\operatorname{prefix}\left(\operatorname{concat}\left(\operatorname{concat}\left(h, s\right), \operatorname{one}\left(\operatorname{report}\left(q, \operatorname{leafLabel}\left(V, q\right)\right)\right)\right), \operatorname{T}\left(pi, V\right)\right)) \land (\operatorname{leafLabel}\left(U, q\right) \neq \operatorname{leafLabel}\left(V, q\right)) \land (\neg (q \in \operatorname{A}\left(\operatorname{concat}\left(h, s\right)\right))) \land ((\neg (q \in \operatorname{L}\left(U\right))) \lor (\neg (q \in \operatorname{L}\left(V\right)))) \land (((\operatorname{nonempty}\left(\operatorname{diff}\left(\operatorname{A}\left(h\right), \operatorname{L}\left(U\right)\right)\right)) \land (\operatorname{nonempty}\left(\operatorname{diff}\left(\operatorname{A}\left(h\right), \operatorname{L}\left(V\right)\right)\right))) \implies ((2 \leq \operatorname{card}\left(\operatorname{diff}\left(\operatorname{J}\left(pi, U\right), \operatorname{L}\left(U\right)\right)\right)) \lor (2 \leq \operatorname{card}\left(\operatorname{diff}\left(\operatorname{J}\left(pi, V\right), \operatorname{L}\left(V\right)\right)\right))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ActualCoarseReadoutHistory.shared_history_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the formula, T(pi,W)=kappaHist(terminal(pi,W).history), J(pi,W)=paid(terminal(pi,W).history), and A(g) is the finite set of addresses occurring in the coarse history g. concat is chronological list concatenation, report(q,r) is the dependent address-response pair, and one(a) is the singleton list. prefix means List.IsPrefix; diff is finite-set difference; card and nonempty have their ordinary finite-set meanings. Positive is membership in the third native Fibonacci substitution image, and NC is the existing Nonconflict predicate. O(pi.policy) means CoarseObservable(pi.policy).

For any common coarse terminal prefix h, the history s extends it to a first differing coarse reply. Coarse observability synchronizes the query at each matching step. Complete compulsory leaf acquisition and literal frontier rigidity rule out identical coarse terminal histories. A repeated address has already fixed its truthful reply on both inputs, so the separating query is fresh. Nonconflict excludes differing labels at a shared leaf. If both inputs have already paid a nonleaf on h, the input for which the fresh query is a nonleaf therefore has two distinct nonleaf payments.

A common raw history cannot replace a common coarse history: branch and absent may already differ while their coarse reports remain equal. The theorem concerns saturated shared histories and the minimal coarse interface. Joint completion, fallback and cache contracts, finite-family pruning, and endpoint classifications are outside its statement.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualCoarseReadoutHistory.CoarseObservable`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualCoarseReadoutHistory.kappa`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualCoarseReadoutHistory.kappa_hist`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualCoarseReadoutHistory.shared_history_obstruction`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation](ActualImageSevenLeafSeparation.md)
