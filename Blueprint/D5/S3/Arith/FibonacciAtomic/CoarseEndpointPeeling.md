# Coarse Endpoint Leaf Peeling

## Abstract

A target attains the coarse endpoint precisely when its leaves separate at most one merged nonleaf competitor at a time.

The sources are all finite nonempty ordered binary trees with Boolean leaf labels. Positive means membership in the third substitution image. A Strategy has one deterministic history policy, an empty initial history on every source, and a correct finite run on every source. Fees count distinct actual addresses. kappa preserves the two leaf labels and merges branch and absent into none; CoarseObservable requires the policy to agree on every pair of histories with the same chronological coarse history.

**Definition 1.1 (Safe merged-nonleaf peeling).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/CoarseEndpointPeeling.Peels`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/CoarseEndpointPeeling.Peels` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For family F, target z and current survivor set S, every listed address q must be a leaf of F(z). The existing coarse fiber at none has cardinality at most one. Continue with the fiber at the target's leaf label. The empty list requires S to be contained in {z}. Starting with all members retains the target throughout. Nonconflict makes any competitor that is still a leaf report the same label, so each step deletes exactly the merged branch-or-absent group.

**Definition 1.2 (Finite actual coarse route).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/CoarseEndpointPeeling.peelRoute`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/CoarseEndpointPeeling.peelRoute` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The passive protocol requests the listed addresses in order while the actual coarse reply equals the target's label. A different reply immediately stops the route. Repeated addresses remain logical requests, with distinct-address charging supplied by the common completion.

**Definition 1.3 (Reached singleton selection).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/CoarseEndpointPeeling.peelDecode`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/CoarseEndpointPeeling.peelDecode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Replay the route history from its current survivor set. Matching replies update that set to the existing coarse fiber. A different reply selects its unique member when that response fiber is a singleton. Exhausting the list selects z. A malformed query address, incomplete history or non-singleton different response selects no member. The common completion verifies a selected member's complete leaf frontier and starts acquisition when no member is selected or verification fails.

**Theorem 1.4 (Endpoint equivalence and exact paid sets).**

$$\forall k: Nat, ((1 \leq k) \implies (\forall z: \operatorname{Fin}\left(m\right), (((\exists pi: \operatorname{Strategy}\left(\right), ((\operatorname{CoarseObservable}\left(\operatorname{policy}\left(pi\right)\right)) \land (\forall i: \operatorname{Fin}\left(m\right), (\operatorname{C}\left(pi, \operatorname{Fk}\left(i\right)\right) = n + 1 - \operatorname{indicator}\left(i = z\right))))) \iff (\exists qs: \operatorname{List}\left(\operatorname{Address}\left(\right)\right), (\operatorname{Peels}\left(Fk, z, univ, qs\right)))) \land (\forall qs: \operatorname{List}\left(\operatorname{Address}\left(\right)\right), ((\operatorname{Peels}\left(Fk, z, univ, qs\right)) \implies (\exists pi: \operatorname{Strategy}\left(\right), ((\operatorname{policy}\left(pi\right) = \operatorname{P}\left(Fk, z, qs\right)) \land (\operatorname{CoarseObservable}\left(\operatorname{policy}\left(pi\right)\right)) \land (\forall i: \operatorname{Fin}\left(m\right), (\operatorname{C}\left(pi, \operatorname{Fk}\left(i\right)\right) = n + 1 - \operatorname{indicator}\left(i = z\right))) \land (\operatorname{J}\left(pi, \operatorname{Fk}\left(z\right)\right) = \operatorname{L}\left(\operatorname{Fk}\left(z\right)\right)) \land (\forall i: \operatorname{Fin}\left(m\right), ((i \neq z) \implies (\exists q: \operatorname{Address}\left(\right), ((\operatorname{First}\left(qs, Fk, i\right) = \operatorname{some}\left(q\right)) \land (\neg (q \in \operatorname{L}\left(\operatorname{Fk}\left(i\right)\right))) \land (\operatorname{J}\left(pi, \operatorname{Fk}\left(i\right)\right) = \operatorname{L}\left(\operatorname{Fk}\left(i\right)\right) \cup \operatorname{singleton}\left(q\right)))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/CoarseEndpointPeeling.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every k at least one, m=2k+1 and n=3k+13. Fk is Scale38NestedCompensation.family transported through Fintype.equivFin from Unit plus Fin(k) plus Fin(k) to Fin(m). Every member is positive, distinct and has n leaves; every pair is nonconflicting. The target z ranges over all members. The indicator equals one precisely when i=z, and subtraction is natural subtraction.

L(U) denotes leafAddresses(U), C(pi,U) denotes cost(pi,U), and J(pi,U) denotes paid(terminal(pi,U).1). First(qs,Fk,i) is List.find? on the predicate leafLabel(Fk(i),a)=none, so it names the first nonleaf exit even when qs repeats addresses. P(Fk,z,qs) is the policy obtained by compileRaw with peelRoute and peelDecode, evaluated on encodeHistory(kappa_hist(h)). The equality with this policy connects the precise bills to the actual common completion, including its globally correct fallback.

A baseline-cost target must request exactly its leaves. A surviving competitor shares the target's coarse prefix, and the same next query therefore extends both actual histories. If two competitors report none there, each has paid a nonleaf on their common coarse prefix. The common-history obstruction forces one to pay at least two nonleaves, contrary to endpoint costs. At the target's terminal history no different member can remain, since the same obstruction supplies a strictly later divergence. Following the target's finite terminal trace gives the safe list.

Conversely a safe route selects the unique exiting competitor or the target. Requests before an exit are that member's own leaves; the exit is its sole nonleaf. The complete verifier obtains every leaf of the selected member. The common completion's paid-set union therefore gives L(Z) on the target and L(U) union the singleton exit on every competitor, and hence the stated costs.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CoarseEndpointPeeling.Peels`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CoarseEndpointPeeling.peelDecode`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CoarseEndpointPeeling.peelRoute`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CoarseEndpointPeeling.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualCoarseReadoutCompletion](ActualCoarseReadoutCompletion.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Scale38NestedCompensation](Scale38NestedCompensation.md)
