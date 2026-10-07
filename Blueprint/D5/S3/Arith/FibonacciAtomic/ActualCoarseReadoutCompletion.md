# Common Completion of Finite Coarse Routes

## Abstract

Every finite coarse route has a globally correct actual-tree completion with complete leaf verification, existence-controlled acquisition and an exact address cache.

Source, Address, Reply, Positive, Strategy, readout, leaves, paid and terminal are the original actual-tree objects. Positive means membership in the third Fibonacci substitution image. The existing coarse quotient kappa preserves the two leaf labels and merges branch with absent into none. Function.FactorsThrough(pi.policy,kappa_hist) requires equality of policy actions on every pair of raw histories with equal coarse histories, including unreachable histories.

**Definition 1.1 (Reply representatives).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualCoarseReadoutCompletion.encodeHistory`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualCoarseReadoutCompletion.encodeHistory` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

encodeHistory maps each coarse report to the same address and a raw representative: some(true) to alpha, some(false) to beta, and none to branch. This is a section for policy evaluation. It gives no existence certificate for an arbitrary address. Write N(h)=encodeHistory(kappa_hist(h)).

**Definition 1.2 (Finite route compilation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualCoarseReadoutCompletion.compileRaw`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualCoarseReadoutCompletion.compileRaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The route p is the existing finite dependent PassiveProtocol over Address with response Option Bool. A decoder maps its complete coarse chronological history to an optional prototype index. compileRaw(F,decode,p,g) compiles each query through kappa and accumulates the coarse routing history g. A selected stop starts verifyController(F(i),leaves(F(i))); an unselected stop starts fallback. Neither phase receives the preceding route as its own logical history.

**Definition 1.3 (Exact address caching).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualCoarseReadoutCompletion.cachedExecute`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualCoarseReadoutCompletion.cachedExecute` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

cachedExecute takes a native raw policy, fuel, logical history, cache and input. A logical request is always recorded. If its exact address occurs in the cache, the stored reply is reused. Otherwise the actual readout is obtained and appended. The cache begins empty, contains only reports acquired in the same run, and stores neither inferred prefixes nor prototype knowledge. Repeated logical requests consume logical fuel but do not add paid addresses.

**Theorem 1.4 (All-source completion and exact prototype fees).**

$$\forall m: Nat, (\forall F: \operatorname{Function}\left(\operatorname{Fin}\left(m\right), \operatorname{Source}\left(\right)\right), ((\forall i: \operatorname{Fin}\left(m\right), (\operatorname{Positive}\left(\operatorname{F}\left(i\right)\right))) \implies (\forall p: \operatorname{PassiveProtocol}\left(\operatorname{Address}\left(\right), \operatorname{Option}\left(Bool\right)\right), (\forall decode: \operatorname{Function}\left(CH, \operatorname{Option}\left(\operatorname{Fin}\left(m\right)\right)\right), (\exists pi: \operatorname{Strategy}\left(\right), ((\operatorname{policy}\left(pi\right) = \operatorname{compose}\left(\operatorname{CP}\left(C\right), N\right)) \land (\operatorname{FactorsThrough}\left(\operatorname{policy}\left(pi\right), K\right)) \land (\forall U: \operatorname{Source}\left(\right), (\exists n: Nat, (\exists t: RH, (\exists b: Bool, (\exists cache: RH, ((\operatorname{E}\left(pi, n, U\right) = \operatorname{some}\left(\operatorname{pair}\left(t, b\right)\right)) \land (\operatorname{CE}\left(pi, n, U\right) = \operatorname{some}\left(\operatorname{pair}\left(\operatorname{pair}\left(t, b\right), cache\right)\right)) \land (\operatorname{pair}\left(t, b\right) = \operatorname{T}\left(pi, U\right)) \land ((b = true) \iff (\operatorname{Positive}\left(U\right))) \land (\operatorname{ND}\left(cache\right)) \land (\operatorname{Truth}\left(U, cache\right)) \land (\operatorname{paid}\left(cache\right) = \operatorname{paid}\left(t\right)))))))) \land (\forall U: \operatorname{Source}\left(\right), (\forall h: RH, (\forall s: RH, (\operatorname{Phase}\left(U, h, s\right))))) \land (\forall V: \operatorname{Source}\left(\right), (\forall pre: \operatorname{List}\left(\operatorname{Address}\left(\right)\right), (\forall rest: \operatorname{List}\left(\operatorname{Address}\left(\right)\right), (\forall q: \operatorname{Address}\left(\right), (\forall y: \operatorname{Reply}\left(\right), (\forall s: RH, (\operatorname{Failed}\left(V, pre, rest, q, y, s\right)))))))) \land (\forall U: \operatorname{Source}\left(\right), (\forall h: RH, (\forall q: \operatorname{Address}\left(\right), (\operatorname{Acq}\left(U, h, q\right))))) \land (\forall i: \operatorname{Fin}\left(m\right), (\operatorname{Prototype}\left(pi, i\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ActualCoarseReadoutCompletion.completion_contract` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the formula RH is the native raw history type Hist(fun _ : Address => Reply), and CH is the coarse chronological history type Hist(fun _ : Address => Option Bool). R(p,U) is runPassiveProtocol(q,W -> leafLabel(W,q),p,U), K is kappa_hist, N is the representative map defined above, and C is compileRaw(F,decode,p,empty). V(i) is verifyController(F(i),leaves(F(i))). CP and CO denote controllerPolicy and controllerOutcome. FactorsThrough denotes Function.FactorsThrough. empty is the empty list, concat is chronological list concatenation, report(q,y) is the dependent address-response pair, and one(x) is a singleton list. leafTrace(V) maps every address in leaves(V) to its actual labelled reply. A(g) is the finite set of addresses in a coarse history g, and L(V) is the existing leafAddresses(V). E(pi,n,U) is execute(readout,pi.policy,n,empty,U); CE(pi,n,U) is cachedExecute(pi.policy,n,empty,empty,U). T(pi,U) is terminal(pi,U). Truth(U,cache) means every stored reply equals the actual readout at its exact address, and ND(cache) means the cache address list has no duplicate.

Phase(U,h,s) states that K(h)=R(p,U) implies pi.policy(concat(h,s)) equals CP(V(i),N(s)) when decode(K(h))=some(i), and acquisitionPolicy(N(s)) when it is none. Failed(V,pre,rest,q,y,s) states that leaves(V)=concat(pre,cons(q,rest)) and kappa(y) differs from leafLabel(V,q) imply CP(verifyController(V,leaves(V)),N(concat(concat(leafTrace(pre,V),one(report(q,y))),s)))=acquisitionPolicy(N(s)). Here leafTrace(pre,V) records exactly the matching reports on the listed prefix pre. These equalities hold for every future logical suffix s, so both phases start with fresh logical histories.

Acq(U,h,q) states that h is a prefix of acquisitionTrace(empty,U) and acquisitionPolicy(N(h))=inl(q) imply three conclusions: an actual subtree exists at q; kappa(readout(q,U))=none then forces this subtree to be a branch; and every nonroot q is concat(v,one(d)) for a parent v and direction d whose actual branch report occurs in h. The parent condition supplies existence from a preceding real request. A cached none alone supplies no such evidence.

Prototype(pi,i) applies only when decode(R(p,F(i)))=some(i). It gives K(T(pi,F(i)).history)=concat(R(p,F(i)),K(leafTrace(F(i)))) and paid(T(pi,F(i)).history)=union(A(R(p,F(i))),L(F(i))). No prototype fee formula is asserted when the route chooses another index or abandons routing.

The full result quantifies every finite coarse route, every decoder and every positive prototype family, including the empty family. Correctness and finite termination quantify all Source inputs without a size, positivity or family-membership promise. The known raw phase theorem supplies leaf-verifier correctness and finite raw execution. Reachable acquisition prefixes fix the quotient representatives; the frontier invariant establishes actual subtree existence and previously reported parents. The compiled coarse route therefore has the same actual execution as the raw controller. Cache hits reproduce real reports, while misses append one new address, making the final cache truthful and its paid set exactly the logical request set. The prototype trace identity adds the complete leaf phase to precisely the selected route.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualCoarseReadoutCompletion.cachedExecute`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualCoarseReadoutCompletion.compileRaw`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualCoarseReadoutCompletion.completion_contract`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualCoarseReadoutCompletion.encodeHistory`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualCoarseReadoutHistory](ActualCoarseReadoutHistory.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore](ActualJointResponseCostCore.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity](ActualLeafHistoryRigidity.md)
