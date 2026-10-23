# Exact Native Total-State Frontier

## Abstract

The exact jointly optimized complete-entry and total-state frontier holds on the entire original native repeated-partner origin fiber.

Solves(M,entry,r,q) quantifies every actual origin in NativeSixSourceCones.Fiber. The entire exported and recoverable initial mutable state is entry(x) in Q+H. A finite set E covers its realized range with cardinality at most r; because Q+H is finite this is exactly an upper bound on realized export capacity. For every origin there is a terminating actual stationary Run with at most q running visits and fixed whole-row output canonicalRow(P,x). Tables, addresses, state spaces and outputs are common across all origins. All members of Q and H are charged, including unreachable states. The arbitrary function entry is quantified together with the common controller; no particular encoder is fixed in the lower theorem.

**Theorem 1.1 (Native Capacity and State Bounds).**

$$\forall Q: Type, (\forall H: Type, ([\operatorname{Fintype}\left(Q\right)] [\operatorname{Fintype}\left(H\right)], \forall M: \operatorname{Controller}\left(Q, H\right), (\forall entry: (Fiber) \to (\operatorname{Sum}\left(Q, H\right)), (\forall r: Nat, (\forall q: Nat, ((\operatorname{Solves}\left(M, entry, r, q\right)) \implies ((5 \leq \operatorname{mul}\left(r, \operatorname{pow}\left(2, q\right)\right)) \land (5 \leq \operatorname{card}\left(H\right)) \land (\operatorname{max}\left(5, \operatorname{sub}\left(10, r\right)\right) \leq \operatorname{card}\left(\operatorname{Sum}\left(Q, H\right)\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeRepeatedPartnerFrontier.native_budget_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact all-address factorization of the six actual sources is used at each visited running state. Its two possible native replies define two common successors for that state. Bounded unrolling produces a finite set of possible halts with cardinality at most two to the power q. The five distinct complete predecessor rows require five distinct halts. Taking the union over at most r actual entry values gives five at most r times two to the power q. Binary replies are asserted only on these actual sources, not on the full native interface or every origin.

For the state bound let R be the union of running states in these actual terminating runs and V their disjoint running and terminal states. All five distinct required halts occur in V, so its cardinality is at least card(R)+5. The run-support lemma proves that every vertex in V is either an exported entry or one of the two native successors of a member of R. Therefore card(V) is at most r+2card(R), and five is at most r+card(R). Counting the entire Q+H gives total at least max(5,10-r). This is the reachable-graph counting method applied to the exact native reply restriction. It imposes no acyclicity, unique-predecessor, tree-controller or non-repetition assumption.

**Theorem 1.2 (All Upper Budgets).**

$$\forall r: Nat, (\forall q: Nat, ((1 \leq r) \implies ((\forall Q: Type, (\forall H: Type, ([\operatorname{Fintype}\left(Q\right)] [\operatorname{Fintype}\left(H\right)], \forall M: \operatorname{Controller}\left(Q, H\right), (\forall entry: (Fiber) \to (\operatorname{Sum}\left(Q, H\right)), ((\operatorname{Solves}\left(M, entry, r, q\right)) \implies ((5 \leq \operatorname{mul}\left(r, \operatorname{pow}\left(2, q\right)\right)) \land (\operatorname{minimum}\left(r, q\right) \leq \operatorname{card}\left(\operatorname{Sum}\left(Q, H\right)\right)))))))) \land ((5 \leq \operatorname{mul}\left(r, \operatorname{pow}\left(2, q\right)\right)) \implies (\exists n: Nat, (\exists M: \operatorname{Controller}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(5\right)\right), (\exists entry: (Fiber) \to (\operatorname{Sum}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(5\right)\right)), ((\operatorname{Solves}\left(M, entry, r, q\right)) \land (\operatorname{add}\left(n, 5\right) = \operatorname{minimum}\left(r, q\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeRepeatedPartnerFrontier.exact_frontier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Minimum(r,q) is ten when r=1 and q=3, and max(5,10-r) otherwise. The first conjunct is universal over all finite running and halting types, every common controller and every complete-entry encoder. It proves infeasibility whenever r times two to the power q is less than five, and the minimum lower bound whenever a successful controller exists. The second conjunct constructs a controller with exactly that minimum at every feasible budget, using five fixed complete-row halts. Thus nonexistence represents the infinite branch of the original minimum formula; no finite substitute or fixed-encoder performance statement is used.

At capacity one, the complete-entry cover has at most one member, so all actual origins have one common entry. The previously proved six-source three-call obstruction gives ten states at (1,3). All other state lower bounds use native_budget_lower. The six matching full-fiber constructions supply ten at (1,3), nine for r=1 and q at least four, eight for r=2 and q at least two, seven for r=3 and q at least one, six for r=4 and q at least one, and five for r at least five. Elementary integer case analysis exhausts every feasible r at least one and natural q. Capacity and invocation limits are upper bounds, so the construction adds no dummy queries or exported distinctions.

The domain, all literal addresses, repeated partner occurrences, complete predecessor rows and entire mutable-state contract are unchanged. Genuine acquisition, same-version authentication, actual export, recoverable normalization, access isolation and native-service continuity remain supplied premises. The frontier counts abstract states and actual native calls. It identifies neither exported capacity with running memory nor state cardinality with physical storage, production cost, address price or time. Existing native chart and finite-root suppliers remain the source of their reused statements; the new content is the actual six-source restriction, forced five-address obstruction, full-fiber common controllers and their exact state frontier. No literature-priority claim is made.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeRepeatedPartnerFrontier.exact_frontier`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeRepeatedPartnerFrontier.native_budget_lower`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeRepeatedPartnerControllers](NativeRepeatedPartnerControllers.md)
