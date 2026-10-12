# Faithful Finite Tables for Native Bounded Observers

## Abstract

Finite native tables represent complete bounded observers and cover every admissible competitor after native absent normalization.

An observer carries every nominal configuration, including unreachable rows. Its action is a literal-word query or a Boolean halt; its transition has a column for each of the four original replies. Every nominal decoded cache has distinct addresses. Cache truth and the exact read, hit and append laws are required on actual executions. These two requirements have different scopes. In the displayed formulas Report denotes an original address and raw reply pair, while Q(N), eZero(M) and Joint(N,M,tau,k) denote Q_N N, M.e0 and J_N N M tau k, respectively.

**Definition 1.1 (Finite literal words).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverFiniteTable.BoundedAddress`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverFiniteTable.BoundedAddress` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

BoundedAddress N is the subtype of original Boolean words belonging to Q_N N, equivalently of length at most N minus one. Mathlib List.finite_length_le supplies finiteness directly. The representation retains the words themselves and their ordered bits.

**Definition 1.2 (Finite ordered raw cache decorations).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverFiniteTable.NativeCache`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverFiniteTable.NativeCache` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

NativeCache N consists of lists of bounded literal words paired with original Reply values, with no repeated address. Finiteness follows by embedding these lists into Mathlib's finite type of duplicate-free lists over BoundedAddress N times Reply. Distinctness of addresses implies distinctness of pairs, but the reverse condition alone would permit two different reports at the same address and is insufficient.

**Definition 1.3 (Original ordered cache decoding).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverFiniteTable.decodeCache`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverFiniteTable.decodeCache` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

decodeCache erases only the bounded-word membership proofs. It preserves literal words, raw alpha, beta, branch and absent values, and chronological first-hit order. Its address list is duplicate-free.

**Definition 1.4 (Complete finite tables).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverFiniteTable.NativeTable`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverFiniteTable.NativeTable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

NativeTable N n has an action in Sum (BoundedAddress N) Bool at every Fin n row, all four raw transition successors, and an ordered NativeCache decoration at every row. Its type is finite as a subtype of a finite product of function types. There is no reachability restriction or source-dependent initial label.

**Definition 1.5 (Interpretation in the original observer contract).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverFiniteTable.tableObserver`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverFiniteTable.tableObserver` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a positive number n of rows, tableObserver assigns initial label zero, erases bounded-word proofs in the action column, retains the transition column, and decodes each cache decoration. It is an original Observer (Fin n). Absorbing halt semantics are supplied by the existing barStep; all installed nominal rows remain present.

**Definition 1.6 (Exactly the admissible finite tables).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverFiniteTable.lawfulTables`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverFiniteTable.lawfulTables` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

lawfulTables N n p filters the finite universal table set by Admissible N (tableObserver p T). This is the original contract: empty initial cache, raw cache truth and exact update at every actual prefix, correct finite termination on every original allowed source, and coarse action factorization on every raw history. The predicate is a mathematical specification; no effective real-price comparator or checker implementation is asserted.

**Definition 1.7 (Relabeling the whole nominal carrier).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverFiniteTable.relabel`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverFiniteTable.relabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any equivalence r from E to Fin n, relabel M r transports the initial configuration and every raw successor through r, and pulls actions and decoded caches back through its inverse. No row is removed or merged.

**Theorem 1.8 (Exact representation of every bounded observer).**

$$\forall E: Type, ([\operatorname{Fintype}\left(E\right)], \forall N: Nat, (\forall M: \operatorname{Observer}\left(E\right), (((\forall e: E, (\forall q: Address, ((\operatorname{action}\left(M, e\right) = \operatorname{inl}\left(q\right)) \implies (\operatorname{Member}\left(q, \operatorname{Q}\left(N\right)\right))))) \land (\forall e: E, (\forall a: Report, ((\operatorname{Member}\left(a, \operatorname{decoder}\left(M, e\right)\right)) \implies (\operatorname{Member}\left(\operatorname{fst}\left(a\right), \operatorname{Q}\left(N\right)\right)))))) \implies (\exists p: 0 < \operatorname{card}\left(E\right), (\exists r: \operatorname{Equiv}\left(E, \operatorname{Fin}\left(\operatorname{card}\left(E\right)\right)\right), (\exists T: \operatorname{NativeTable}\left(N, \operatorname{card}\left(E\right)\right), ((\operatorname{r}\left(\operatorname{eZero}\left(M\right)\right) = 0) \land (\operatorname{tableObserver}\left(p, T\right) = \operatorname{relabel}\left(M, r\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverFiniteTable.bounded_table_representation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose every query row of M uses Q_N N and every entry of every nominal cache uses Q_N N. No correctness, termination or price premise is needed. Enumerate the complete carrier using Mathlib Fintype.equivFin, then swap the image of the original initial configuration with zero. Install each bounded action, transported successor and packed original cache. Erasing the membership proofs recovers every original cache entry in order. The resulting native table observer equals the relabeled original observer as a complete record.

**Definition 1.9 (Exact actual and all-history correspondence).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverFiniteTable.RepresentationContract`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverFiniteTable.RepresentationContract` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

RepresentationContract records initial label zero; exact action, transition and decoded-cache correspondence at every nominal row; equivalence of actual prefixes and finite runs at every original source, arbitrary starting row and literal raw trace; equality of counterfactual actions and transported folded states on every raw history; exact sourcewise Fee and J_N for arbitrary real prices; and transport of Admissible. Histories include impossible, unreachable, inconsistent and wrong-address reports, as well as reports after halt. The finite-run equivalence gives equality of the complete terminating-trace predicates, so Fee equality follows even when a source has no terminating run. The price identity preserves the full carrier cardinality and the maximum over the same original allowed-source domain.

**Theorem 1.10 (A faithful complete table satisfies the representation contract).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverFiniteTable.representation_contract`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverFiniteTable.representation_contract` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Given an equivalence r between the complete carrier and Fin(card E), a native table T with initial label zero, and equality of tableObserver with relabel M r, every field of RepresentationContract holds. The supplier preserves exact actions, four-reply successors, ordered caches, actual prefixes and runs, all raw-history semantics, arbitrary real Fee and J_N, and admissibility. It is consumed both by competitor coverage and by the lawful pure-acquisition baseline table.

**Theorem 1.11 (Actual coverage of every original admissible competitor).**

$$\forall E: Type, ([\operatorname{Fintype}\left(E\right)], \forall N: Nat, (\forall M: \operatorname{Observer}\left(E\right), ((\operatorname{Admissible}\left(N, M\right)) \implies (\exists H: \operatorname{Observer}\left(E\right), (\exists p: 0 < \operatorname{card}\left(E\right), (\exists r: \operatorname{Equiv}\left(E, \operatorname{Fin}\left(\operatorname{card}\left(E\right)\right)\right), (\exists T: \operatorname{NativeTable}\left(N, \operatorname{card}\left(E\right)\right), ((\operatorname{NormalizationContract}\left(N, M, H\right)) \land ((\operatorname{RepresentationContract}\left(N, H, p, r, T\right)) \land ((\operatorname{Member}\left(T, \operatorname{lawfulTables}\left(N, \operatorname{card}\left(E\right), p\right)\right)) \land (\forall tau: Address \Rightarrow Real, ((\forall q: Address, (0 \leq \operatorname{tau}\left(q\right))) \implies ((\forall U: Source, ((\operatorname{Allowed}\left(N, U\right)) \implies (\operatorname{Fee}\left(\operatorname{tableObserver}\left(p, T\right), tau, U\right) \leq \operatorname{Fee}\left(M, tau, U\right)))) \land (\forall k: Real, ((0 < k) \implies (\operatorname{Joint}\left(N, \operatorname{tableObserver}\left(p, T\right), tau, k\right) \leq \operatorname{Joint}\left(N, M, tau, k\right)))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverFiniteTable.admissible_competitor_table_coverage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original admissible bounded observer M, native absent normalization supplies H on exactly the same E. Its all-row request condition bounds the action column. Its decoder identity filters every nominal cache to Q_N N, including unreachable rows; the original Observer already requires address distinctness on every nominal row. Thus H satisfies both representation premises. The constructed table has exactly card E rows, initial label zero, and a RepresentationContract with H, and belongs to lawfulTables at that cardinality.

Induction on actual runs and prefixes transports the same raw requests and reports under relabeling. The existing List.foldl_hom transports arbitrary response words from the conjugacy of the absorbing steps. This proves the representation contract and transports original admissibility. Normalization supplies ordered trace deletion and exact projected caches; relabeling thereafter changes only row labels. For every nonnegative literal address price, each sourcewise table fee is at most the fee of M, and the joint price is at most that of M for every strictly positive state price.

The table family is finite for each fixed nominal cardinality and covers every normalized competitor of that cardinality by construction. The complete joint-price application below uses this coverage conclusion, the existing pure-acquisition baseline and exact finite checks. Neither the baseline nor the price cutoff is a premise of the coverage theorem.

Fix N at least one, arbitrary real literal-address prices tau(q) at least zero and state price k strictly positive. All original competitors are the existing Observer E with arbitrary universe-polymorphic finite full nominal E and Admissible N M. Their queries may use every original word, and their raw caches and histories retain order, repeats and impossible reports. No all-source Strategy hypothesis is added. allowedSources_exact identifies the finite source enumeration with every original tree of leaf count at most N. Partitioning this class by leaf count j and alpha count a, the existing GenealogicalFiberTransport.result gives Cat(j-1) times choose(j,a) in each composition fiber; summing choose(j,a) gives d(N)=sum(j=1..N) Cat(j-1)*2^j. The list-to-tuple equivalence partitions literal bounded words by lengths zero through N-1; the finite geometric sum gives a(N)=2^N-1. The original subtree_leaf_count and outside_Q_N_absent supply node containment and raw absent outside that set. The bounded comb-leaf realization in source38.40 is context and is not needed as a premise of this optimization.

For a=card(BoundedAddress N), a chronological address-distinct cache of length j corresponds bijectively to an embedding Fin j into BoundedAddress N and an arbitrary function Fin j to the four original Reply values. The map is List.ofFn of the address/report pairs; its inverse reads the original list positions. No raw cache is discarded for being unreachable or untruthful on a source. Mathlib card_embedding_eq, card_fun, card_sigma and descFactorial_eq_div give exactly gamma(a)=sum(j=0..a) a!/(a-j)!*4^j. In particular gamma(0)=1, gamma(1)=5 and gamma(2)=41. NativeTable is exactly the product of its three full field functions. There are (a+2)^n action columns, (n^4)^n four-successor columns and gamma(a)^n cache columns. Thus its raw cardinality equals [(a+2)*n^4*gamma(a)]^n, which supplies the original upper bound. Halt successor junk remains in this raw enumeration and is absorbed by barStep.

The two acceptance checks stay separate. ActualObserverFiniteChecks.sourceCheck_iff characterizes the n-row source-orbit test without preassuming Legal: initial decoder empty, a correct finiteDecision halt before n, and raw truth and exact queryReply/cacheUpdate equality at every row of that orbit window, including the absorbing terminal row. Apply it to every allowedSources member. For the independent all-history check enumerate finite subsets R of the full E times E, accepting when R contains (e0,e0), is closed under every pair of raw replies with equal coarse image through the original absorbing barStep, and has equal actions at every member. Its acceptance predicate uses only finite row data. The frozen pairReach_iff_equal_coarse_response_words characterization and Mathlib List.rel_foldl propagate the closed certificate along equal-coarse words and prove soundness; completeness uses the generated finite pair set as a mathematical witness. PairReach is never an oracle in acceptance. The existing pairActionInvariant_iff_allHistoryFactorization converts this certificate exactly to all-history factorization. Combining the tests retains precisely lawfulTables, without a global acyclicity condition, cache-truth pruning of pairs or a coarse cache comparison.

Take the unchanged pureObserver N p. Its full nominal cardinality is s0=nominalCard N=1+sum(g in coarsePrefixes N)2^noneCount(g), including every compatible ghost cache lift and the absorbing sink. pure_node_fee charges exactly the same source actual nodes; pure_joint_price gives its achieved B=k*s0+nodeMax(N,p,tau), with an allowed original source attaining nodeMax. lawfulPureTable is a same-cardinality original native table with initial zero and the complete representation contract. Nonnegative sums give nodeMax at least zero and B strictly positive. Let K be the natural floor of B/k; nonnegativity makes this the same integer floor. Nat.le_floor gives s0 at most K. For every original observer with card E greater than K, Nat.floor_lt gives k*card E greater than B and fee nonnegativity gives J_N(M) greater than B.

Form the finite dependent pool of all pairs (n,T) with 1 at most n at most K and T in precisely lawfulTables N n. Price each candidate by its original J_N, preserving the maximum over the same original sources and each source chronological paid-address set. The pure table belongs to this pool and has price B, so the pool is nonempty. Finset.exists_min_image selects an actual table Tstar with the least pool price, at most B. For an arbitrary original admissible M, a carrier above K has price greater than B. Otherwise admissible_competitor_table_coverage supplies a lawful table at exactly card E whose price is at most J_N(M); pool minimality then gives J_N(Tstar) at most J_N(M). Tstar is itself an original admissible observer. The minimum therefore is attained in the original class, not only in a representation of candidate costs.

The unrestricted price set consists of all real J_N values of arbitrary original admissible Observer(Fin n), for every positive natural n, with unrestricted word actions and raw caches before normalization. Every arbitrary finite original E has exactly its price in this set by full-carrier relabel, relabel_admissible and relabel_fee; no reachable-state quotient or bounded catalogue defines this set. The selected Tstar belongs to it and lower-bounds it. IsLeast.csInf_eq proves that its literal real sInf equals the min of the finite lawful pool price image. The simultaneous universal inequality over every E:Type u makes the carrier presentation immaterial. These are applications of the existing normalization, representation, pure-compiler and pinned counting/order suppliers, together with the new source-check reflection; no separate count, cutoff or optimizer theorem is installed.

The result is mathematical finite attainment for arbitrary nonnegative real prices. It supplies no effective real comparator or efficiency bound, no physical memory or energy optimum, and no freedom to combine separately attainable state and address minima or exchange the same-source maximum with a sum. Zero address prices and integral B/k are included. Zero state price, negative address prices and additional priced resources are outside this argument. The general prescribed-route/prototype exact-trace compiler remains a separate contract.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverFiniteTable.BoundedAddress`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverFiniteTable.NativeCache`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverFiniteTable.NativeTable`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverFiniteTable.RepresentationContract`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverFiniteTable.admissible_competitor_table_coverage`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverFiniteTable.bounded_table_representation`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverFiniteTable.decodeCache`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverFiniteTable.lawfulTables`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverFiniteTable.relabel`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverFiniteTable.representation_contract`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverFiniteTable.tableObserver`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization](ActualObserverAbsorbingNormalization.md)
