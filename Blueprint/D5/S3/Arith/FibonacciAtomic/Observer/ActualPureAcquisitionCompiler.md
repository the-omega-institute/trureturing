# Finite Pure Acquisition and Exact Node Baseline

## Abstract

A finite original observer preserves pure acquisition on every bounded source, all-history coarse control, every nominal cache lift and the exact node-fee baseline.

The source, address, four raw replies, coarse quotient, acquisition policy, acquisition trace, finiteDecision and nodes are the original actual-tree objects. Allowed N U is the exact original leaf-budget class. For every N at least one, pureObserver inhabits the existing Observer contract with no source argument. Its actual runs use the existing Run, ActualPrefix, Legal and Admissible relations. In formulas M(N,p) denotes pureObserver N p, Trace(U) denotes acquisitionTrace [] U, nodeSet(U) denotes (nodes U).toFinset, eZero denotes the initial configuration, kappaHist denotes kappa_hist, card denotes Fintype.card, and Joint denotes the original J_N. Natural cardinalities are cast to Real in the joint-price formula.

**Definition 1.1 (Finite coarse-prefix carrier).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.coarsePrefixes`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.coarsePrefixes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All coarse prefixes of all original allowed source acquisition traces, including terminal prefixes.

**Definition 1.2 (Coarse-prefix index).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.CoarseIndex`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.CoarseIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A CoarseIndex is a coarse prefix together with its membership witness.

**Definition 1.3 (Nominal row).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.PureRow`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.PureRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A nominal row is a coarse-prefix index together with one complete compatible raw-cache lift.

**Definition 1.4 (Rows plus sink).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.PureState`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.PureState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

PureState is the nominal row carrier plus one absorbing sink.

**Definition 1.5 (Finite pure carrier).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.pureStateFintype`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.pureStateFintype` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The pure carrier has a finite type instance obtained from the finite source prefix union and compatible fibers.

**Definition 1.6 (Exact nominal cardinality).**

$$\forall N: Nat, (\operatorname{nominalCard}\left(N\right) = 1+\sum_{g \in \operatorname{coarsePrefixes}\left(N\right)} 2^{\operatorname{noneCount}\left(g\right)})$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.nominalCard` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each installed coarse prefix has distinct addresses because the original trace is the nodes preorder without duplicates. Thus noneCount counts coarse-none first occurrences. Every compatible branch or absent lift contributes a separate nominal row, whether or not any source reaches it; the absorbing sink contributes one more. The exact sum, rather than an upper bound or a reachability quotient, is used for the state price.

**Theorem 1.7 (Exact full carrier count).**

$$\forall N: Nat, (\operatorname{card}\left(\operatorname{PureState}\left(N\right)\right) = \operatorname{nominalCard}\left(N\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.pureState_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite sigma carrier has exactly the compatible-fiber sum plus one sink. This exact count determines the nominal-state term of the joint price.

**Theorem 1.8 (Original preorder addresses).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.trace_addresses`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.trace_addresses` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original source U and address prefix u, mapping Sigma.fst over acquisitionTrace u U gives nodes U with u prepended to each address. Tree induction preserves the root, left and right preorder. At the root, its paid Finset is exactly (nodes U).toFinset; the addresses are duplicate-free.

**Definition 1.9 (Source-independent empty row).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.emptyRow`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.emptyRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For N at least one, the empty coarse prefix belongs to the carrier and its unique compatible cache is empty. The initial row depends only on N and its positivity proof, with no source, source size, oracle or externally readable history.

**Definition 1.10 (Original raw cache decoder).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.rowDecoder`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.rowDecoder` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Decode the compatible raw lift of the installed row. Addresses are distinct at every nominal row, including every ghost row.

**Definition 1.11 (Exact history row).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.rowOfHistory`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.rowOfHistory` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A raw history whose coarse projection belongs to coarsePrefixes is packed without changing its raw reports. This constructor is used in the proof of actual execution; the runtime has no history input.

**Definition 1.12 (Coarse-only installed action).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.pureAction`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.pureAction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At a row with coarse prefix g, the action is acquisitionPolicy (encodeHistory g). The sink action is Halt(false). Raw cache lifts cannot influence this action. A faithful finite table installs these values at all nominal rows.

**Definition 1.13 (Coarse-only row or sink selection).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.appendRow`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.appendRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

After query q and raw report y, append (q,kappa y) to the coarse prefix. Membership of that new prefix alone selects a row or the sink. A selected row packs the exact original cacheUpdate, which preserves the first raw value on a repeated hit. No raw contradiction test selects a control branch. In this pure acquisition carrier every retained extension has a fresh address; a repeated query extension is outside the prefix carrier regardless of its raw report.

**Definition 1.14 (Total raw transition).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.pureTransition`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.pureTransition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A query row takes appendRow; a halt row absorbs every raw response. The sink is absorbing. All four raw reply columns are defined at every installed row.

**Definition 1.15 (Original finite observer).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.pureObserver`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.pureObserver` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complete original Observer uses the empty row, coarse-only action, total raw transition and exact decoder. Its decoded_nodup field holds on every nominal configuration.

**Definition 1.16 (Coarse control projection).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.control`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.control` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

control returns the coarse-prefix index for a row and none for the sink. Raw cache lifts are forgotten.

**Theorem 1.17 (Unrestricted coarse factorization).**

$$\forall N: Nat, (\forall p: 1 \leq N, (\operatorname{FactorsThrough}\left(\operatorname{historyAction}\left(\operatorname{M}\left(N, p\right)\right), kappaHist\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.pure_all_history_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction on the original PairReach relation preserves equality of control for every pair of raw responses with equal kappa. Both action and row-versus-sink selection factor through this control. The frozen pairActionInvariant_iff_allHistoryFactorization criterion yields action factorization on all raw histories, including inconsistent reports, repeated or wrong address labels and reports after halt. No actual-source or cache-truth premise restricts this proof.

**Theorem 1.18 (Exact original acquisition run).**

$$\forall N: Nat, (\forall p: 1 \leq N, (\forall U: Source, ((\operatorname{Allowed}\left(N, U\right)) \implies (\exists f: \operatorname{PureState}\left(N\right), (\operatorname{Run}\left(\operatorname{M}\left(N, p\right), U, \operatorname{eZero}\left(\operatorname{M}\left(N, p\right)\right), \operatorname{Trace}\left(U\right), f, \operatorname{finiteDecision}\left(U\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.pure_acquisition_run` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every allowed original U, execute_to_run converts the original acquisition execution into an original Run with exactly acquisitionTrace [] U and finiteDecision U. Actual prefixes fix encodeHistory representatives, and truthful cache replies reproduce the same original source report. No query-all bounded-address baseline is substituted.

**Theorem 1.19 (Every actual prefix has the original cache).**

$$\forall N: Nat, (\forall p: 1 \leq N, (\forall U: Source, (\forall e: \operatorname{PureState}\left(N\right), (\forall h: RawHistory, (((\operatorname{Allowed}\left(N, U\right)) \land (\operatorname{ActualPrefix}\left(\operatorname{M}\left(N, p\right), U, e, h\right))) \implies ((\operatorname{IsPrefix}\left(h, \operatorname{Trace}\left(U\right)\right)) \land (\operatorname{decoder}\left(\operatorname{M}\left(N, p\right), e\right) = h) \land (\operatorname{CacheTruth}\left(h, U\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.pure_actual_prefix_cache` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every actual prefix h is a prefix of the exact original trace. Its decoded cache is literally h and is truthful on the same U. Pure acquisition has no repeated actual address, so this literal prefix equals its ordered first-occurrence cache. The proof retains a remaining original execute continuation at every prefix; the sink is never reached on an allowed source. Truth is asserted on actual prefixes, not on arbitrary ghost rows.

**Theorem 1.20 (Complete bounded admissibility).**

$$\forall N: Nat, (\forall p: 1 \leq N, (\operatorname{Admissible}\left(N, \operatorname{M}\left(N, p\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.pure_admissible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original Admissible contract follows from empty initial cache, actual-prefix truth and exact cacheUpdate, original finiteDecision correctness, exact finite acquisition runs and the separate unrestricted factorization theorem.

**Theorem 1.21 (Exact actual-node fee).**

$$\forall N: Nat, (\forall p: 1 \leq N, (\forall tau: Address \Rightarrow Real, (\forall U: Source, ((\operatorname{Allowed}\left(N, U\right)) \implies (\operatorname{Fee}\left(\operatorname{M}\left(N, p\right), tau, U\right) = \sum_{q \in \operatorname{nodeSet}\left(U\right)} \operatorname{tau}\left(q\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.pure_node_fee` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original fee_run and the exact paid address identity give Fee(M,tau,U) equal to the sum of tau over (nodes U).toFinset for every allowed source. This identity holds for arbitrary real address prices.

**Definition 1.22 (Attained original node maximum).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.nodeMax`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.nodeMax` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

nodeMax N p tau is the finite sup over the exact allowedSources N of the sum of tau over each source's original nodes. Its domain is nonempty for N at least one.

**Theorem 1.23 (Exact source38.10 baseline).**

$$\forall N: Nat, (\forall p: 1 \leq N, (\forall tau: Address \Rightarrow Real, (\forall c: Real, ((\operatorname{Joint}\left(N, \operatorname{M}\left(N, p\right), tau, c\right) = c \cdot \operatorname{nominalCard}\left(N\right)+\operatorname{nodeMax}\left(N, p, tau\right)) \land (\exists U: Source, ((\operatorname{Allowed}\left(N, U\right)) \land (\operatorname{nodeMax}\left(N, p, tau\right) = \sum_{q \in \operatorname{nodeSet}\left(U\right)} \operatorname{tau}\left(q\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.pure_joint_price` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original J_N of the compiled observer is c times its exact full nominal count plus nodeMax. An original allowed source attains that node maximum. Both statements hold for arbitrary real tau and c; later domination and cutoff arguments additionally require nonnegative tau and strictly positive c.

**Theorem 1.24 (Original node depth).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.nodes_length`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.nodes_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original source U and every literal q in nodes U, q.length + 1 is at most U.length. Each descent leaves a nonempty sibling subtree, so its path requires at least one additional leaf per level. This original node geometry supplies bounded-address membership for the pure table and the routed completion horizon.

**Definition 1.25 (Faithful lawful baseline table).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.lawfulPureTable`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.lawfulPureTable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every nominal query and cache address belongs to Q_N, established from original node geometry and the acquisition existence supplier. bounded_table_representation and representation_contract then provide a table with exactly card(PureState N) rows, initial label zero, complete raw transition and cache correspondence, exact actual Run and prefix correspondence, all-history semantics, and exact Fee and J_N. The table belongs to the existing lawfulTables at that full cardinality. No ghost row is removed.

For nonnegative tau and positive c, the existing ActualObserverFiniteTable application uses this exact lawful table as the baseline below K=floor(B/c), with B=c*nominalCard(N)+nodeMax(N,p,tau). Nonnegative node fees give nominalCard(N) at most K; the original full state fee excludes all larger carriers from improving B. The finite nonempty lawful-table pool then has an attained least price, and competitor coverage gives the unrestricted original infimum equality. This application preserves the same-source node maximum and all nominal ghost rows. It does not install a real comparator or any extra observer port. The general prescribed routed/prototype compiler remains separate from this pure-acquisition supplier.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.CoarseIndex`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.PureRow`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.PureState`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.appendRow`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.coarsePrefixes`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.control`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.emptyRow`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.lawfulPureTable`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.nodeMax`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.nodes_length`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.nominalCard`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.pureAction`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.pureObserver`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.pureStateFintype`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.pureState_card`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.pureTransition`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.pure_acquisition_run`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.pure_actual_prefix_cache`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.pure_admissible`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.pure_all_history_factorization`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.pure_joint_price`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.pure_node_fee`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.rowDecoder`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.rowOfHistory`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.trace_addresses`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualCoarseReadoutCompletion](../ActualCoarseReadoutCompletion.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/ActualAcquisitionCacheFiber](ActualAcquisitionCacheFiber.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverFiniteTable](ActualObserverFiniteTable.md)
