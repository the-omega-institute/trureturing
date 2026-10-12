# Original Marked Exact Tables and Attained Minima

## Abstract

Original actual phase observations decorate every exact competitor on its unchanged nominal carrier. Primitive finite checks and full competitor coverage give common attained state and fixed-trace price minima.

Fix a finite prototype family F indexed by Fin(m), an arbitrary decoder of the complete coarse routing history, a finite passive route p, a positive source budget N and a Strategy pi. The protocol endpoint retains the exact identity pi.policy(h)=controllerPolicy(compileRaw(F,decode,p,[]),encodeHistory(kappa_hist(h))). Prototype positivity is needed when pi is constructed by completion_contract; it is not an extra hypothesis of generic actual-prefix replay or marking. Empty prototype families, duplicate selected indices, repeated requests and arbitrary literal address lengths remain permitted.

**Definition 1.1 (Finite original phase alphabet).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactMarkedTables.PhaseMark`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactMarkedTables.PhaseMark` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A mark is a member of insert(malformed,phaseAlphabet(F,decode,p,N,pi)). phaseAlphabet is the existing finite image of the original routePhase label over strategyPrefixes. No Fintype on the entire unbounded PhaseLabel type is assumed. Malformed is the fixed decoration for a row with no actual witness.

**Definition 1.2 (Original actual-only observation contract).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactMarkedTables.OriginalMarks`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactMarkedTables.OriginalMarks` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every allowed source U and every native ActualPrefix(M,U,e,h), the installed mark at e equals the first component of routePhase(F,decode,p,[],kappa_hist(h)). No equality is required for arbitrary-history labels, and no cache or mark equality is required on PairReach.

**Theorem 1.3 (Every exact competitor has original marks).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactMarkedTables.same_carrier_original_marking`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactMarkedTables.same_carrier_original_marking` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite full carrier E and observer M with Admissible(N,M) and ExactTraces(N,pi,M), there exists mark:E to PhaseMark satisfying OriginalMarks. Choose an allowed actual history at an actually visited row and malformed otherwise. Native cross-source rigidity proves that this choice agrees with every other actual witness at the row. Prefix-tail splitting and strategy_prefix_mem place the chosen concrete parser value in phaseAlphabet. E, its initial row, actions, transitions and ordered decoder are unchanged. A counterfactual word reaching an actual row sees that row's installed actual mark; its own parser label need not agree.

**Definition 1.4 (Primitive prescribed-prefix row guards).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactMarkedTables.PrefixCertificate`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactMarkedTables.PrefixCertificate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For raw trace t and terminal bit b, inspect every j in Fin(length(t)+1), including zero and length(t), and require decoder(historyState(M,t.take(j)))=firstRaw(t.take(j)). For every j in Fin(length(t)), let a=t[j] and e=historyState(M,t.take(j)); require action(e)=Query(a.address), queryReply(decoder(e),a.address,U)=a.rawReply, historyState(M,t.take(j+1))=transition(e,a.rawReply), and the exact cacheUpdate equality at that successor. At the full terminal prefix require action(historyState(M,t))=Halt(b). Every repeated logical report is retained, and the halt cache is checked.

**Definition 1.5 (Separate unrestricted finite pair certificate).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactMarkedTables.PairCertificate`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactMarkedTables.PairCertificate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

There exists a finite pair set containing (e0,e0), with equal actions on every included pair and closed under barStep for every pair of four-valued replies y,z with kappa(y)=kappa(z). This checks the independent all-history action law. Impossible replies, wrong-address words, post-halt absorption and contradictory cached hits are retained. The relation is never pruned using source, cache or phase feasibility.

**Definition 1.6 (Original exact finite certificate).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactMarkedTables.ExactCertificate`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactMarkedTables.ExactCertificate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

N is at least one; the independent PairCertificate holds; and for every U in the complete allowedSources(N) enumeration, sourceCheck(M,U)=true and PrefixCertificate holds for the prescribed terminal(pi,U) trace and bit. sourceCheck supplies original actual legality and correct termination. The additional primitive guards supply the prescribed trace. This does not decide Legal, Admissible or ExactTraces themselves.

**Theorem 1.7 (Finite guards are equivalent to native exact behavior).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactMarkedTables.prescribed_prefix_certificate_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactMarkedTables.prescribed_prefix_certificate_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every N,pi and M, ExactCertificate(N,pi,M) is equivalent to Admissible(N,M) together with ExactTraces(N,pi,M). The primitive successor guards construct actual prefixes of the prescribed trace by induction. sourceCheck supplies a terminating run; prefix_run_tail and the terminal halt guard force its tail after the prescribed prefix to be empty. Conversely the original bounded_cache_control_lower_bounds prefix supplier, actualPrefix_semantics and prefix_run_tail give every guard. PairCertificate is separately equivalent to all-history coarse action factorization.

**Definition 1.8 (Every prescribed prefix carries its original mark).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactMarkedTables.MarkCertificate`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactMarkedTables.MarkCertificate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every allowed source U and every j from zero through the full prescribed terminal length, the mark at historyState(M,terminal(pi,U).trace.take(j)) equals the concrete original routePhase label on the coarsened full prefix. With the exact native contract, these finite tests are equivalent to OriginalMarks on every actual prefix.

**Definition 1.9 (Full nominal literal support).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactMarkedTables.SupportedRows`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactMarkedTables.SupportedRows` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every nominal query address and every entry of every nominal decoded cache belongs to Q=prescribedSupport(N,pi). This includes rows unused by actual sources. W=supportWidth(Q) is only address packing, independently of the source budget N.

**Definition 1.10 (Retained unmarked native tables).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactMarkedTables.rawPool`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactMarkedTables.rawPool` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a positive n, retain NativeTable(W,n) exactly when SupportedRows(Q,tableObserver) and ExactCertificate(N,pi,tableObserver) hold. All nominal configurations remain present. The pool is a mathematical finite set; it is not lawfulTables(W), which would use the wrong source domain.

**Definition 1.11 (Retained originally marked native tables).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactMarkedTables.markedPool`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactMarkedTables.markedPool` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Retain pairs of an underlying rawPool table and a function from its full Fin(n) carrier into PhaseMark when every MarkCertificate guard holds. The unmarked version deletes only phase decoration and phase checking. No history-state or phase-state product is used.

**Theorem 1.12 (Equal feasibility at every nominal size).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactMarkedTables.raw_mem_iff_marked`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactMarkedTables.raw_mem_iff_marked` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every fixed original F,decode,p,N,pi, every positive n and NativeTable(W,n) T, T belongs to rawPool if and only if there exists a mark with (T,mark) in markedPool. The forward construction uses same_carrier_original_marking on T. Forgetting marks proves the reverse implication. This equivalence strengthens the separate marked and unmarked minima to equality.

**Theorem 1.13 (Complete coverage of original marked competitors).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactMarkedTables.marked_competitor_table_coverage`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactMarkedTables.marked_competitor_table_coverage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite E and every M,mark satisfying Admissible, ExactTraces and OriginalMarks, there exist positive card(E), a bijection r:E to Fin(card(E)), a NativeTable(W,card(E)) T and finite original labels with (T,labels) in markedPool. Every allowed ActualPrefix at r(e) is equivalent to the old prefix at e. At each old actual prefix, the table decoder and action agree with the old decoder and action, and labels(r(e)) equals the old mark. Existing exact_competitor_table_coverage preserves the complete nominal cardinality and supplies supported actions and caches. Transport original marks through r; labels outside the finite alphabet are defaulted only off actual visits. This covers every original competitor, rather than quotients of a chosen table.

**Definition 1.14 (Finite exact compiler cutoff).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactMarkedTables.feasibleSizes`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactMarkedTables.feasibleSizes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The subset of range(strategyStateCard(N,pi)+1) whose positive n has a nonempty rawPool. The exact compiler supplies a member at its full cardinality s. No redesign price cutoff or exhaustive enumeration execution is introduced.

**Definition 1.15 (Attained common prescribed address fee).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactMarkedTables.fixedTraceFee`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactMarkedTables.fixedTraceFee` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite maximum over the same allowedSources(N) of charge(tau,terminal(pi,U).trace), with charge summing tau over distinct paid addresses. It uses N for sources and retains every long or repeated prescribed report.

**Theorem 1.16 (Common attained original state and price minima).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactMarkedTables.original_exact_marked_attainment`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactMarkedTables.original_exact_marked_attainment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under positive N and the exact original policy binding, there exist k>0, a NativeTable(W,k) T and finite original marks such that k is at most strategyStateCard(N,pi), T is retained unmarked and (T,mark) is retained marked. For every original finite Carrier,M with Admissible and ExactTraces, k is at most card(Carrier), including competitors larger than the compiler cutoff. For every original U, terminal(pi,U) equals the original controllerOutcome. For every nonnegative real address price tau and strictly positive state price kappa, the witnessed table has price kappa*k+fixedTraceFee. Every original exact competitor has at least this price. Each allowed prescribed charge is at most fixedTraceFee, and one allowed source attains it. Take the least feasible raw size, construct its original marks and use full-cardinality marked coverage to obtain the final marked table. Its underlying table is also retained unmarked at the same k. Comparisons with arbitrary original competitors use the exact full-carrier coverage directly. Hence the original marked and unmarked state minima both equal k and both joint minima equal the displayed attained price.

Finite minimum extraction and fixed-fee arithmetic use Finset.min', fee_run and maximum_exact. Native replay and shared-state rigidity make the original marks well-defined without changing the carrier; the primitive prefix correspondence connects finite row guards to native execution. Marks and the underlying table share one actual witness, which attains both the state and joint price minima. Physical storage, address emission, description length and effective synthesis costs are outside J_N. Arbitrary real prices give mathematical attainment without an effective comparator.

The labels are exactly the already defined routePhase values. This endpoint does not prove that an acquisition label's local suffix is a fresh same-source prefix of acquisitionTrace, or return the first mismatch cut and fresh parent-branch/existence evidence. Those require a separate actual acquisition-cut theorem. Local parser resets alone do not discharge that provenance clause, and the persistent decoder remains firstRaw of the full global history. No claim of equality with pi on all counterfactual histories or counterfactual termination is made.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactMarkedTables.ExactCertificate`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactMarkedTables.MarkCertificate`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactMarkedTables.OriginalMarks`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactMarkedTables.PairCertificate`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactMarkedTables.PhaseMark`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactMarkedTables.PrefixCertificate`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactMarkedTables.SupportedRows`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactMarkedTables.feasibleSizes`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactMarkedTables.fixedTraceFee`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactMarkedTables.markedPool`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactMarkedTables.marked_competitor_table_coverage`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactMarkedTables.original_exact_marked_attainment`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactMarkedTables.prescribed_prefix_certificate_iff`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactMarkedTables.rawPool`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactMarkedTables.raw_mem_iff_marked`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualExactMarkedTables.same_carrier_original_marking`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionHorizon](ActualCompletionHorizon.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionPhaseReplay](ActualCompletionPhaseReplay.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverFiniteChecks](ActualObserverFiniteChecks.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverPrefixRigidity](ActualObserverPrefixRigidity.md)
