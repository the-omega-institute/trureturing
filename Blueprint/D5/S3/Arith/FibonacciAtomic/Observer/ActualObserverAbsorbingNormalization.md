# Full Nominal Absorbing Absent Normalization

## Abstract

Static absent elimination preserves every nominal row, exactly filters actual ordered reports and caches, preserves all-history coarse action factorization, and dominates the original attained joint price.

Sources are the original nonempty ordered FreeMagma Bool trees. Allowed(N,U) means that U has at most N leaves, with N at least one. Every finite Boolean word remains a permitted address. Q_N consists of words of length at most N minus one. The four raw replies are alpha, beta, branch and absent; kappa identifies only branch with absent. Positive(U) is the original third-substitution image predicate. The immutable source is the same throughout each execution.

**Definition 1.1 (Ordered literal projection).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.project`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.project` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

project(N,h) filters h by membership of its literal address in Q_N. It retains the original raw replies, order and every repetition. The same operation is used on traces and on the installed ordered first-occurrence caches.

**Definition 1.2 (Retained nominal rows).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.retained`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.retained` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A row is retained exactly when its action is a Boolean halt or a query at an address in Q_N.

**Definition 1.3 (Static absent successor).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.absentStep`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.absentStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

absentStep fixes every retained row and takes the original raw absent transition at every removed query row. It uses the installed table and N, without a source argument.

**Definition 1.4 (Finite static first-exit scan).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.scan`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.scan` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

scan(N,M,n,e) tests the first n rows of the static absent orbit, starting with e. It returns the first retained row, or none if the tested segment has no retained row.

**Definition 1.5 (Complete nominal first-exit table).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.skip`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.skip` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

skip scans exactly card(E) rows from each nominal e. The finite deterministic orbit bound ensures that every retained exit, if any exists, is found in this window. Thus none means that no finite iterate is retained, including at unreachable cyclic rows.

**Definition 1.6 (Independent native observer table).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.normalized`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.normalized` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

normalized(N,M) is an Observer on exactly the original complete E with the same e0. Its decoder at every nominal e is literally project(N,M.decoder(e)), preserving address distinctness. At an entry with skip(e)=some s, its action is M.action(s) and its raw reply successor is M.transition(s,y). If skip(e)=none, its action is Halt(false) and every successor is e. Halt rows are interpreted absorbingly by the existing barStep. The static tables introduce no execution-time counter, source label, history argument or jump storage.

**Theorem 1.7 (Exact execution from every old actual prefix).**

$$\forall E: Type, ([\operatorname{Fintype}\left(E\right)], \forall N: Nat, (\forall M: \operatorname{Observer}\left(E\right), (\forall U: Source, (\forall e, f: E, (\forall h, t: RawHistory, (\forall b: Bool, (((\operatorname{Allowed}\left(N, U\right)) \land (\operatorname{Legal}\left(M, U\right)) \land (\operatorname{ActualPrefix}\left(M, U, e, h\right)) \land (\operatorname{Run}\left(M, U, e, t, f, b\right))) \implies (\exists g: E, ((\operatorname{Run}\left(\operatorname{normalized}\left(N, M\right), U, e, \operatorname{project}\left(N, t\right), g, b\right)) \land (\operatorname{skip}\left(N, M, g\right) = \operatorname{some}\left(f\right)) \land (\operatorname{project}\left(N, \operatorname{decoder}\left(M, g\right)\right) = \operatorname{project}\left(N, \operatorname{decoder}\left(M, f\right)\right)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.normalize_run_from_actual_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every allowed original U, every Legal old observer, every actual old prefix ending at e and every old terminating suffix t from e, the independently installed normalized table has a native Run with precisely project(N,t), the same output bit, and final entry g with skip(g)=some f. Its decoded cache equals the ordered projection of the old final cache. The final entry g need not equal the old halt f. A removed request, including a cache hit, supplies raw absent by the original same-source cache truth and outside-address theorem. Filtering its exact cache update leaves the retained cache unchanged. A retained request has the same raw cached reply after projection. Induction constructs the new Run using its own query and halt constructors.

**Theorem 1.8 (Unrestricted paired-history transport).**

$$\forall E: Type, ([\operatorname{Fintype}\left(E\right)], \forall N: Nat, (\forall M: \operatorname{Observer}\left(E\right), ((\operatorname{FactorsThrough}\left(\operatorname{historyAction}\left(M\right), kappa_{hist}\right)) \implies ((\forall e, f: E, ((\operatorname{PairReach}\left(\operatorname{normalized}\left(N, M\right), e, f\right)) \implies (\operatorname{PairReach}\left(M, e, f\right)))) \land (\operatorname{FactorsThrough}\left(\operatorname{historyAction}\left(\operatorname{normalized}\left(N, M\right)\right), kappa_{hist}\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.normalized_pair_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume only the old all-history FactorsThrough condition. Every pair generated by the normalized observer is generated by the old observer, and the normalized action also factors through kappa_hist on all finite raw histories. Old related rows have equal literal actions; simultaneous raw absent steps through removed queries remain related. Their first retained rows are related, or both scans have no exit. Retained raw reply pairs use the original PairReach step for every pair with equal kappa; normalized halts absorb at their entry rows. Impossible, raw-inconsistent, repeated, wrong-address and posthalt histories remain in scope. No equality between the old action on an arbitrary raw history and the new action on its filtered history is asserted.

**Definition 1.9 (Once-per-address real charge).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.charge`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.charge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

charge(tau,t) is the sum of tau(q) over the existing paid(t), the finite set of distinct literal addresses in t. Repeated reports and cached hits remain in the trace but do not incur a second address charge.

**Definition 1.10 (Native source execution fee).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.Fee`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.Fee` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a terminating initial Run, Fee(M,tau,U) is charge(tau,t) on its unique trace. Run determinism makes this independent of the selected existence witness. Its default zero is used only when no terminating run exists; every allowed source of an Admissible observer has such a run.

**Definition 1.11 (Exact original finite source domain).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.allowedSources`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.allowedSources` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

allowedSources(N) filters the existing boundedSources(N) enumeration by Allowed(N). The composition fibers and their existing finite instances show that every original tree with at most N leaves occurs; membership is equivalent to Allowed(N,U). Both labels and every ordered shape are retained, without a supplied coverage premise.

**Definition 1.12 (Attained worst-source fee).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.maxFee`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.maxFee` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

maxFee(N,M,tau) is the finite maximum of Fee over allowedSources(N), with default zero only for an empty domain. For N at least one, the domain contains a one-leaf source. Every allowed source fee is bounded above by this maximum, and a source in that same domain attains it.

**Definition 1.13 (Full nominal joint price).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.J_N`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.J_N` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

J_N(N,M,tau,c) equals c times card(E) plus maxFee(N,M,tau). It charges every nominal configuration, including unreachable rows and cycles. The domain and each source are the original ones; there is no interchange of maximization with a per-address sum.

**Theorem 1.14 (Exact bounded source membership).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.allowedSources_exact`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.allowedSources_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every N and original U, U belongs to allowedSources N if and only if Allowed N U. The composition-fiber enumeration covers every original shape and label under the same leaf budget.

**Theorem 1.15 (Positive budget has an original source).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.allowedSources_nonempty`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.allowedSources_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For N at least one, allowedSources N is nonempty; the original true-labelled singleton tree supplies a member.

**Theorem 1.16 (Fee of any original terminating run).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.fee_run`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.fee_run` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any original Observer M, real address price tau, source U and initial Run with trace t, Fee M tau U equals charge tau t. Original finite-run determinism identifies this run with the fee's selected termination witness.

**Theorem 1.17 (Same-domain maximum bound and attainment).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.maximum_exact`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.maximum_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For N at least one and any original M and real tau, every allowed source fee is at most maxFee N M tau, and some original allowed source attains exactly this maximum. Nonnegative prices and admissibility are not required for this finite maximum identity.

**Definition 1.18 (Complete same-carrier normalization contract).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.NormalizationContract`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.NormalizationContract` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The contract requires the same initial row; an exact first-exit specification on every nominal row, with a first retained index less than card(E) and no earlier retained index; and the absorbing Halt(false) fallback at every no-exit row. Every nominal decoder is the literal ordered filter and a sublist of the old decoder. Every installed query belongs to Q_N. The new observer is Admissible, so every allowed actual prefix has an empty initial cache, raw same-source truth, exact hit or append update, correct finite termination and all-history coarse factorization.

The contract gives both prefix directions. Every old actual prefix h at e has a new prefix project(N,h) at g with skip(g)=skip(e) and new decoder equal to the projection of M.decoder(e). Every new actual prefix at entry e lifts to an old actual prefix at that same entry, whose projection is the new history. Every old initial Run t to f with bit b yields a new initial Run project(N,t) to g with the same b, skip(g)=some f and the projected final cache; it also has t.length less than card(E). Conversely every new initial Run s to g with bit b has an old Run t to f with that same b, s=project(N,t), skip(g)=some f and the same projected final cache. These are actual-source relations, not arbitrary raw-history cache identities.

The contract also transports every unrestricted new PairReach into old PairReach and states exact allowedSources membership. For every real address price tau with tau(q) at least zero, it gives Fee(new,tau,U) at most Fee(old,tau,U) for every allowed U, an allowed source attaining each of the old and new maxima, and J_N(new) at most J_N(old) for every strictly positive nominal price c. Zero address prices are included. The paid set of a filtered trace is exactly the old paid set restricted to Q_N; nonnegative finite-sum domination proves the sourcewise inequality. Attainment on the exact finite original source domain then proves the joint inequality.

**Theorem 1.19 (Complete normalization for every original competitor).**

$$\forall E: Type, ([\operatorname{Fintype}\left(E\right)], \forall N: Nat, (\forall M: \operatorname{Observer}\left(E\right), ((\operatorname{Admissible}\left(N, M\right)) \implies (\exists H: \operatorname{Observer}\left(E\right), ((H = \operatorname{normalized}\left(N, M\right)) \land (\operatorname{NormalizationContract}\left(N, M, H\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.absent_normalization_contract` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every original Admissible observer has the specified normalized Observer on the same E satisfying all clauses of NormalizationContract. The two prefix constructions establish legality at every allowed actual prefix. Native execution simulation preserves termination and the original Positive output. Universal pair transport supplies the separate all-history condition. The existing finite orbit theorem is applied both to the static absent successor and to the source-specific absorbing successor; a constructor induction identifies an old Run with that iterate and its first halt. No additional uniform fuel assumption is required. This is a redesign theorem: it does not preserve the removed requests of a fixed exact-trace compiler, assert equality to an original policy on every impossible history, establish the finite table minimum, or price address length, synthesis, elapsed time, physical memory or communication.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.Fee`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.J_N`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.NormalizationContract`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.absentStep`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.absent_normalization_contract`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.allowedSources`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.allowedSources_exact`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.allowedSources_nonempty`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.charge`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.fee_run`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.maxFee`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.maximum_exact`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.normalize_run_from_actual_prefix`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.normalized`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.normalized_pair_transport`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.project`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.retained`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.scan`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization.skip`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverPairReach](ActualObserverPairReach.md)
- Dependency: [D5/S3/ObserverMemory/Prediction/FiniteOrbitPeriodBound](../../../ObserverMemory/Prediction/FiniteOrbitPeriodBound.md)
