# Bounded Native Cache and Control Lower Bounds

## Abstract

Correctness on the original bounded source domain forces complete positive leaf acquisition, an exact decoded cache spectrum, and lower bounds on the full nominal observer carrier.

A source is an original nonempty ordered FreeMagma Bool tree. Allowed(N,U) means that its leaf count is at most N. Positive(U) means membership in the third iterate of the original substitution. An Observer has a finite complete nominal carrier E, initial row e0, source-independent actions and raw-response transitions, and a decoder whose cache addresses are distinct. Admissible(N,M) includes N at least one, correct finite termination for every original allowed source, exact truthful cache updates at every actual prefix, and coarse action factorization on all finite histories. Every finite Boolean word remains a permitted query, including absent addresses of arbitrary length.

**Definition 1.1 (Decoded chronological prefix values).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverBoundedLowerBounds.cachedVisits`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverBoundedLowerBounds.cachedVisits` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

cachedVisits(M,t) is the image of all indices from zero through length(t) under i mapped to decoder(historyState(M,t.take(i))). The external trace retains each literal address, raw reply and repetition. The observer receives only its current row and a raw response. Actual-prefix certificates identify these response folds with the actual configurations, including the initial empty cache and the terminal cache.

**Definition 1.2 (Positive original bounded sources).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverBoundedLowerBounds.positiveSources`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverBoundedLowerBounds.positiveSources` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

positiveSources(N) filters the exact allowedSources(N) enumeration by Positive. It counts distinct original trees, with every ordered shape and both labels, without identifying sources having the same partial observation. Write p_N for its cardinality.

**Theorem 1.3 (Exact actual-prefix cache spectrum).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverBoundedLowerBounds.prefix_cache_spectrum`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverBoundedLowerBounds.prefix_cache_spectrum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every M,U with Legal(M,U), every actual state e and raw prefix h, paid(decoder(M,e)) equals paid(h), card(cachedVisits(M,h)) equals card(paid(h))+1, and every cache in cachedVisits has paid support contained in paid(h). Repeats retain the ordered cache; each fresh address creates one distinct decoder value. The scope includes the empty prefix and terminal cache.

**Theorem 1.4 (Complete bounded-source lower bounds).**

$$\forall E: Type, ([\operatorname{Fintype}\left(E\right)], \forall N: Nat, (\forall M: \operatorname{Observer}\left(E\right), ((\operatorname{Admissible}\left(N, M\right)) \implies ((\forall U: Source, (((\operatorname{Allowed}\left(N, U\right)) \land (\operatorname{Positive}\left(U\right))) \implies (\forall t: RawHistory, (\forall f: E, (\forall b: Bool, ((\operatorname{Run}\left(M, U, \operatorname{e0}\left(M\right), t, f, b\right)) \implies ((\operatorname{toFinset}\left(\operatorname{leaves}\left(U\right)\right) \subseteq \operatorname{paid}\left(t\right)) \land (\operatorname{length}\left(U\right)+1 \leq \operatorname{card}\left(E\right)) \land (\forall tau: Address \to \mathbb{R}, ((\forall q: Address, (0 \leq \operatorname{tau}\left(q\right))) \implies (\sum_{q \in \operatorname{toFinset}\left(\operatorname{leaves}\left(U\right)\right)} \operatorname{tau}\left(q\right) \leq \operatorname{Fee}\left(M, tau, U\right))))))))))) \land (\forall U: Source, ((\operatorname{Allowed}\left(N, U\right)) \implies (\forall t: RawHistory, (\forall f: E, (\forall b: Bool, ((\operatorname{Run}\left(M, U, \operatorname{e0}\left(M\right), t, f, b\right)) \implies ((\operatorname{paid}\left(\operatorname{decoder}\left(M, f\right)\right) = \operatorname{paid}\left(t\right)) \land (\operatorname{card}\left(\operatorname{cachedVisits}\left(M, t\right)\right) = \operatorname{card}\left(\operatorname{paid}\left(t\right)\right)+1) \land (\forall i: Nat, ((i \leq \operatorname{length}\left(t\right)) \implies (\operatorname{ActualPrefix}\left(M, U, \operatorname{historyState}\left(M, \operatorname{take}\left(t, i\right)\right), \operatorname{take}\left(t, i\right)\right))))))))))) \land ((0 < \operatorname{card}\left(\operatorname{positiveSources}\left(N\right)\right)) \implies (\operatorname{card}\left(\operatorname{positiveSources}\left(N\right)\right)+2 \leq \operatorname{card}\left(E\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverBoundedLowerBounds.bounded_cache_control_lower_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive allowed U and every native initial Run with trace t, all leaves of U belong to paid(t), the finite set of distinct literal requested addresses. The full nominal carrier satisfies length(U)+1 at most card(E). For every real address price tau that is nonnegative at every address, the leaf sum is at most Fee(M,tau,U) on that same U. Zero prices are permitted. All nominal rows, including unreachable rows, contribute to card(E).

For every allowed U and every actual terminating Run, paid(decoder(f)) equals paid(t). Exactly card(paid(t))+1 distinct decoded caches occur along its chronological prefixes, and each prefix fold has an ActualPrefix certificate. Repeated requests can change the row but preserve the full cache. Each first acquisition appends one truthful raw entry and creates a new cache value. Thus k distinct acquired addresses give exactly k+1 cache values, including empty and terminal values; absent addresses also count.

If p_N is positive, card(E) is at least p_N+2. Different positive sources require different true terminal rows: a shared decoder is truthful for both sources, contains all labelled leaves of the first, and the original leaf rigidity forces the sources to agree. A negative singleton requires a separate false terminal row. Since both answers occur, the source-independent initial row cannot halt and supplies a further row. The positive-count condition is essential; the one- and two-leaf domains contain no positive source.

To force a positive leaf request, flip an omitted leaf. The flip preserves the original leaf budget and is negative. All paid source readouts agree, so induction on the native Run replays the exact ordered trace, final nominal row and output bit. Bounded correctness then contradicts the opposite source truth values. This argument uses no all-source Strategy. Induction on actual prefixes proves cache separation using the exact hit-or-append law. Finite image cardinality and nonnegative sum domination give the state and fee bounds.

The conclusions concern decoded caches and nominal finite control, not physical memory, runtime, communication or table-description cost. They establish no minimum joint price, price cutoff or gamma formula.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverBoundedLowerBounds.bounded_cache_control_lower_bounds`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverBoundedLowerBounds.cachedVisits`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverBoundedLowerBounds.positiveSources`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverBoundedLowerBounds.prefix_cache_spectrum`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization](ActualObserverAbsorbingNormalization.md)
