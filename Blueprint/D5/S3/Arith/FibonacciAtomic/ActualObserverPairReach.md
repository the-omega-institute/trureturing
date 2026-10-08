# Absorbing Paired Histories and Coarse Action Factorization

## Abstract

The least absorbing paired response relation is characterized by equal coarse words and exactly characterizes coarse action factorization on every finite raw history.

M is any complete finite nominal observer, with initial row e0 and action in Sum Address Bool. The existing barStep follows the raw transition at a query row and fixes a halt row for every reply. responseState folds this absorbing step from a specified row; historyAction folds the replies from e0 and returns the resulting action. No source, cache truth, legal execution, termination, fuel or acyclicity assumption is imposed.

**Definition 1.1 (Least synchronized raw-response relation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualObserverPairReach.PairReach`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualObserverPairReach.PairReach` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

PairReach starts at (e0,e0). From any generated pair (e,f), every raw pair (y,z) with kappa(y)=kappa(z) generates (barStep(M,e,y),barStep(M,f,z)). All four replies remain available, and absent and branch may be paired. Edges remain available after either component has halted.

**Definition 1.2 (Paired action equality).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualObserverPairReach.pairActionInvariant`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualObserverPairReach.pairActionInvariant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At every generated pair the two actions agree. This concerns action equality rather than state equality.

**Definition 1.3 (Coarse response words).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ActualObserverPairReach.coarseResponseWord`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ActualObserverPairReach.coarseResponseWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Map the existing kappa over a raw reply word. Alpha and beta retain their distinct Boolean leaf labels; absent and branch both map to none. Address labels are not part of a response word.

**Theorem 1.4 (Equal-coarse words extend a generated pair).**

$$\forall E: Type, ([\operatorname{Fintype}\left(E\right)], \forall M: \operatorname{Observer}\left(E\right), (\forall e, f: E, (\forall w, v: \operatorname{List}\left(Reply\right), (((\operatorname{PairReach}\left(M, e, f\right)) \land (\operatorname{map}\left(kappa, w\right) = \operatorname{map}\left(kappa, v\right))) \implies (\operatorname{PairReach}\left(M, \operatorname{responseState}\left(M, e, w\right), \operatorname{responseState}\left(M, f, v\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ActualObserverPairReach.pairReach_response_words` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any generated starting pair, folding any two finite raw words with equal coarse images yields another generated pair. The existing list map and equality lemmas turn equal coarse images into Forall2 of the raw words with relation kappa(y)=kappa(z). Mathlib List.rel_foldl then applies directly with state relation PairReach, both folds barStep, the generating step as relation closure and the starting pair as initial premise. The same statement applies to words continuing beyond a halt.

**Theorem 1.5 (Exact equal-coarse response-word characterization).**

$$\forall E: Type, ([\operatorname{Fintype}\left(E\right)], \forall M: \operatorname{Observer}\left(E\right), (\forall e, f: E, ((\operatorname{PairReach}\left(M, e, f\right)) \iff (\exists w, v: \operatorname{List}\left(Reply\right), ((\operatorname{responseState}\left(M, \operatorname{e0}\left(M\right), w\right) = e) \land ((\operatorname{responseState}\left(M, \operatorname{e0}\left(M\right), v\right) = f) \land (\operatorname{map}\left(kappa, w\right) = \operatorname{map}\left(kappa, v\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ActualObserverPairReach.pairReach_iff_equal_coarse_response_words` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A generated pair is exactly a pair of folds from e0 of two finite raw words having equal coarse images. Induction on the generated relation appends the edge replies to the two words. In the reverse direction, the equal-coarse word extension applied to the initial pair constructs the required pair. Raw words need not be equal, and their final rows need not be equal.

**Theorem 1.6 (Exact all-history factorization with absorbing stops).**

$$\forall E: Type, ([\operatorname{Fintype}\left(E\right)], \forall M: \operatorname{Observer}\left(E\right), ((\operatorname{pairActionInvariant}\left(M\right)) \iff (\operatorname{FactorsThrough}\left(\operatorname{historyAction}\left(M\right), kappa_{hist}\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ActualObserverPairReach.pairActionInvariant_iff_allHistoryFactorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Paired action equality holds exactly when Function.FactorsThrough(historyAction(M),kappa_hist) holds. FactorsThrough means equal actions whenever the complete coarse histories agree. The existing kappa_hist retains addresses, order and repetitions. Its domain is every finite RawHistory, including unreachable, impossible, wrong-address, duplicate and raw-inconsistent labels.

Projecting equal coarse histories to their replies supplies equal-coarse response words, so the characterization gives the forward implication. Conversely, encode the two response words with the same fixed empty literal address at every position. Their coarse histories agree, and all-history factorization gives action equality at the represented pair. No actual-source condition restricts these encodings. Absorbing barStep permits arbitrary replies after either halt. These statements concern the original observer and assert no transformed execution, cache projection or cost bound.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualObserverPairReach.PairReach`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualObserverPairReach.coarseResponseWord`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualObserverPairReach.pairActionInvariant`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualObserverPairReach.pairActionInvariant_iff_allHistoryFactorization`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualObserverPairReach.pairReach_iff_equal_coarse_response_words`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ActualObserverPairReach.pairReach_response_words`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualFiniteObserverAbsentElimination](ActualFiniteObserverAbsentElimination.md)
