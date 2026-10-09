# Same-reset weighted factor dictionaries

## Abstract

The original equal-weight weak codebook has distinct factors in one lower-memory language, with exact reset overhead and a weighted limsup bound.

**Definition 1.1 (FactorDictionary).**

$$\forall X \in \operatorname{Set}\left(Int \to CuLetter\right), T \in Nat,\; \operatorname{FactorDictionary}\left(X, T\right) = \operatorname{Subtype}\left(\left(\left(\exists omega \in Int \to CuLetter,\; \operatorname{member}\left(omega, X\right) \land \operatorname{Occurs}\left(omega, w\right)\right) \land \operatorname{wordWeight}\left(w\right) = T\right)_{w \in \operatorname{List}\left(CuLetter\right)}\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetFactors.FactorDictionary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The dictionary contains every word of exact original weight T that occurs in a bilateral sequence of X. Occurrence retains a single sequence and one integer starting position; transient graph paths are not substituted.

**Definition 1.2 (factorCount).**

$$\forall X \in \operatorname{Set}\left(Int \to CuLetter\right), T \in Nat,\; \operatorname{factorCount}\left(X, T\right) = \operatorname{NatCard}\left(\operatorname{FactorDictionary}\left(X, T\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetFactors.factorCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The count is the natural cardinality of that entire factor dictionary, including the empty word at weight zero when the language is nonempty.

**Definition 1.3 (weightedFactorRate).**

$$\forall X \in \operatorname{Set}\left(Int \to CuLetter\right),\; \operatorname{weightedFactorRate}\left(X\right) = \operatorname{FilterLimsup}\left(\left(\operatorname{divide}\left(\operatorname{logb}\left(2, \operatorname{toReal}\left(\operatorname{max}\left(1, \operatorname{factorCount}\left(X, T\right)\right)\right)\right), \operatorname{toReal}\left(T\right)\right)\right)_{T \in Nat}, atTop\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetFactors.weightedFactorRate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The rate is the real upper limit over total actual weight T, with max(1,count) and total real division at T=0. It uses the original weights 20 and 6, rather than letter length.

**Definition 1.4 (resetFactor).**

$$\forall R \in Return, words \in \operatorname{List}\left(\operatorname{List}\left(Return\right)\right),\; \operatorname{resetFactor}\left(R, words\right) = \operatorname{flatten}\left(\operatorname{map}\left(\left(\operatorname{executionWord}\left(\operatorname{cons}\left(R, xs\right)\right)\right)_{xs \in \operatorname{List}\left(Return\right)}, words\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetFactors.resetFactor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every finite ordered choice receives the same original reset before its execution word. Flattening concatenates these words without prescribing a common letter length.

**Theorem 1.5 (word weight geometry).**

$$\left(\forall w \in \operatorname{List}\left(CuLetter\right), v \in \operatorname{List}\left(CuLetter\right),\; \operatorname{wordWeight}\left(\operatorname{append}\left(w, v\right)\right) = \operatorname{add}\left(\operatorname{wordWeight}\left(w\right), \operatorname{wordWeight}\left(v\right)\right)\right) \land \left(\left(\forall w \in \operatorname{List}\left(CuLetter\right),\; \operatorname{le}\left(\operatorname{length}\left(w\right), \operatorname{wordWeight}\left(w\right)\right)\right) \land \left(\forall w \in \operatorname{List}\left(CuLetter\right),\; \operatorname{wordWeight}\left(w\right) = 0 \Rightarrow w = \operatorname{nil}\left(\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetFactors.word_weight_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original letter weights are positive and additive. A zero-weight word is empty; letter length is bounded by its actual weight.

**Theorem 1.6 (factor dictionary bound).**

$$\forall X \in \operatorname{Set}\left(Int \to CuLetter\right), T \in Nat,\; \operatorname{Finite}\left(\operatorname{FactorDictionary}\left(X, T\right)\right) \land \operatorname{le}\left(\operatorname{factorCount}\left(X, T\right), \operatorname{power}\left(3, \operatorname{add}\left(T, 1\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetFactors.factor_dictionary_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every word of weight T has at most T letters. Its optional letters at the first T+1 indices determine it uniquely, giving a finite dictionary and the bound 3 to T+1.

**Theorem 1.7 (equal weight concatenation injective).**

$$\forall L \in Nat,\; \operatorname{lt}\left(0, L\right) \Rightarrow \operatorname{FunctionInjective}\left(\left(\operatorname{flatten}\left(\operatorname{map}\left(val, words\right)\right)\right)_{words \in \operatorname{List}\left(\operatorname{Subtype}\left(\left(\operatorname{wordWeight}\left(w\right) = L\right)_{w \in \operatorname{List}\left(CuLetter\right)}\right)\right)}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetFactors.equal_weight_concatenation_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At each common accumulated positive weight, prefix comparison recovers the next whole block. This proves unique parsing with variable block letter lengths; equality of weights never asserts equality of lengths.

**Theorem 1.8 (reset factor parser).**

$$\forall R \in Return, N \in Nat, p \in \operatorname{List}\left(Return\right) \to Prop,\; \operatorname{FunctionInjective}\left(\left(\operatorname{resetFactor}\left(R, \operatorname{map}\left(val, words\right)\right)\right)_{words \in \operatorname{List}\left(\operatorname{Subtype}\left(\left(\operatorname{apply}\left(p, xs\right) \land \operatorname{listWeight}\left(xs\right) = N\right)_{xs \in \operatorname{List}\left(Return\right)}\right)\right)}\right) \land \left(\forall words \in \operatorname{List}\left(\operatorname{Subtype}\left(\left(\operatorname{apply}\left(p, xs\right) \land \operatorname{listWeight}\left(xs\right) = N\right)_{xs \in \operatorname{List}\left(Return\right)}\right)\right),\; \operatorname{wordWeight}\left(\operatorname{resetFactor}\left(R, \operatorname{map}\left(val, words\right)\right)\right) = \operatorname{multiply}\left(\operatorname{length}\left(words\right), \operatorname{add}\left(\operatorname{add}\left(N, \operatorname{multiply}\left(20, \operatorname{r}\left(R\right)\right)\right), \operatorname{multiply}\left(6, \operatorname{m}\left(R\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetFactors.reset_factor_parser` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing complete execution-word parser identifies each original return list after the fixed reset is removed. Equal weighted cuts identify the ordered choices. No reset exponent restriction is needed here; the weight includes the actual r(R).

**Theorem 1.9 (tiled window occurs).**

$$\forall W \in Int \to \operatorname{List}\left(CuLetter\right), omega \in Int \to CuLetter, a \in Int, q \in Nat,\; \left(\left(\forall j \in Int,\; \operatorname{lt}\left(0, \operatorname{length}\left(\operatorname{apply}\left(W, j\right)\right)\right)\right) \land \left(\forall j \in Int, k \in \operatorname{Fin}\left(\operatorname{length}\left(\operatorname{apply}\left(W, j\right)\right)\right),\; \operatorname{apply}\left(omega, \operatorname{add}\left(\operatorname{blockCut}\left(W, j\right), \operatorname{toInt}\left(k\right)\right)\right) = \operatorname{getElem}\left(\operatorname{apply}\left(W, j\right), k\right)\right)\right) \Rightarrow \left(\forall k \in \operatorname{Fin}\left(\operatorname{length}\left(\operatorname{blockWindow}\left(W, a, q\right)\right)\right),\; \operatorname{apply}\left(omega, \operatorname{add}\left(\operatorname{blockCut}\left(W, a\right), \operatorname{toInt}\left(k\right)\right)\right) = \operatorname{getElem}\left(\operatorname{blockWindow}\left(W, a, q\right), k\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetFactors.tiled_window_occurs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The indexed tiling supplies every letter of each consecutive finite block window at its original integer cut. All blocks, including the negative-index past, belong to the same bilateral realization.

**Theorem 1.10 (choice window ofFn).**

$$\forall V \in Type, choices \in Int \to V, a \in Int, q \in Nat,\; \operatorname{choiceWindow}\left(choices, a, q\right) = \operatorname{ofFn}\left(\left(\operatorname{apply}\left(choices, \operatorname{add}\left(a, \operatorname{toInt}\left(i\right)\right)\right)\right)_{i \in \operatorname{Fin}\left(q\right)}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetFactors.choice_window_ofFn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The recursive finite choice window equals the list of choices at consecutive integer indices a through a+q-1.

**Theorem 1.11 (factor rate of power count).**

$$\forall X \in \operatorname{Set}\left(Int \to CuLetter\right), a \in Nat, L \in Nat,\; \left(\operatorname{lt}\left(0, L\right) \land \left(\forall q \in Nat,\; \operatorname{le}\left(\operatorname{power}\left(a, q\right), \operatorname{factorCount}\left(X, \operatorname{multiply}\left(q, L\right)\right)\right)\right)\right) \Rightarrow \operatorname{le}\left(\operatorname{divide}\left(\operatorname{logb}\left(2, \operatorname{toReal}\left(\operatorname{max}\left(1, a\right)\right)\right), \operatorname{toReal}\left(L\right)\right), \operatorname{weightedFactorRate}\left(X\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetFactors.factor_rate_of_power_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite alphabet supplies a uniform bound on the real logarithmic quotients. Counts at all multiples of a positive L give a frequent lower bound and hence the weighted limsup bound. Empty and singleton codebooks have the displayed zero lower bound.

**Theorem 1.12 (same reset factor cardinality).**

$$\forall o \in Ownership, b \in Real, K \in Nat,\; \left(\operatorname{le}\left(2, K\right) \land \left(\operatorname{lt}\left(\operatorname{subtract}\left(lam, \operatorname{multiply}\left(\operatorname{multiply}\left(\operatorname{power}\left(g, 2\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{hSide}\left(high\right)\right)\right), b\right) \land \operatorname{lt}\left(b, \operatorname{subtract}\left(lam, \operatorname{multiply}\left(\operatorname{multiply}\left(\operatorname{power}\left(g, 2\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{divide}\left(\operatorname{aSide}\left(high\right), \operatorname{subtract}\left(1, \operatorname{multiply}\left(rho, \operatorname{power}\left(chi, K\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\exists R \in Return,\; \operatorname{r}\left(R\right) = 1 \land \left(\operatorname{lt}\left(\operatorname{max}\left(\operatorname{max}\left(\operatorname{xSide}\left(high\right), \operatorname{ySide}\left(high\right)\right), \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right)\right), \operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(\operatorname{power}\left(rho, \operatorname{m}\left(R\right)\right), \operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(chi, \operatorname{aSide}\left(high\right)\right)\right)\right)\right)\right) \land \left(\forall sourceModel \in Model, N \in Nat,\; \operatorname{lt}\left(0, N\right) \Rightarrow \left(\operatorname{lt}\left(0, \operatorname{subtract}\left(\operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(\operatorname{power}\left(rho, \operatorname{m}\left(R\right)\right), \operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(chi, \operatorname{aSide}\left(high\right)\right)\right)\right)\right), \operatorname{initial}\left(high, sourceModel\right)\right)\right) \land \left(\operatorname{lt}\left(0, \operatorname{multiply}\left(\operatorname{subtract}\left(\operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(\operatorname{power}\left(rho, \operatorname{m}\left(R\right)\right), \operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(chi, \operatorname{aSide}\left(high\right)\right)\right)\right)\right), \operatorname{initial}\left(high, sourceModel\right)\right), \operatorname{power}\left(g, N\right)\right)\right) \land \left(\operatorname{lt}\left(0, \operatorname{divide}\left(\operatorname{min}\left(\operatorname{subtract}\left(b, \operatorname{actualAutomaticCost}\left(K\right)\right), \operatorname{multiply}\left(\operatorname{multiply}\left(\operatorname{power}\left(g, 2\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{multiply}\left(\operatorname{subtract}\left(\operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(\operatorname{power}\left(rho, \operatorname{m}\left(R\right)\right), \operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(chi, \operatorname{aSide}\left(high\right)\right)\right)\right)\right), \operatorname{initial}\left(high, sourceModel\right)\right), \operatorname{power}\left(g, N\right)\right)\right)\right), 2\right)\right) \land \left(\operatorname{Finite}\left(\operatorname{Subtype}\left(\left(\operatorname{GuardTrace}\left(K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), false, high, xs, \operatorname{initial}\left(high, sourceModel\right)\right) \land \operatorname{listWeight}\left(xs\right) = N\right)_{xs \in \operatorname{List}\left(Return\right)}\right)\right) \land \left(\left(\forall targetModel \in Model, words \in \operatorname{List}\left(\operatorname{Subtype}\left(\left(\operatorname{GuardTrace}\left(K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), false, high, xs, \operatorname{initial}\left(high, sourceModel\right)\right) \land \operatorname{listWeight}\left(xs\right) = N\right)_{xs \in \operatorname{List}\left(Return\right)}\right)\right),\; \operatorname{GuardTrace}\left(K, \operatorname{add}\left(\operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{multiply}\left(\operatorname{subtract}\left(\operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(\operatorname{power}\left(rho, \operatorname{m}\left(R\right)\right), \operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(chi, \operatorname{aSide}\left(high\right)\right)\right)\right)\right), \operatorname{initial}\left(high, sourceModel\right)\right), \operatorname{power}\left(g, N\right)\right)\right), false, high, \operatorname{resetConcatenation}\left(R, \operatorname{map}\left(val, words\right)\right), \operatorname{initial}\left(high, targetModel\right)\right) \land \operatorname{ActualPairSupply}\left(targetModel, o, \operatorname{subtract}\left(b, \operatorname{divide}\left(\operatorname{min}\left(\operatorname{subtract}\left(b, \operatorname{actualAutomaticCost}\left(K\right)\right), \operatorname{multiply}\left(\operatorname{multiply}\left(\operatorname{power}\left(g, 2\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{multiply}\left(\operatorname{subtract}\left(\operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(\operatorname{power}\left(rho, \operatorname{m}\left(R\right)\right), \operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(chi, \operatorname{aSide}\left(high\right)\right)\right)\right)\right), \operatorname{initial}\left(high, sourceModel\right)\right), \operatorname{power}\left(g, N\right)\right)\right)\right), 2\right)\right), strict, \operatorname{resetConcatenation}\left(R, \operatorname{map}\left(val, words\right)\right)\right)\right) \land \left(\exists n \in Nat,\; \operatorname{le}\left(K, n\right) \land \left(\operatorname{lt}\left(\operatorname{multiply}\left(\operatorname{hSide}\left(high\right), \operatorname{power}\left(rho, n\right)\right), \operatorname{multiply}\left(\operatorname{power}\left(chi, \operatorname{subtract}\left(K, 1\right)\right), \operatorname{multiply}\left(\operatorname{subtract}\left(\operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(\operatorname{power}\left(rho, \operatorname{m}\left(R\right)\right), \operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(chi, \operatorname{aSide}\left(high\right)\right)\right)\right)\right), \operatorname{initial}\left(high, sourceModel\right)\right), \operatorname{power}\left(g, N\right)\right)\right)\right) \land \left(\left(\forall choices \in Int \to \operatorname{Subtype}\left(\left(\operatorname{GuardTrace}\left(K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), false, high, xs, \operatorname{initial}\left(high, sourceModel\right)\right) \land \operatorname{listWeight}\left(xs\right) = N\right)_{xs \in \operatorname{List}\left(Return\right)}\right),\; \exists omega \in Int \to CuLetter,\; \operatorname{member}\left(omega, \operatorname{AuxiliaryLanguage}\left(K, \operatorname{add}\left(\operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{multiply}\left(\operatorname{subtract}\left(\operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(\operatorname{power}\left(rho, \operatorname{m}\left(R\right)\right), \operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(chi, \operatorname{aSide}\left(high\right)\right)\right)\right)\right), \operatorname{initial}\left(high, sourceModel\right)\right), \operatorname{power}\left(g, N\right)\right)\right)\right)\right) \land \left(\operatorname{member}\left(omega, \operatorname{LowerMemoryLanguage}\left(n, K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right)\right)\right) \land \left(\left(\forall j \in Int, k \in \operatorname{Fin}\left(\operatorname{length}\left(\operatorname{apply}\left(\left(\operatorname{executionWord}\left(\operatorname{cons}\left(R, \operatorname{val}\left(\operatorname{apply}\left(choices, j\right)\right)\right)\right)\right)_{j \in Int}, j\right)\right)\right),\; \operatorname{apply}\left(omega, \operatorname{add}\left(\operatorname{blockCut}\left(\left(\operatorname{executionWord}\left(\operatorname{cons}\left(R, \operatorname{val}\left(\operatorname{apply}\left(choices, j\right)\right)\right)\right)\right)_{j \in Int}, j\right), \operatorname{toInt}\left(k\right)\right)\right) = \operatorname{getElem}\left(\operatorname{apply}\left(\left(\operatorname{executionWord}\left(\operatorname{cons}\left(R, \operatorname{val}\left(\operatorname{apply}\left(choices, j\right)\right)\right)\right)\right)_{j \in Int}, j\right), k\right)\right) \land \left(\forall j \in Int,\; \operatorname{GuardTrace}\left(K, \operatorname{add}\left(\operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{multiply}\left(\operatorname{subtract}\left(\operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(\operatorname{power}\left(rho, \operatorname{m}\left(R\right)\right), \operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(chi, \operatorname{aSide}\left(high\right)\right)\right)\right)\right), \operatorname{initial}\left(high, sourceModel\right)\right), \operatorname{power}\left(g, N\right)\right)\right), false, high, \operatorname{cons}\left(R, \operatorname{val}\left(\operatorname{apply}\left(choices, j\right)\right)\right), \operatorname{pastState}\left(omega, \operatorname{blockCut}\left(\left(\operatorname{executionWord}\left(\operatorname{cons}\left(R, \operatorname{val}\left(\operatorname{apply}\left(choices, j\right)\right)\right)\right)\right)_{j \in Int}, j\right)\right)\right)\right)\right)\right)\right) \land \left(\left(\forall q \in Nat,\; \operatorname{FunctionInjective}\left(\left(\operatorname{resetFactor}\left(R, \operatorname{ofFn}\left(\left(\operatorname{val}\left(\operatorname{apply}\left(z, i\right)\right)\right)_{i \in \operatorname{Fin}\left(q\right)}\right)\right)\right)_{z \in \operatorname{Fin}\left(q\right) \to \operatorname{Subtype}\left(\left(\operatorname{GuardTrace}\left(K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), false, high, xs, \operatorname{initial}\left(high, sourceModel\right)\right) \land \operatorname{listWeight}\left(xs\right) = N\right)_{xs \in \operatorname{List}\left(Return\right)}\right)}\right) \land \left(\left(\forall z \in \operatorname{Fin}\left(q\right) \to \operatorname{Subtype}\left(\left(\operatorname{GuardTrace}\left(K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), false, high, xs, \operatorname{initial}\left(high, sourceModel\right)\right) \land \operatorname{listWeight}\left(xs\right) = N\right)_{xs \in \operatorname{List}\left(Return\right)}\right),\; \operatorname{wordWeight}\left(\operatorname{apply}\left(\left(\operatorname{resetFactor}\left(R, \operatorname{ofFn}\left(\left(\operatorname{val}\left(\operatorname{apply}\left(z, i\right)\right)\right)_{i \in \operatorname{Fin}\left(q\right)}\right)\right)\right)_{z \in \operatorname{Fin}\left(q\right) \to \operatorname{Subtype}\left(\left(\operatorname{GuardTrace}\left(K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), false, high, xs, \operatorname{initial}\left(high, sourceModel\right)\right) \land \operatorname{listWeight}\left(xs\right) = N\right)_{xs \in \operatorname{List}\left(Return\right)}\right)}, z\right)\right) = \operatorname{multiply}\left(q, \operatorname{add}\left(\operatorname{add}\left(N, 20\right), \operatorname{multiply}\left(6, \operatorname{m}\left(R\right)\right)\right)\right) \land \left(\exists omega \in Int \to CuLetter,\; \operatorname{member}\left(omega, \operatorname{LowerMemoryLanguage}\left(n, K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right)\right)\right) \land \operatorname{Occurs}\left(omega, \operatorname{apply}\left(\left(\operatorname{resetFactor}\left(R, \operatorname{ofFn}\left(\left(\operatorname{val}\left(\operatorname{apply}\left(z, i\right)\right)\right)_{i \in \operatorname{Fin}\left(q\right)}\right)\right)\right)_{z \in \operatorname{Fin}\left(q\right) \to \operatorname{Subtype}\left(\left(\operatorname{GuardTrace}\left(K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), false, high, xs, \operatorname{initial}\left(high, sourceModel\right)\right) \land \operatorname{listWeight}\left(xs\right) = N\right)_{xs \in \operatorname{List}\left(Return\right)}\right)}, z\right)\right)\right)\right) \land \left(\left(\exists family \in \operatorname{Finset}\left(\operatorname{List}\left(CuLetter\right)\right),\; \operatorname{card}\left(family\right) = \operatorname{power}\left(\operatorname{NatCard}\left(\operatorname{Subtype}\left(\left(\operatorname{GuardTrace}\left(K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), false, high, xs, \operatorname{initial}\left(high, sourceModel\right)\right) \land \operatorname{listWeight}\left(xs\right) = N\right)_{xs \in \operatorname{List}\left(Return\right)}\right)\right), q\right) \land \left(\left(\forall w \in \operatorname{List}\left(CuLetter\right),\; \operatorname{member}\left(w, family\right) \Leftrightarrow \left(\exists z \in \operatorname{Fin}\left(q\right) \to \operatorname{Subtype}\left(\left(\operatorname{GuardTrace}\left(K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), false, high, xs, \operatorname{initial}\left(high, sourceModel\right)\right) \land \operatorname{listWeight}\left(xs\right) = N\right)_{xs \in \operatorname{List}\left(Return\right)}\right),\; \operatorname{apply}\left(\left(\operatorname{resetFactor}\left(R, \operatorname{ofFn}\left(\left(\operatorname{val}\left(\operatorname{apply}\left(z, i\right)\right)\right)_{i \in \operatorname{Fin}\left(q\right)}\right)\right)\right)_{z \in \operatorname{Fin}\left(q\right) \to \operatorname{Subtype}\left(\left(\operatorname{GuardTrace}\left(K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), false, high, xs, \operatorname{initial}\left(high, sourceModel\right)\right) \land \operatorname{listWeight}\left(xs\right) = N\right)_{xs \in \operatorname{List}\left(Return\right)}\right)}, z\right) = w\right)\right) \land \left(\forall w \in \operatorname{List}\left(CuLetter\right),\; \operatorname{member}\left(w, family\right) \Rightarrow \left(\operatorname{wordWeight}\left(w\right) = \operatorname{multiply}\left(q, \operatorname{add}\left(\operatorname{add}\left(N, 20\right), \operatorname{multiply}\left(6, \operatorname{m}\left(R\right)\right)\right)\right) \land \left(\exists omega \in Int \to CuLetter,\; \operatorname{member}\left(omega, \operatorname{LowerMemoryLanguage}\left(n, K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right)\right)\right) \land \operatorname{Occurs}\left(omega, w\right)\right)\right)\right)\right)\right) \land \operatorname{le}\left(\operatorname{power}\left(\operatorname{NatCard}\left(\operatorname{Subtype}\left(\left(\operatorname{GuardTrace}\left(K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), false, high, xs, \operatorname{initial}\left(high, sourceModel\right)\right) \land \operatorname{listWeight}\left(xs\right) = N\right)_{xs \in \operatorname{List}\left(Return\right)}\right)\right), q\right), \operatorname{factorCount}\left(\operatorname{LowerMemoryLanguage}\left(n, K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right)\right), \operatorname{multiply}\left(q, \operatorname{add}\left(\operatorname{add}\left(N, 20\right), \operatorname{multiply}\left(6, \operatorname{m}\left(R\right)\right)\right)\right)\right)\right)\right)\right)\right) \land \operatorname{le}\left(\operatorname{divide}\left(\operatorname{logb}\left(2, \operatorname{toReal}\left(\operatorname{max}\left(1, \operatorname{NatCard}\left(\operatorname{Subtype}\left(\left(\operatorname{GuardTrace}\left(K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), false, high, xs, \operatorname{initial}\left(high, sourceModel\right)\right) \land \operatorname{listWeight}\left(xs\right) = N\right)_{xs \in \operatorname{List}\left(Return\right)}\right)\right)\right)\right)\right), \operatorname{toReal}\left(\operatorname{add}\left(\operatorname{add}\left(N, 20\right), \operatorname{multiply}\left(6, \operatorname{m}\left(R\right)\right)\right)\right)\right), \operatorname{weightedFactorRate}\left(\operatorname{LowerMemoryLanguage}\left(n, K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetFactors.same_reset_factor_cardinality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One reset with r=1 has floor B above both actual initial states and d, and is fixed before both source models and all N>0. For the full weak codebook, delta=B-D0 and gamma=delta times g to N. Every finite choice has high guard d+gamma and actual strict supply with the positive half-minimum error margin, including the original zero-error futures. The same reset admits every bilateral choice on one sequence with all block guards, in one lower-memory language n chosen after the fixed codebook. Here n is at least K and h rho to n is below chi to K-1 times gamma. For every q, the choice map is injective, its exact-weight image has cardinality a to q, and every image word extends bilaterally in that same lower language. The resulting weighted rate is at least log base two of max(1,a), divided by N+20+6m(R). Positive accumulated-weight cuts recover the choices even when their letter lengths differ. The empty choice q=0 uses the all-u sequence.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetFactors.FactorDictionary`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetFactors.choice_window_ofFn`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetFactors.equal_weight_concatenation_injective`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetFactors.factorCount`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetFactors.factor_dictionary_bound`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetFactors.factor_rate_of_power_count`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetFactors.resetFactor`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetFactors.reset_factor_parser`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetFactors.same_reset_factor_cardinality`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetFactors.tiled_window_occurs`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetFactors.weightedFactorRate`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetFactors.word_weight_geometry`
- Dependency: [D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetCodebook](ResetCodebook.md)
