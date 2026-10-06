# Reset codebooks on one bilateral realization

## Abstract

A common reset and exact weighted gain support finite actual records and bilateral lower-memory realizations.

**Definition 1.1 (forwardCut).**

$$\forall W \in Int \to \operatorname{List}\left(CuLetter\right),\; \operatorname{forwardCut}\left(W, 0\right) = 0 \land \left(\forall n \in Nat,\; \operatorname{forwardCut}\left(W, \operatorname{add}\left(n, 1\right)\right) = \operatorname{add}\left(\operatorname{forwardCut}\left(W, n\right), \operatorname{toInt}\left(\operatorname{length}\left(\operatorname{apply}\left(W, \operatorname{toInt}\left(n\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetCodebook.forwardCut` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Forward cuts add the next block's positive letter length.

**Definition 1.2 (backwardCut).**

$$\forall W \in Int \to \operatorname{List}\left(CuLetter\right),\; \operatorname{backwardCut}\left(W, 0\right) = 0 \land \left(\forall n \in Nat,\; \operatorname{backwardCut}\left(W, \operatorname{add}\left(n, 1\right)\right) = \operatorname{add}\left(\operatorname{backwardCut}\left(W, n\right), \operatorname{toInt}\left(\operatorname{length}\left(\operatorname{apply}\left(W, \operatorname{negate}\left(\operatorname{add}\left(\operatorname{toInt}\left(n\right), 1\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetCodebook.backwardCut` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Backward cuts sum the blocks at indices minus one, minus two and so on.

**Definition 1.3 (blockCut).**

$$\forall W \in Int \to \operatorname{List}\left(CuLetter\right),\; \left(\forall n \in Nat,\; \operatorname{blockCut}\left(W, \operatorname{toInt}\left(n\right)\right) = \operatorname{forwardCut}\left(W, n\right)\right) \land \left(\forall n \in Nat,\; \operatorname{blockCut}\left(W, \operatorname{negSucc}\left(n\right)\right) = \operatorname{negate}\left(\operatorname{backwardCut}\left(W, \operatorname{add}\left(n, 1\right)\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetCodebook.blockCut` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The origin is fixed. Negative cuts use the negative backward sum; negSucc(n) denotes minus n minus one.

**Theorem 1.4 (positive block tiling).**

$$\forall W \in Int \to \operatorname{List}\left(CuLetter\right),\; \left(\forall j \in Int,\; \operatorname{lt}\left(0, \operatorname{length}\left(\operatorname{apply}\left(W, j\right)\right)\right)\right) \Rightarrow \left(\left(\operatorname{blockCut}\left(W, 0\right) = 0 \land \left(\left(\forall j \in Int,\; \operatorname{blockCut}\left(W, \operatorname{add}\left(j, 1\right)\right) = \operatorname{add}\left(\operatorname{blockCut}\left(W, j\right), \operatorname{toInt}\left(\operatorname{length}\left(\operatorname{apply}\left(W, j\right)\right)\right)\right)\right) \land \operatorname{StrictMono}\left(\operatorname{blockCut}\left(W\right)\right)\right)\right) \land \left(\exists omega \in Int \to CuLetter,\; \forall j \in Int, k \in \operatorname{Fin}\left(\operatorname{length}\left(\operatorname{apply}\left(W, j\right)\right)\right),\; \operatorname{apply}\left(omega, \operatorname{add}\left(\operatorname{blockCut}\left(W, j\right), \operatorname{toInt}\left(k\right)\right)\right) = \operatorname{getElem}\left(\operatorname{apply}\left(W, j\right), k\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetCodebook.positive_block_tiling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every indexed family of nonempty words determines disjoint consecutive block intervals covering all integer letter positions. Each prescribed letter belongs to one bilateral sequence, even when block letter lengths vary.

**Theorem 1.5 (execute seed difference).**

$$\forall xs \in \operatorname{List}\left(Return\right), x \in Real, y \in Real,\; \operatorname{subtract}\left(\operatorname{execute}\left(high, xs, y\right), \operatorname{execute}\left(high, xs, x\right)\right) = \operatorname{multiply}\left(\operatorname{power}\left(g, \operatorname{listWeight}\left(xs\right)\right), \operatorname{subtract}\left(y, x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetCodebook.execute_seed_difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original literal affine maps give the exact gain g raised to the original list weight. Positive return exponents make that weight even.

**Theorem 1.6 (exact guard gain).**

$$\forall K \in Nat, N \in Nat, d \in Real, B \in Real, model \in Model, xs \in \operatorname{List}\left(Return\right), E \in Real,\; \left(\operatorname{GuardTrace}\left(K, d, false, high, xs, \operatorname{initial}\left(high, model\right)\right) \land \left(\operatorname{listWeight}\left(xs\right) = N \land \left(\operatorname{lt}\left(\operatorname{initial}\left(high, model\right), B\right) \land \operatorname{le}\left(B, E\right)\right)\right)\right) \Rightarrow \left(\operatorname{GuardTrace}\left(K, \operatorname{add}\left(d, \operatorname{multiply}\left(\operatorname{subtract}\left(B, \operatorname{initial}\left(high, model\right)\right), \operatorname{power}\left(g, N\right)\right)\right), false, high, xs, E\right) \land \operatorname{lt}\left(\operatorname{aSide}\left(high\right), \operatorname{execute}\left(high, xs, E\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetCodebook.exact_guard_gain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An initial gain at least B minus the original initial displacement remains at least that gain times g to the full word weight at every high return prefix. The same execution also stays above the original lower boundary.

**Theorem 1.7 (reset codebook construction).**

$$\forall o \in Ownership, b \in Real, K \in Nat,\; \left(\operatorname{le}\left(2, K\right) \land \left(\operatorname{lt}\left(\operatorname{subtract}\left(lam, \operatorname{multiply}\left(\operatorname{multiply}\left(\operatorname{power}\left(g, 2\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{hSide}\left(high\right)\right)\right), b\right) \land \operatorname{lt}\left(b, \operatorname{subtract}\left(lam, \operatorname{multiply}\left(\operatorname{multiply}\left(\operatorname{power}\left(g, 2\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{divide}\left(\operatorname{aSide}\left(high\right), \operatorname{subtract}\left(1, \operatorname{multiply}\left(rho, \operatorname{power}\left(chi, K\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\exists R \in Return,\; \operatorname{r}\left(R\right) = 1 \land \left(\forall sourceModel \in Model, N \in Nat,\; \operatorname{lt}\left(0, N\right) \Rightarrow \left(\operatorname{lt}\left(0, \operatorname{subtract}\left(\operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(\operatorname{power}\left(rho, \operatorname{m}\left(R\right)\right), \operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(chi, \operatorname{aSide}\left(high\right)\right)\right)\right)\right), \operatorname{initial}\left(high, sourceModel\right)\right)\right) \land \left(\operatorname{lt}\left(0, \operatorname{multiply}\left(\operatorname{subtract}\left(\operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(\operatorname{power}\left(rho, \operatorname{m}\left(R\right)\right), \operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(chi, \operatorname{aSide}\left(high\right)\right)\right)\right)\right), \operatorname{initial}\left(high, sourceModel\right)\right), \operatorname{power}\left(g, N\right)\right)\right) \land \left(\left(\forall targetModel \in Model, words \in \operatorname{List}\left(\operatorname{Subtype}\left(\left(\operatorname{GuardTrace}\left(K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), false, high, xs, \operatorname{initial}\left(high, sourceModel\right)\right) \land \operatorname{listWeight}\left(xs\right) = N\right)_{xs \in \operatorname{List}\left(Return\right)}\right)\right),\; \operatorname{GuardTrace}\left(K, \operatorname{add}\left(\operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{multiply}\left(\operatorname{subtract}\left(\operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(\operatorname{power}\left(rho, \operatorname{m}\left(R\right)\right), \operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(chi, \operatorname{aSide}\left(high\right)\right)\right)\right)\right), \operatorname{initial}\left(high, sourceModel\right)\right), \operatorname{power}\left(g, N\right)\right)\right), false, high, \operatorname{resetConcatenation}\left(R, \operatorname{map}\left(val, words\right)\right), \operatorname{initial}\left(high, targetModel\right)\right) \land \operatorname{ActualPairSupply}\left(targetModel, o, \operatorname{subtract}\left(b, \operatorname{divide}\left(\operatorname{min}\left(\operatorname{subtract}\left(b, \operatorname{actualAutomaticCost}\left(K\right)\right), \operatorname{multiply}\left(\operatorname{multiply}\left(\operatorname{power}\left(g, 2\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{multiply}\left(\operatorname{subtract}\left(\operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(\operatorname{power}\left(rho, \operatorname{m}\left(R\right)\right), \operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(chi, \operatorname{aSide}\left(high\right)\right)\right)\right)\right), \operatorname{initial}\left(high, sourceModel\right)\right), \operatorname{power}\left(g, N\right)\right)\right)\right), 2\right)\right), strict, \operatorname{resetConcatenation}\left(R, \operatorname{map}\left(val, words\right)\right)\right)\right) \land \left(\left(\exists n \in Nat,\; \operatorname{le}\left(K, n\right) \land \operatorname{lt}\left(\operatorname{multiply}\left(\operatorname{hSide}\left(high\right), \operatorname{power}\left(rho, n\right)\right), \operatorname{multiply}\left(\operatorname{power}\left(chi, \operatorname{subtract}\left(K, 1\right)\right), \operatorname{multiply}\left(\operatorname{subtract}\left(\operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(\operatorname{power}\left(rho, \operatorname{m}\left(R\right)\right), \operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(chi, \operatorname{aSide}\left(high\right)\right)\right)\right)\right), \operatorname{initial}\left(high, sourceModel\right)\right), \operatorname{power}\left(g, N\right)\right)\right)\right)\right) \land \left(\forall choices \in Int \to \operatorname{Subtype}\left(\left(\operatorname{GuardTrace}\left(K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), false, high, xs, \operatorname{initial}\left(high, sourceModel\right)\right) \land \operatorname{listWeight}\left(xs\right) = N\right)_{xs \in \operatorname{List}\left(Return\right)}\right),\; \left(\operatorname{blockCut}\left(\left(\operatorname{executionWord}\left(\operatorname{cons}\left(R, \operatorname{val}\left(\operatorname{apply}\left(choices, j\right)\right)\right)\right)\right)_{j \in Int}, 0\right) = 0 \land \left(\left(\forall j \in Int,\; \operatorname{blockCut}\left(\left(\operatorname{executionWord}\left(\operatorname{cons}\left(R, \operatorname{val}\left(\operatorname{apply}\left(choices, j\right)\right)\right)\right)\right)_{j \in Int}, \operatorname{add}\left(j, 1\right)\right) = \operatorname{add}\left(\operatorname{blockCut}\left(\left(\operatorname{executionWord}\left(\operatorname{cons}\left(R, \operatorname{val}\left(\operatorname{apply}\left(choices, j\right)\right)\right)\right)\right)_{j \in Int}, j\right), \operatorname{toInt}\left(\operatorname{length}\left(\operatorname{apply}\left(\left(\operatorname{executionWord}\left(\operatorname{cons}\left(R, \operatorname{val}\left(\operatorname{apply}\left(choices, j\right)\right)\right)\right)\right)_{j \in Int}, j\right)\right)\right)\right)\right) \land \operatorname{StrictMono}\left(\operatorname{blockCut}\left(\left(\operatorname{executionWord}\left(\operatorname{cons}\left(R, \operatorname{val}\left(\operatorname{apply}\left(choices, j\right)\right)\right)\right)\right)_{j \in Int}\right)\right)\right)\right) \land \left(\exists omega \in Int \to CuLetter,\; \forall j \in Int, k \in \operatorname{Fin}\left(\operatorname{length}\left(\operatorname{apply}\left(\left(\operatorname{executionWord}\left(\operatorname{cons}\left(R, \operatorname{val}\left(\operatorname{apply}\left(choices, j\right)\right)\right)\right)\right)_{j \in Int}, j\right)\right)\right),\; \operatorname{apply}\left(omega, \operatorname{add}\left(\operatorname{blockCut}\left(\left(\operatorname{executionWord}\left(\operatorname{cons}\left(R, \operatorname{val}\left(\operatorname{apply}\left(choices, j\right)\right)\right)\right)\right)_{j \in Int}, j\right), \operatorname{toInt}\left(k\right)\right)\right) = \operatorname{getElem}\left(\operatorname{apply}\left(\left(\operatorname{executionWord}\left(\operatorname{cons}\left(R, \operatorname{val}\left(\operatorname{apply}\left(choices, j\right)\right)\right)\right)\right)_{j \in Int}, j\right), k\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetCodebook.reset_codebook_construction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The codebook subtype contains all weak original execution lists of weight N. One low reset R is fixed before both models and all weights. Its floor B is h minus rho to m(R) times h minus chi A; delta is B minus the selected original initial displacement and gamma is delta times g to N. Every finite joint choice has the exact high guard d plus gamma and the displayed common actual error margin. The margin uses the original automatic-slot bound, and the literal zero-error futures are included in ActualPairSupply. The two-sided symbolic tiling uses exactly the same reset blocks.

**Definition 1.8 (blockWindow).**

$$\forall W \in Int \to \operatorname{List}\left(CuLetter\right), a \in Int,\; \operatorname{blockWindow}\left(W, a, 0\right) = \operatorname{nil}\left(\right) \land \left(\forall n \in Nat,\; \operatorname{blockWindow}\left(W, a, \operatorname{add}\left(n, 1\right)\right) = \operatorname{append}\left(\operatorname{apply}\left(W, a\right), \operatorname{blockWindow}\left(W, \operatorname{add}\left(a, 1\right), n\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetCodebook.blockWindow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite window concatenates the blocks at a through a+n-1 in increasing execution order.

**Theorem 1.9 (block window positions).**

$$\forall W \in Int \to \operatorname{List}\left(CuLetter\right), a \in Int, n \in Nat,\; \left(\forall j \in Int,\; \operatorname{lt}\left(0, \operatorname{length}\left(\operatorname{apply}\left(W, j\right)\right)\right)\right) \Rightarrow \left(\operatorname{toInt}\left(\operatorname{length}\left(\operatorname{blockWindow}\left(W, a, n\right)\right)\right) = \operatorname{subtract}\left(\operatorname{blockCut}\left(W, \operatorname{add}\left(a, \operatorname{toInt}\left(n\right)\right)\right), \operatorname{blockCut}\left(W, a\right)\right) \land \left(\forall j \in Nat, k \in Nat,\; \left(\operatorname{lt}\left(j, n\right) \land \operatorname{lt}\left(k, \operatorname{length}\left(\operatorname{apply}\left(W, \operatorname{add}\left(a, \operatorname{toInt}\left(j\right)\right)\right)\right)\right)\right) \Rightarrow \operatorname{getD}\left(\operatorname{getElemOption}\left(\operatorname{blockWindow}\left(W, a, n\right), \operatorname{add}\left(\operatorname{toNat}\left(\operatorname{subtract}\left(\operatorname{blockCut}\left(W, \operatorname{add}\left(a, \operatorname{toInt}\left(j\right)\right)\right), \operatorname{blockCut}\left(W, a\right)\right)\right), k\right)\right), u\right) = \operatorname{getD}\left(\operatorname{getElemOption}\left(\operatorname{apply}\left(W, \operatorname{add}\left(a, \operatorname{toInt}\left(j\right)\right)\right), k\right), u\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetCodebook.block_window_positions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite window has precisely the difference of its endpoint cuts as its length. Each internal block letter occurs at the cut difference plus its local index.

**Theorem 1.10 (compact block tiling).**

$$\forall K \in Nat, d \in Real, W \in Int \to \operatorname{List}\left(CuLetter\right),\; \left(\operatorname{le}\left(1, K\right) \land \left(\left(\forall j \in Int,\; \operatorname{lt}\left(0, \operatorname{length}\left(\operatorname{apply}\left(W, j\right)\right)\right)\right) \land \left(\forall a \in Int, n \in Nat,\; \operatorname{member}\left(\operatorname{uPadding}\left(\operatorname{blockWindow}\left(W, a, n\right)\right), \operatorname{AuxiliaryLanguage}\left(K, d\right)\right)\right)\right)\right) \Rightarrow \left(\exists omega \in Int \to CuLetter,\; \operatorname{member}\left(omega, \operatorname{AuxiliaryLanguage}\left(K, d\right)\right) \land \left(\forall j \in Int, k \in \operatorname{Fin}\left(\operatorname{length}\left(\operatorname{apply}\left(W, j\right)\right)\right),\; \operatorname{apply}\left(omega, \operatorname{add}\left(\operatorname{blockCut}\left(W, j\right), \operatorname{toInt}\left(k\right)\right)\right) = \operatorname{getElem}\left(\operatorname{apply}\left(W, j\right), k\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetCodebook.compact_block_tiling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Centered finite block windows, shifted to their prescribed cuts, lie in one compact auxiliary language. A convergent subsequence preserves every eventually fixed block letter and the same closed guard. The result is one bilateral realization of the entire two-sided choice.

**Definition 1.11 (LowerMemoryLanguage).**

$$\forall n \in Nat, K \in Nat, d \in Real, omega \in Int \to CuLetter,\; \operatorname{member}\left(omega, \operatorname{LowerMemoryLanguage}\left(n, K, d\right)\right) \Leftrightarrow \left(\left(\forall i \in Int,\; \operatorname{not}\left(\forall q \in \operatorname{Fin}\left(\operatorname{add}\left(K, 1\right)\right),\; \operatorname{apply}\left(omega, \operatorname{add}\left(i, \operatorname{toInt}\left(q\right)\right)\right) = c\right)\right) \land \left(\forall i \in Int,\; \left(\forall q \in \operatorname{Fin}\left(K\right),\; \operatorname{apply}\left(omega, \operatorname{subtract}\left(i, \operatorname{toInt}\left(q\right)\right)\right) = c\right) \Rightarrow \operatorname{lt}\left(\operatorname{multiply}\left(\operatorname{power}\left(chi, \operatorname{subtract}\left(K, 1\right)\right), d\right), \operatorname{finitePast}\left(omega, i, n, 0\right)\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetCodebook.LowerMemoryLanguage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The lower graph forbids K+1 consecutive c letters and checks the zero-seed past before the current Kth c transition. Membership retains the original strict inequality and the original high-edge timing.

**Theorem 1.12 (uniform guard lower memory).**

$$\forall omega \in Int \to CuLetter, n \in Nat, K \in Nat, d \in Real, gamma \in Real,\; \left(\operatorname{member}\left(omega, \operatorname{AuxiliaryLanguage}\left(K, \operatorname{add}\left(d, gamma\right)\right)\right) \land \operatorname{lt}\left(\operatorname{multiply}\left(\operatorname{hSide}\left(high\right), \operatorname{power}\left(rho, n\right)\right), \operatorname{multiply}\left(\operatorname{power}\left(chi, \operatorname{subtract}\left(K, 1\right)\right), gamma\right)\right)\right) \Rightarrow \operatorname{member}\left(omega, \operatorname{LowerMemoryLanguage}\left(n, K, d\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetCodebook.uniform_guard_lower_memory` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The bilateral state exceeds its zero-seed n-past by at most h times rho to n. A common state margin larger than that error gives every strict lower-graph guard on the same sequence.

**Definition 1.13 (choiceWindow).**

$$\forall V \in Type, choices \in Int \to V, a \in Int,\; \operatorname{choiceWindow}\left(choices, a, 0\right) = \operatorname{nil}\left(\right) \land \left(\forall n \in Nat,\; \operatorname{choiceWindow}\left(choices, a, \operatorname{add}\left(n, 1\right)\right) = \operatorname{cons}\left(\operatorname{apply}\left(choices, a\right), \operatorname{choiceWindow}\left(choices, \operatorname{add}\left(a, 1\right), n\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetCodebook.choiceWindow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite window of indexed choices keeps their order and their actual subtype membership.

**Theorem 1.14 (bilateral reset codebook).**

$$\forall o \in Ownership, b \in Real, K \in Nat,\; \left(\operatorname{le}\left(2, K\right) \land \left(\operatorname{lt}\left(\operatorname{subtract}\left(lam, \operatorname{multiply}\left(\operatorname{multiply}\left(\operatorname{power}\left(g, 2\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{hSide}\left(high\right)\right)\right), b\right) \land \operatorname{lt}\left(b, \operatorname{subtract}\left(lam, \operatorname{multiply}\left(\operatorname{multiply}\left(\operatorname{power}\left(g, 2\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{divide}\left(\operatorname{aSide}\left(high\right), \operatorname{subtract}\left(1, \operatorname{multiply}\left(rho, \operatorname{power}\left(chi, K\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\exists R \in Return,\; \operatorname{r}\left(R\right) = 1 \land \left(\forall sourceModel \in Model, N \in Nat,\; \operatorname{lt}\left(0, N\right) \Rightarrow \left(\operatorname{lt}\left(0, \operatorname{subtract}\left(\operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(\operatorname{power}\left(rho, \operatorname{m}\left(R\right)\right), \operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(chi, \operatorname{aSide}\left(high\right)\right)\right)\right)\right), \operatorname{initial}\left(high, sourceModel\right)\right)\right) \land \left(\operatorname{lt}\left(0, \operatorname{multiply}\left(\operatorname{subtract}\left(\operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(\operatorname{power}\left(rho, \operatorname{m}\left(R\right)\right), \operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(chi, \operatorname{aSide}\left(high\right)\right)\right)\right)\right), \operatorname{initial}\left(high, sourceModel\right)\right), \operatorname{power}\left(g, N\right)\right)\right) \land \left(\exists n \in Nat,\; \operatorname{le}\left(K, n\right) \land \left(\operatorname{lt}\left(\operatorname{multiply}\left(\operatorname{hSide}\left(high\right), \operatorname{power}\left(rho, n\right)\right), \operatorname{multiply}\left(\operatorname{power}\left(chi, \operatorname{subtract}\left(K, 1\right)\right), \operatorname{multiply}\left(\operatorname{subtract}\left(\operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(\operatorname{power}\left(rho, \operatorname{m}\left(R\right)\right), \operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(chi, \operatorname{aSide}\left(high\right)\right)\right)\right)\right), \operatorname{initial}\left(high, sourceModel\right)\right), \operatorname{power}\left(g, N\right)\right)\right)\right) \land \left(\forall choices \in Int \to \operatorname{Subtype}\left(\left(\operatorname{GuardTrace}\left(K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), false, high, xs, \operatorname{initial}\left(high, sourceModel\right)\right) \land \operatorname{listWeight}\left(xs\right) = N\right)_{xs \in \operatorname{List}\left(Return\right)}\right),\; \exists omega \in Int \to CuLetter,\; \operatorname{member}\left(omega, \operatorname{AuxiliaryLanguage}\left(K, \operatorname{add}\left(\operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{multiply}\left(\operatorname{subtract}\left(\operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(\operatorname{power}\left(rho, \operatorname{m}\left(R\right)\right), \operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(chi, \operatorname{aSide}\left(high\right)\right)\right)\right)\right), \operatorname{initial}\left(high, sourceModel\right)\right), \operatorname{power}\left(g, N\right)\right)\right)\right)\right) \land \left(\operatorname{member}\left(omega, \operatorname{LowerMemoryLanguage}\left(n, K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right)\right)\right) \land \left(\left(\forall j \in Int, k \in \operatorname{Fin}\left(\operatorname{length}\left(\operatorname{apply}\left(\left(\operatorname{executionWord}\left(\operatorname{cons}\left(R, \operatorname{val}\left(\operatorname{apply}\left(choices, j\right)\right)\right)\right)\right)_{j \in Int}, j\right)\right)\right),\; \operatorname{apply}\left(omega, \operatorname{add}\left(\operatorname{blockCut}\left(\left(\operatorname{executionWord}\left(\operatorname{cons}\left(R, \operatorname{val}\left(\operatorname{apply}\left(choices, j\right)\right)\right)\right)\right)_{j \in Int}, j\right), \operatorname{toInt}\left(k\right)\right)\right) = \operatorname{getElem}\left(\operatorname{apply}\left(\left(\operatorname{executionWord}\left(\operatorname{cons}\left(R, \operatorname{val}\left(\operatorname{apply}\left(choices, j\right)\right)\right)\right)\right)_{j \in Int}, j\right), k\right)\right) \land \left(\forall j \in Int,\; \operatorname{GuardTrace}\left(K, \operatorname{add}\left(\operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{multiply}\left(\operatorname{subtract}\left(\operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(\operatorname{power}\left(rho, \operatorname{m}\left(R\right)\right), \operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(chi, \operatorname{aSide}\left(high\right)\right)\right)\right)\right), \operatorname{initial}\left(high, sourceModel\right)\right), \operatorname{power}\left(g, N\right)\right)\right), false, high, \operatorname{cons}\left(R, \operatorname{val}\left(\operatorname{apply}\left(choices, j\right)\right)\right), \operatorname{pastState}\left(omega, \operatorname{blockCut}\left(\left(\operatorname{executionWord}\left(\operatorname{cons}\left(R, \operatorname{val}\left(\operatorname{apply}\left(choices, j\right)\right)\right)\right)\right)_{j \in Int}, j\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetCodebook.bilateral_reset_codebook` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the full weak equal-weight original codebook, fix delta and gamma first and then choose n at least K with h rho to n less than chi to K-1 times gamma. Every two-sided choice has one bilateral sequence in AuxiliaryLanguage at d plus gamma and in the original lower-memory language at d. Every reset block occurs at its prescribed cut, and its complete return trace on that same sequence has high-start margin gamma. Thus the before-Kth-c state margin is chi to K-1 times delta times g to N. This statement supplies the bilateral construction and margins; the weighted factor-count and factor-rate conclusions require a separate counting argument.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetCodebook.LowerMemoryLanguage`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetCodebook.backwardCut`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetCodebook.bilateral_reset_codebook`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetCodebook.blockCut`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetCodebook.blockWindow`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetCodebook.block_window_positions`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetCodebook.choiceWindow`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetCodebook.compact_block_tiling`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetCodebook.exact_guard_gain`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetCodebook.execute_seed_difference`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetCodebook.forwardCut`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetCodebook.positive_block_tiling`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetCodebook.reset_codebook_construction`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetCodebook.uniform_guard_lower_memory`
- Dependency: [D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion](../FibonacciFactorCompletion.md)
