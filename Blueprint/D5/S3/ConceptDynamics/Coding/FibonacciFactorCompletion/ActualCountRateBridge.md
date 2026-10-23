# Actual complete counts and the auxiliary rate

## Abstract

Complete actual return-list counts, prescribed source contracts and auxiliary factors have the same weighted limsup rate.

The variable weight N counts six times each m plus twenty times each r. The model fixes the high initial state XH or YH and the matching low initial state. Every supply uses the same execution list on both literal sources. External source order reverses the execution list while preserving the internal U, V and C labels. The original tails remain UC cubed followed by five and zeros, and VC cubed followed by zeros. Auxiliary bilateral padding serves only to count factors.

**Definition 1.1 (ActualDictionary).**

$$\forall model \in Model, K \in Nat, d \in Real, strict \in Bool, N \in Nat,\; \operatorname{ActualDictionary}\left(model, K, d, strict, N\right) = \operatorname{subtype}\left((xs : \operatorname{List}\left(Return\right) \mapsto \operatorname{GuardTrace}\left(K, d, strict, high, xs, \operatorname{initial}\left(high, model\right)\right) \land \operatorname{listWeight}\left(xs\right) = N)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge.ActualDictionary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complete lists satisfy the actual high-start guard trace and have exactly the indicated variable weight. Empty lists are included at weight zero.

**Definition 1.2 (actualCount).**

$$\forall model \in Model, K \in Nat, d \in Real, strict \in Bool, N \in Nat,\; \operatorname{actualCount}\left(model, K, d, strict, N\right) = \operatorname{NatCard}\left(\operatorname{ActualDictionary}\left(model, K, d, strict, N\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge.actualCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Only different complete lists are counted; errors and realizing positions are not extra choices.

**Definition 1.3 (actualLogRate).**

$$\forall model \in Model, K \in Nat, d \in Real, strict \in Bool, N \in Nat,\; \operatorname{actualLogRate}\left(model, K, d, strict, N\right) = \operatorname{divide}\left(\operatorname{logb}\left(2, \operatorname{toReal}\left(\operatorname{max}\left(1, \operatorname{actualCount}\left(model, K, d, strict, N\right)\right)\right)\right), \operatorname{toReal}\left(N\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge.actualLogRate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The max-one logarithm handles empty and unsupported weight fibres. Division at zero is the real division convention.

**Definition 1.4 (actualRate).**

$$\forall model \in Model, K \in Nat, d \in Real, strict \in Bool,\; \operatorname{actualRate}\left(model, K, d, strict\right) = \operatorname{limsup}\left((N : Nat \mapsto \operatorname{actualLogRate}\left(model, K, d, strict, N\right)), atTop\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge.actualRate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the original sparse-weight upper limit, with N tending through all natural weights.

**Definition 1.5 (actualToFactor).**

$$\forall model \in Model, K \in Nat, d \in Real, strict \in Bool, N \in Nat,\; \operatorname{le}\left(1, K\right) \Rightarrow \operatorname{hasType}\left(\operatorname{actualToFactor}\left(model, K, d, strict, N\right), \operatorname{ActualDictionary}\left(model, K, d, strict, N\right) \to \operatorname{FactorDictionary}\left(\operatorname{AuxiliaryLanguage}\left(K, d\right), N\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge.actualToFactor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The map retains exactly executionWord of the actual list. The original auxiliary lower padding proves that this word occurs in the same guard language, and the complete parser preserves its weight.

**Theorem 1.6 (actual to factor injective).**

$$\forall model \in Model, K \in Nat, d \in Real, strict \in Bool, N \in Nat,\; \operatorname{le}\left(1, K\right) \Rightarrow \operatorname{Injective}\left(\operatorname{actualToFactor}\left(model, K, d, strict, N\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge.actual_to_factor_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete c and u run parser recovers the actual positive return list from its execution word.

**Theorem 1.7 (actual dictionary bound).**

$$\forall model \in Model, K \in Nat, d \in Real, strict \in Bool, N \in Nat,\; \operatorname{le}\left(1, K\right) \Rightarrow \left(\operatorname{Finite}\left(\operatorname{ActualDictionary}\left(model, K, d, strict, N\right)\right) \land \left(\operatorname{le}\left(\operatorname{actualCount}\left(model, K, d, strict, N\right), \operatorname{factorCount}\left(\operatorname{AuxiliaryLanguage}\left(K, d\right), N\right)\right) \land \operatorname{le}\left(\operatorname{actualCount}\left(model, K, d, strict, N\right), \operatorname{power}\left(3, \operatorname{add}\left(N, 1\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge.actual_dictionary_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The injection into the finite factor dictionary bounds both strict and weak complete-list counts uniformly at every weight.

**Definition 1.8 (completedList).**

$$\forall R \in Return, a \in Nat, first \in Return, rest \in \operatorname{List}\left(Return\right),\; \operatorname{completedList}\left(R, a, first, rest\right) = \operatorname{cons}\left(\operatorname{return}\left(\operatorname{add}\left(\operatorname{m}\left(R\right), a\right), 1\right), \operatorname{cons}\left(\operatorname{return}\left(\operatorname{add}\left(\operatorname{m}\left(first\right), 1\right), \operatorname{r}\left(first\right)\right), rest\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge.completedList` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Leading u letters are absorbed into the low reset. One extra u is inserted after the first c run, even when this first return is low.

**Definition 1.9 (recoverFactor).**

$$\forall R \in Return, final \in Bool, reset \in Return, extra \in Return, rest \in \operatorname{List}\left(Return\right),\; \operatorname{recoverFactor}\left(R, final, \operatorname{cons}\left(reset, \operatorname{cons}\left(extra, rest\right)\right)\right) = \operatorname{ifThenElse}\left(final, \operatorname{dropLast}\left(\operatorname{append}\left(\operatorname{replicate}\left(\operatorname{subtract}\left(\operatorname{m}\left(reset\right), \operatorname{m}\left(R\right)\right), u\right), \operatorname{append}\left(\operatorname{replicate}\left(\operatorname{r}\left(extra\right), c\right), \operatorname{append}\left(\operatorname{replicate}\left(\operatorname{subtract}\left(\operatorname{m}\left(extra\right), 1\right), u\right), \operatorname{executionWord}\left(rest\right)\right)\right)\right)\right), \operatorname{append}\left(\operatorname{replicate}\left(\operatorname{subtract}\left(\operatorname{m}\left(reset\right), \operatorname{m}\left(R\right)\right), u\right), \operatorname{append}\left(\operatorname{replicate}\left(\operatorname{r}\left(extra\right), c\right), \operatorname{append}\left(\operatorname{replicate}\left(\operatorname{subtract}\left(\operatorname{m}\left(extra\right), 1\right), u\right), \operatorname{executionWord}\left(rest\right)\right)\right)\right)\right) \land \left(\forall xs \in \operatorname{List}\left(Return\right),\; \operatorname{lt}\left(\operatorname{length}\left(xs\right), 2\right) \Rightarrow \operatorname{recoverFactor}\left(R, final, xs\right) = \operatorname{nil}\left(CuLetter\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge.recoverFactor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Subtract the fixed number of reset u letters from the merged leading run. Remove the first-return extra u and, only for the final-c category, the last appended u. Lists shorter than two returns give the empty word.

**Theorem 1.10 (same reset completion).**

$$\forall o \in Ownership, b \in Real, K \in Nat,\; \left(\operatorname{le}\left(2, K\right) \land \left(\operatorname{lt}\left(\operatorname{subtract}\left(lam, \operatorname{multiply}\left(\operatorname{multiply}\left(\operatorname{power}\left(g, 2\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{hSide}\left(high\right)\right)\right), b\right) \land \operatorname{lt}\left(b, \operatorname{subtract}\left(lam, \operatorname{multiply}\left(\operatorname{multiply}\left(\operatorname{power}\left(g, 2\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{divide}\left(\operatorname{aSide}\left(high\right), \operatorname{subtract}\left(1, \operatorname{multiply}\left(rho, \operatorname{power}\left(chi, K\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\exists R \in Return,\; \operatorname{r}\left(R\right) = 1 \land \left(\operatorname{lt}\left(\operatorname{max}\left(\operatorname{max}\left(\operatorname{xSide}\left(high\right), \operatorname{ySide}\left(high\right)\right), \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right)\right), \operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(\operatorname{power}\left(rho, \operatorname{m}\left(R\right)\right), \operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(chi, \operatorname{aSide}\left(high\right)\right)\right)\right)\right)\right) \land \left(\left(\forall src \in Model, dst \in Model, xs \in \operatorname{List}\left(Return\right),\; \operatorname{GuardTrace}\left(K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), false, high, xs, \operatorname{initial}\left(high, src\right)\right) \Rightarrow \operatorname{ActualPairSupply}\left(dst, o, b, strict, \operatorname{cons}\left(R, xs\right)\right)\right) \land \left(\forall model \in Model, w \in \operatorname{List}\left(CuLetter\right),\; \left(\operatorname{AuxiliaryFactor}\left(K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), w\right) \land \operatorname{member}\left(c, w\right)\right) \Rightarrow \left(\exists a \in Nat, first \in Return, rest \in \operatorname{List}\left(Return\right),\; \operatorname{ifThenElse}\left(\operatorname{getLastOption}\left(w\right) = \operatorname{some}\left(c\right), \operatorname{append}\left(w, \operatorname{singleton}\left(u\right)\right), w\right) = \operatorname{append}\left(\operatorname{replicate}\left(a, u\right), \operatorname{executionWord}\left(\operatorname{cons}\left(first, rest\right)\right)\right) \land \left(\operatorname{ActualPairSupply}\left(model, o, b, strict, \operatorname{completedList}\left(R, a, first, rest\right)\right) \land \operatorname{listWeight}\left(\operatorname{completedList}\left(R, a, first, rest\right)\right) = \operatorname{add}\left(\operatorname{add}\left(\operatorname{wordWeight}\left(w\right), \operatorname{add}\left(20, \operatorname{multiply}\left(6, \operatorname{m}\left(R\right)\right)\right)\right), \operatorname{ifThenElse}\left(\operatorname{getLastOption}\left(w\right) = \operatorname{some}\left(c\right), 12, 6\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge.same_reset_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One finite low reset has output above both actual high starts and the threshold d. Enlarging a low first return retains strict actual supply, so the same reset supports weak-to-strict insertion and both factor-completion categories. The completion increases weight by CR plus six for final u and by CR plus twelve for final c. The two inserted u letters remain distinct when the first return is also the last.

**Definition 1.11 (FactorClass).**

$$\forall K \in Nat, d \in Real, N \in Nat, final \in Bool,\; \operatorname{FactorClass}\left(K, d, N, final\right) = \operatorname{subtype}\left((w : \operatorname{FactorDictionary}\left(\operatorname{AuxiliaryLanguage}\left(K, d\right), N\right) \mapsto \operatorname{member}\left(c, \operatorname{val}\left(w\right)\right) \land \left(\operatorname{getLastOption}\left(\operatorname{val}\left(w\right)\right) = \operatorname{some}\left(c\right) \Leftrightarrow final = true\right))\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge.FactorClass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two classes contain c and retain the exact final-letter distinction.

**Definition 1.12 (NoCFactor).**

$$\forall K \in Nat, d \in Real, N \in Nat,\; \operatorname{NoCFactor}\left(K, d, N\right) = \operatorname{subtype}\left((w : \operatorname{FactorDictionary}\left(\operatorname{AuxiliaryLanguage}\left(K, d\right), N\right) \mapsto \operatorname{not}\left(\operatorname{member}\left(c, \operatorname{val}\left(w\right)\right)\right))\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge.NoCFactor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the separate class containing no c.

**Theorem 1.13 (no c factor card).**

$$\forall K \in Nat, d \in Real, N \in Nat,\; \operatorname{le}\left(\operatorname{NatCard}\left(\operatorname{NoCFactor}\left(K, d, N\right)\right), 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge.no_c_factor_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Such a word consists only of u. Its weight is six times its length, so a fixed weight determines at most one word, including zero and unsupported weights.

**Theorem 1.14 (same reset count comparison).**

$$\forall o \in Ownership, b \in Real, K \in Nat,\; \left(\operatorname{le}\left(2, K\right) \land \left(\operatorname{lt}\left(\operatorname{subtract}\left(lam, \operatorname{multiply}\left(\operatorname{multiply}\left(\operatorname{power}\left(g, 2\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{hSide}\left(high\right)\right)\right), b\right) \land \operatorname{lt}\left(b, \operatorname{subtract}\left(lam, \operatorname{multiply}\left(\operatorname{multiply}\left(\operatorname{power}\left(g, 2\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{divide}\left(\operatorname{aSide}\left(high\right), \operatorname{subtract}\left(1, \operatorname{multiply}\left(rho, \operatorname{power}\left(chi, K\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\exists R \in Return,\; \operatorname{r}\left(R\right) = 1 \land \left(\operatorname{lt}\left(\operatorname{max}\left(\operatorname{max}\left(\operatorname{xSide}\left(high\right), \operatorname{ySide}\left(high\right)\right), \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right)\right), \operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(\operatorname{power}\left(rho, \operatorname{m}\left(R\right)\right), \operatorname{subtract}\left(\operatorname{hSide}\left(high\right), \operatorname{multiply}\left(chi, \operatorname{aSide}\left(high\right)\right)\right)\right)\right)\right) \land \left(\left(\forall src \in Model, dst \in Model, N \in Nat,\; \operatorname{le}\left(\operatorname{actualCount}\left(src, K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), false, N\right), \operatorname{actualCount}\left(dst, K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), true, \operatorname{add}\left(N, \operatorname{add}\left(20, \operatorname{multiply}\left(6, \operatorname{m}\left(R\right)\right)\right)\right)\right)\right)\right) \land \left(\forall model \in Model, N \in Nat,\; \operatorname{le}\left(\operatorname{factorCount}\left(\operatorname{AuxiliaryLanguage}\left(K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right)\right), N\right), \operatorname{add}\left(\operatorname{add}\left(\operatorname{actualCount}\left(model, K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), true, \operatorname{add}\left(\operatorname{add}\left(N, \operatorname{add}\left(20, \operatorname{multiply}\left(6, \operatorname{m}\left(R\right)\right)\right)\right), 6\right)\right), \operatorname{actualCount}\left(model, K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), true, \operatorname{add}\left(\operatorname{add}\left(N, \operatorname{add}\left(20, \operatorname{multiply}\left(6, \operatorname{m}\left(R\right)\right)\right)\right), 12\right)\right)\right), 1\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge.same_reset_count_comparison` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Deleting the fixed reset recovers every weak list. For each final-letter class, recoverFactor is a left inverse of actual completion. The c-containing factors therefore inject into the two strict complete dictionaries at the literal shifted weights. The class without c contributes at most one.

**Theorem 1.15 (actual log rate bounds).**

$$\forall model \in Model, K \in Nat, d \in Real, strict \in Bool,\; \operatorname{le}\left(1, K\right) \Rightarrow \left(\left(\forall N \in Nat,\; \operatorname{le}\left(0, \operatorname{actualLogRate}\left(model, K, d, strict, N\right)\right)\right) \land \operatorname{IsBoundedUnder}\left(le, atTop, (N : Nat \mapsto \operatorname{actualLogRate}\left(model, K, d, strict, N\right))\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge.actual_log_rate_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The max-one quotients are nonnegative, and their upper bounds are inherited from the actual factor injection.

**Theorem 1.16 (actual fixed shift rate).**

$$\forall model \in Model, K \in Nat, d \in Real, strict \in Bool, C \in Nat,\; \operatorname{le}\left(1, K\right) \Rightarrow \left(\operatorname{IsBoundedUnder}\left(le, atTop, (N : Nat \mapsto \operatorname{divide}\left(\operatorname{logb}\left(2, \operatorname{toReal}\left(\operatorname{max}\left(1, \operatorname{actualCount}\left(model, K, d, strict, \operatorname{add}\left(N, C\right)\right)\right)\right)\right), \operatorname{toReal}\left(N\right)\right))\right) \land \operatorname{limsup}\left((N : Nat \mapsto \operatorname{divide}\left(\operatorname{logb}\left(2, \operatorname{toReal}\left(\operatorname{max}\left(1, \operatorname{actualCount}\left(model, K, d, strict, \operatorname{add}\left(N, C\right)\right)\right)\right)\right), \operatorname{toReal}\left(N\right)\right)), atTop\right) = \operatorname{actualRate}\left(model, K, d, strict\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge.actual_fixed_shift_rate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Translation by a fixed natural weight preserves the upper limit. The changed denominator multiplies a bounded nonnegative sequence by (N plus C) divided by N, which tends to one. No positivity of the rate or support at every weight is required.

**Theorem 1.17 (actual rates equal).**

$$Ownership \to \left(\forall b \in Real, K \in Nat,\; \left(\operatorname{le}\left(2, K\right) \land \left(\operatorname{lt}\left(\operatorname{subtract}\left(lam, \operatorname{multiply}\left(\operatorname{multiply}\left(\operatorname{power}\left(g, 2\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{hSide}\left(high\right)\right)\right), b\right) \land \operatorname{lt}\left(b, \operatorname{subtract}\left(lam, \operatorname{multiply}\left(\operatorname{multiply}\left(\operatorname{power}\left(g, 2\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{divide}\left(\operatorname{aSide}\left(high\right), \operatorname{subtract}\left(1, \operatorname{multiply}\left(rho, \operatorname{power}\left(chi, K\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\forall src \in Model, dst \in Model,\; \operatorname{actualRate}\left(src, K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), false\right) = \operatorname{actualRate}\left(dst, K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), true\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge.actual_rates_equal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both directions of reset insertion, together with strict inclusion in weak and the proved fixed-shift formula, identify both starts and flags. Ownership is arbitrary and does not enter these rates or the budget inequalities.

**Theorem 1.18 (actual auxiliary rate bridge).**

$$Ownership \to \left(\forall b \in Real, K \in Nat,\; \left(\operatorname{le}\left(2, K\right) \land \left(\operatorname{lt}\left(\operatorname{subtract}\left(lam, \operatorname{multiply}\left(\operatorname{multiply}\left(\operatorname{power}\left(g, 2\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{hSide}\left(high\right)\right)\right), b\right) \land \operatorname{lt}\left(b, \operatorname{subtract}\left(lam, \operatorname{multiply}\left(\operatorname{multiply}\left(\operatorname{power}\left(g, 2\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{divide}\left(\operatorname{aSide}\left(high\right), \operatorname{subtract}\left(1, \operatorname{multiply}\left(rho, \operatorname{power}\left(chi, K\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\forall model \in Model, strict \in Bool,\; \operatorname{actualRate}\left(model, K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), strict\right) = \operatorname{weightedFactorRate}\left(\operatorname{AuxiliaryLanguage}\left(K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge.actual_auxiliary_rate_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The lower comparison is the actual-to-factor injection. For the upper comparison, the two shifted strict counts and one are bounded by three times their max-one maximum. The normalized extra logarithm tends to zero, and both shifted upper limits equal the strict actual rate. Ownership is arbitrary and does not enter either rate or the budget inequalities.

**Definition 1.19 (eta b).**

$$\forall K \in Nat, b \in Real,\; \operatorname{etaB}\left(K, b\right) = \operatorname{actualRate}\left(original, K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), false\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge.eta_b` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The canonical value selects the weak original-start expression of definition 62.8. The rate bridge proves independence of this selection.

**Definition 1.20 (contractStrict).**

$$\forall o \in Ownership, contract \in Contract,\; \operatorname{contractStrict}\left(o, contract\right) = \operatorname{ifThenElse}\left(contract = closed, \operatorname{boolNot}\left(\operatorname{apply}\left(o, 0\right)\right), true\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge.contractStrict` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The high nearest endpoint is owned exactly when o at zero is true. Closed supply then uses weak guards; non-owned closed, strict and record-margin supply use strict guards.

**Definition 1.21 (ContractDictionary).**

$$\forall model \in Model, o \in Ownership, b \in Real, contract \in Contract, N \in Nat,\; \operatorname{ContractDictionary}\left(model, o, b, contract, N\right) = \operatorname{subtype}\left((xs : \operatorname{List}\left(Return\right) \mapsto \operatorname{ActualPairSupply}\left(model, o, b, contract, xs\right) \land \operatorname{listWeight}\left(xs\right) = N)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge.ContractDictionary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The predicate is the original ActualPairSupply: both prescribed sources share the same list and history, with all future errors zero and the literal original-tail future readouts.

**Definition 1.22 (contractCount).**

$$\forall model \in Model, o \in Ownership, b \in Real, contract \in Contract, N \in Nat,\; \operatorname{contractCount}\left(model, o, b, contract, N\right) = \operatorname{NatCard}\left(\operatorname{ContractDictionary}\left(model, o, b, contract, N\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge.contractCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual source contract counts distinct complete lists at the variable weight.

**Definition 1.23 (contractRate).**

$$\forall model \in Model, o \in Ownership, b \in Real, contract \in Contract,\; \operatorname{contractRate}\left(model, o, b, contract\right) = \operatorname{limsup}\left((N : Nat \mapsto \operatorname{divide}\left(\operatorname{logb}\left(2, \operatorname{toReal}\left(\operatorname{max}\left(1, \operatorname{contractCount}\left(model, o, b, contract, N\right)\right)\right)\right), \operatorname{toReal}\left(N\right)\right)), atTop\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge.contractRate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This uses the same max-one normalized logarithm as the complete-list rate.

**Definition 1.24 (contractDictionaryEquiv).**

$$\forall o \in Ownership, b \in Real, K \in Nat,\; \left(\operatorname{le}\left(2, K\right) \land \left(\operatorname{lt}\left(\operatorname{subtract}\left(lam, \operatorname{multiply}\left(\operatorname{multiply}\left(\operatorname{power}\left(g, 2\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{hSide}\left(high\right)\right)\right), b\right) \land \operatorname{lt}\left(b, \operatorname{subtract}\left(lam, \operatorname{multiply}\left(\operatorname{multiply}\left(\operatorname{power}\left(g, 2\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{divide}\left(\operatorname{aSide}\left(high\right), \operatorname{subtract}\left(1, \operatorname{multiply}\left(rho, \operatorname{power}\left(chi, K\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\forall model \in Model, contract \in Contract, N \in Nat,\; \operatorname{hasType}\left(\operatorname{contractDictionaryEquiv}\left(model, o, b, contract, N, K\right), \operatorname{Equiv}\left(\operatorname{ContractDictionary}\left(model, o, b, contract, N\right), \operatorname{ActualDictionary}\left(model, K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{contractStrict}\left(o, contract\right), N\right)\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge.contractDictionaryEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact original strict, record-margin and owned closed supply characterizations give an equivalence that fixes the execution list in both directions.

**Theorem 1.25 (contract count correspondence).**

$$\forall o \in Ownership, b \in Real, K \in Nat,\; \left(\operatorname{le}\left(2, K\right) \land \left(\operatorname{lt}\left(\operatorname{subtract}\left(lam, \operatorname{multiply}\left(\operatorname{multiply}\left(\operatorname{power}\left(g, 2\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{hSide}\left(high\right)\right)\right), b\right) \land \operatorname{lt}\left(b, \operatorname{subtract}\left(lam, \operatorname{multiply}\left(\operatorname{multiply}\left(\operatorname{power}\left(g, 2\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{divide}\left(\operatorname{aSide}\left(high\right), \operatorname{subtract}\left(1, \operatorname{multiply}\left(rho, \operatorname{power}\left(chi, K\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\forall model \in Model, contract \in Contract, N \in Nat,\; \operatorname{Finite}\left(\operatorname{ContractDictionary}\left(model, o, b, contract, N\right)\right) \land \operatorname{contractCount}\left(model, o, b, contract, N\right) = \operatorname{actualCount}\left(model, K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{contractStrict}\left(o, contract\right), N\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge.contract_count_correspondence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual contract dictionary is finite and has the corresponding strict-flag count. A weak count is never substituted for a non-owned closed endpoint.

**Theorem 1.26 (original actual count rate bridge).**

$$\forall o \in Ownership, b \in Real, K \in Nat,\; \left(\operatorname{le}\left(2, K\right) \land \left(\operatorname{lt}\left(\operatorname{subtract}\left(lam, \operatorname{multiply}\left(\operatorname{multiply}\left(\operatorname{power}\left(g, 2\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{hSide}\left(high\right)\right)\right), b\right) \land \operatorname{lt}\left(b, \operatorname{subtract}\left(lam, \operatorname{multiply}\left(\operatorname{multiply}\left(\operatorname{power}\left(g, 2\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{divide}\left(\operatorname{aSide}\left(high\right), \operatorname{subtract}\left(1, \operatorname{multiply}\left(rho, \operatorname{power}\left(chi, K\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\operatorname{weightedFactorRate}\left(\operatorname{AuxiliaryLanguage}\left(K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right)\right)\right) = \operatorname{etaB}\left(K, b\right) \land \left(\left(\forall model \in Model, strict \in Bool,\; \operatorname{actualRate}\left(model, K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), strict\right) = \operatorname{etaB}\left(K, b\right)\right) \land \left(\forall model \in Model, contract \in Contract,\; \operatorname{contractRate}\left(model, o, b, contract\right) = \operatorname{etaB}\left(K, b\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge.original_actual_count_rate_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same auxiliary weightedFactorRate equals eta_b, every complete actual strict or weak rate for both starts, and every original actual source contract rate. This is a rate statement for the specified templates. It does not assert equality of their finite languages, a common positive margin for all lists, finite-memory rate convergence, or all-even asymptotics.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge.ActualDictionary`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge.ContractDictionary`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge.FactorClass`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge.NoCFactor`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge.actualCount`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge.actualLogRate`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge.actualRate`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge.actualToFactor`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge.actual_auxiliary_rate_bridge`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge.actual_dictionary_bound`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge.actual_fixed_shift_rate`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge.actual_log_rate_bounds`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge.actual_rates_equal`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge.actual_to_factor_injective`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge.completedList`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge.contractCount`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge.contractDictionaryEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge.contractRate`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge.contractStrict`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge.contract_count_correspondence`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge.eta_b`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge.no_c_factor_card`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge.original_actual_count_rate_bridge`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge.recoverFactor`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge.same_reset_completion`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge.same_reset_count_comparison`
- Dependency: [D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/WordWeightRegrouping](WordWeightRegrouping.md)
