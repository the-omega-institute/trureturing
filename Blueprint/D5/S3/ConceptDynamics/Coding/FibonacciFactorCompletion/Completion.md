# Actual boundaries for Fibonacci completion

## Abstract

Both actual Fibonacci starts retain the complete-boundary, closed and strict source laws and one finite actual reset map.

**Theorem 1.1 (Literal auxiliary padding of weak complete actual lists).**

$$\forall K \in Nat, d \in Real, model \in Model, xs \in \operatorname{List}\left(Return\right),\; \left(\operatorname{le}\left(1, K\right) \land \operatorname{GuardTrace}\left(K, d, false, high, xs, \operatorname{initial}\left(high, model\right)\right)\right) \Rightarrow \left(\operatorname{pastState}\left(\operatorname{uPadding}\left(\operatorname{executionWord}\left(xs\right)\right), 0\right) = \operatorname{hSide}\left(high\right) \land \left(\left(\forall p \in Nat,\; \operatorname{le}\left(p, \operatorname{length}\left(xs\right)\right) \Rightarrow \operatorname{lt}\left(\operatorname{execute}\left(high, \operatorname{take}\left(xs, p\right), \operatorname{initial}\left(high, model\right)\right), \operatorname{pastState}\left(\operatorname{uPadding}\left(\operatorname{executionWord}\left(xs\right)\right), \operatorname{castInt}\left(\operatorname{length}\left(\operatorname{executionWord}\left(\operatorname{take}\left(xs, p\right)\right)\right)\right)\right)\right)\right) \land \left(\operatorname{member}\left(\operatorname{uPadding}\left(\operatorname{executionWord}\left(xs\right)\right), \operatorname{AuxiliaryLanguage}\left(K, d\right)\right) \land \left(\operatorname{Occurs}\left(\operatorname{uPadding}\left(\operatorname{executionWord}\left(xs\right)\right), \operatorname{executionWord}\left(xs\right)\right) \land \left(\operatorname{AuxiliaryFactor}\left(K, d, \operatorname{executionWord}\left(xs\right)\right) \land \operatorname{wordWeight}\left(\operatorname{executionWord}\left(xs\right)\right) = \operatorname{listWeight}\left(xs\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/Completion.auxiliary_lower_padding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For K at least one, any real guard d and either actual initial model, a weakly guarded complete return list has its exact execution word at the origin of uPadding. This sequence equals that finite word at nonnegative positions inside it, and equals u at every other integer position. Its infinite-past state at zero is h_H. At every complete return boundary its state strictly exceeds the state of the original actual recurrence. Every c position is located in an original return; the intervening positive u runs prevent a K-letter guard from crossing a return boundary. The cap excludes K+1 consecutive c letters, and the weak actual guard transfers to the independent before-Kth-c auxiliary guard. The exact finite word occurs at zero and is an AuxiliaryFactor, with weight equal to listWeight. Combined directly with the existing complete execution parser, this supplies an injection of exact-weight weak complete lists into distinct occurrence factors. Empty lists are included. The auxiliary u tails do not replace either original eventually-empty literal source or its zero-error future. castInt is the natural-to-integer inclusion.

**Theorem 1.2 (Unique decomposition of arbitrary terminal-u words).**

$$\forall w \in \operatorname{List}\left(CuLetter\right),\; \left(w = nil \lor \operatorname{getLastOption}\left(w\right) = \operatorname{some}\left(u\right)\right) \Rightarrow \left(\exists a \in Nat, xs \in \operatorname{List}\left(Return\right),\; w = \operatorname{append}\left(\operatorname{replicate}\left(a, u\right), \operatorname{executionWord}\left(xs\right)\right) \land \left(\forall ap \in Nat, xp \in \operatorname{List}\left(Return\right),\; w = \operatorname{append}\left(\operatorname{replicate}\left(ap, u\right), \operatorname{executionWord}\left(xp\right)\right) \Rightarrow \left(ap = a \land xp = xs\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/Completion.finite_run_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite c/u word that is empty or ends in u has exactly one decomposition into a leading u run and a positive complete return list. The leading run may be empty; the return list may be empty for an all-u word. The existence proof constructs the runs by induction on the literal letters; uniqueness directly reuses the complete execution parser. The displayed two-variable existential with equality of every alternative pair is the unique-existence statement on Nat times List Return. getLastOption denotes getLast?.

**Theorem 1.3 (Independent occurrence guards on canonical complete runs).**

$$\forall K \in Nat, d \in Real, omega \in Int \to CuLetter, i \in Int, xs \in \operatorname{List}\left(Return\right),\; \left(\operatorname{le}\left(1, K\right) \land \left(\operatorname{member}\left(omega, \operatorname{AuxiliaryLanguage}\left(K, d\right)\right) \land \left(\forall k \in \operatorname{Fin}\left(\operatorname{length}\left(\operatorname{executionWord}\left(xs\right)\right)\right),\; \left(\operatorname{lt}\left(\operatorname{add}\left(\operatorname{val}\left(k\right), 1\right), \operatorname{length}\left(\operatorname{executionWord}\left(xs\right)\right)\right) \lor \operatorname{getElem}\left(\operatorname{executionWord}\left(xs\right), k\right) = c\right) \Rightarrow \operatorname{apply}\left(omega, \operatorname{add}\left(i, \operatorname{castInt}\left(\operatorname{val}\left(k\right)\right)\right)\right) = \operatorname{getElem}\left(\operatorname{executionWord}\left(xs\right), k\right)\right)\right)\right) \Rightarrow \operatorname{GuardTrace}\left(K, d, false, high, xs, \operatorname{pastState}\left(omega, i\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/Completion.occurrence_run_guards` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The bilateral sequence independently belongs to AuxiliaryLanguage. Its letters agree with the prescribed complete execution word at every position except that the final u may have been appended as a terminal fill. All c letters must still agree. Each run inherits the cap from the original forbidden K+1 c letters. At a run of length K, the original state before its last c is chi^(K-1) times its run-start state, so the independent before-Kth-c guard yields the weak return guard. When another return follows, every intervening u is an original occurrence letter and the exact transition law aligns its next start. No state alignment is claimed across an appended terminal u.

**Theorem 1.4 (Strict actual completion of every c-containing occurrence factor).**

$$\forall o \in Ownership, b \in Real, K \in Nat,\; \left(\operatorname{le}\left(2, K\right) \land \left(\operatorname{lt}\left(\operatorname{subtract}\left(lam, \operatorname{multiply}\left(\operatorname{multiply}\left(\operatorname{power}\left(g, 2\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{hSide}\left(high\right)\right)\right), b\right) \land \operatorname{lt}\left(b, \operatorname{subtract}\left(lam, \operatorname{multiply}\left(\operatorname{multiply}\left(\operatorname{power}\left(g, 2\right), \operatorname{power}\left(chi, K\right)\right), \operatorname{divide}\left(\operatorname{aSide}\left(high\right), \operatorname{subtract}\left(1, \operatorname{multiply}\left(rho, \operatorname{power}\left(chi, K\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\exists R \in Return,\; \operatorname{r}\left(R\right) = 1 \land \left(\forall model \in Model, w \in \operatorname{List}\left(CuLetter\right),\; \left(\operatorname{AuxiliaryFactor}\left(K, \operatorname{divide}\left(\operatorname{divide}\left(\operatorname{subtract}\left(lam, b\right), \operatorname{power}\left(g, 2\right)\right), \operatorname{power}\left(chi, K\right)\right), w\right) \land \operatorname{member}\left(c, w\right)\right) \Rightarrow \left(\exists a \in Nat, first \in Return, rest \in \operatorname{List}\left(Return\right),\; \operatorname{if}\left(\operatorname{getLastOption}\left(w\right) = \operatorname{some}\left(c\right), \operatorname{append}\left(w, \operatorname{singleton}\left(u\right)\right), w\right) = \operatorname{append}\left(\operatorname{replicate}\left(a, u\right), \operatorname{executionWord}\left(\operatorname{cons}\left(first, rest\right)\right)\right) \land \left(\left(\forall ap \in Nat, xp \in \operatorname{List}\left(Return\right),\; \operatorname{if}\left(\operatorname{getLastOption}\left(w\right) = \operatorname{some}\left(c\right), \operatorname{append}\left(w, \operatorname{singleton}\left(u\right)\right), w\right) = \operatorname{append}\left(\operatorname{replicate}\left(ap, u\right), \operatorname{executionWord}\left(xp\right)\right) \Rightarrow \left(ap = a \land xp = \operatorname{cons}\left(first, rest\right)\right)\right) \land \left(\operatorname{ActualPairSupply}\left(model, o, b, strict, \operatorname{cons}\left(\operatorname{Return}\left(\operatorname{add}\left(\operatorname{m}\left(R\right), a\right), 1\right), \operatorname{cons}\left(\operatorname{Return}\left(\operatorname{add}\left(\operatorname{m}\left(first\right), 1\right), \operatorname{r}\left(first\right)\right), rest\right)\right)\right) \land \left(\operatorname{executionWord}\left(\operatorname{cons}\left(\operatorname{Return}\left(\operatorname{add}\left(\operatorname{m}\left(R\right), a\right), 1\right), \operatorname{cons}\left(\operatorname{Return}\left(\operatorname{add}\left(\operatorname{m}\left(first\right), 1\right), \operatorname{r}\left(first\right)\right), rest\right)\right)\right) = \operatorname{cons}\left(c, \operatorname{append}\left(\operatorname{replicate}\left(\operatorname{add}\left(\operatorname{m}\left(R\right), a\right), u\right), \operatorname{append}\left(\operatorname{replicate}\left(\operatorname{r}\left(first\right), c\right), \operatorname{append}\left(\operatorname{replicate}\left(\operatorname{add}\left(\operatorname{m}\left(first\right), 1\right), u\right), \operatorname{executionWord}\left(rest\right)\right)\right)\right)\right) \land \operatorname{listWeight}\left(\operatorname{cons}\left(\operatorname{Return}\left(\operatorname{add}\left(\operatorname{m}\left(R\right), a\right), 1\right), \operatorname{cons}\left(\operatorname{Return}\left(\operatorname{add}\left(\operatorname{m}\left(first\right), 1\right), \operatorname{r}\left(first\right)\right), rest\right)\right)\right) = \operatorname{add}\left(\operatorname{add}\left(\operatorname{wordWeight}\left(w\right), \operatorname{add}\left(20, \operatorname{multiply}\left(6, \operatorname{m}\left(R\right)\right)\right)\right), \operatorname{if}\left(\operatorname{getLastOption}\left(w\right) = \operatorname{some}\left(c\right), 12, 6\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/Completion.auxiliary_factor_upper_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One fixed reset R has r equal to one. For either actual model and every independently occurring factor containing c, append one terminal u precisely when its last letter is c. The filled word has a unique leading u run of length a followed by first and rest positive returns. Merge that leading run into the reset by replacing its m with R.m+a; add one u after the first visible c-run by replacing first.m with first.m+1. The resulting complete list strictly supplies the original actual paired sources, with all endpoint flags, stems, paid anchor and unchanged zero-error futures. The proof uses the occurrence guards, the reset output bound and the original first-return strict output dominance. Subsequent common transitions strictly preserve dominance. Truncated first and last runs, a low first return and first equal to last are all included; no common family margin follows.

Serialization is the displayed normal form c u^(R.m+a) c^first.r u^(first.m+1) executionWord(rest). The exact weight overhead is 20+6R.m+6 for an original u ending and 20+6R.m+12 for an original c ending. Return(m,r) in the formula specifies the two positive exponents; the Lean constructors include their positivity proofs. This theorem proves actual membership and the unique run decomposition, not a finite-cardinality count or a rate.

**Theorem 1.5 (Actual equal-weight source addresses determine their lists).**

$$\forall j \in Side, model \in Model, xs \in \operatorname{List}\left(Return\right), ys \in \operatorname{List}\left(Return\right),\; \left(\operatorname{listWeight}\left(xs\right) = \operatorname{listWeight}\left(ys\right) \land \operatorname{source}\left(j, model, xs\right) = \operatorname{source}\left(j, model, ys\right)\right) \Rightarrow xs = ys$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/Completion.actual_source_address_injection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either actual side and either model, two return lists of the same variable weight have equal full eventually-empty source addresses only if the lists are equal. Equality of addresses determines the finite observed prefixes because their original lengths coincide. Removing the same stem and paid anchor leaves equal external label words. On the high side U and C have different second labels; on the low side V and C have different first labels. The label-block encoding is therefore uniquely recoverable. Reversing the execution-letter order preserves the letters inside each original block, and the existing complete execution parser recovers the return list. The two literal tails remain unchanged. This is a statement about literal addresses; it does not assert injectivity of the scalar coordinate or establish an asymptotic rate.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/Completion.actual_source_address_injection`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/Completion.auxiliary_factor_upper_completion`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/Completion.auxiliary_lower_padding`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/Completion.finite_run_decomposition`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/Completion.occurrence_run_guards`
- Dependency: [D5/S3/ConceptDynamics/Coding/DecoderOperationTrace](../DecoderOperationTrace.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/Bilateral](Bilateral.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ClosedSupply](ClosedSupply.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/StrictSupply](StrictSupply.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/FibonacciLiteralSource](../FibonacciLiteralSource.md)
