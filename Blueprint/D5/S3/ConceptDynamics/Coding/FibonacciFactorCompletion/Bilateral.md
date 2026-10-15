# Execution parsing, bilateral past states and return guards

## Abstract

Positive Fibonacci return lists have unique execution-word and color-history decodings. Bilateral letter pasts determine a unique bounded state, terminal-u words have unique positive-run decompositions, and independently occurring runs inherit their exact return guards.

**Theorem 1.1 (Maximal complete runs and original history injection).**

$$\left(\forall a \in Return, xs \in \operatorname{List}\left(Return\right),\; \operatorname{takeWhile}\left(\operatorname{executionWord}\left(\operatorname{cons}\left(a, xs\right)\right), isC\right) = \operatorname{replicate}\left(\operatorname{r}\left(a\right), c\right)\right) \land \left(\left(\forall a \in Return, xs \in \operatorname{List}\left(Return\right),\; \operatorname{takeWhile}\left(\operatorname{drop}\left(\operatorname{executionWord}\left(\operatorname{cons}\left(a, xs\right)\right), \operatorname{r}\left(a\right)\right), isU\right) = \operatorname{replicate}\left(\operatorname{m}\left(a\right), u\right)\right) \land \left(\operatorname{Injective}\left(executionWord\right) \land \left(\left(\forall xs \in \operatorname{List}\left(Return\right),\; \operatorname{wordWeight}\left(\operatorname{executionWord}\left(xs\right)\right) = \operatorname{listWeight}\left(xs\right)\right) \land \left(\forall model \in Model,\; \operatorname{Injective}\left(\operatorname{history}\left(model\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/Bilateral.complete_execution_word_parser` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The initial maximal c-run has exactly r letters and the following maximal u-run has exactly m letters for every positive return. Recursing after those runs uniquely recovers the complete execution list. Its weight is exactly the original list weight with c charged 20 and u charged 6. The actual color blocks have different second colors, so their concatenation is injective. Reversing only the execution-letter word produces the external block order without reversing any color-block letters. Removing the fixed common stem and paid anchor proves history injection for each actual model.

**Theorem 1.2 (Independent finite-past state and bounded bilateral uniqueness).**

$$\left(\forall omega \in Int \to CuLetter, i \in Int, N \in Nat, x \in Real, y \in Real,\; \operatorname{subtract}\left(\operatorname{finitePast}\left(omega, i, N, y\right), \operatorname{finitePast}\left(omega, i, N, x\right)\right) = \operatorname{multiply}\left(\operatorname{power}\left(g, \operatorname{pastWeight}\left(omega, i, N\right)\right), \operatorname{subtract}\left(y, x\right)\right)\right) \land \left(\left(\forall omega \in Int \to CuLetter, i \in Int, N \in Nat,\; \operatorname{le}\left(0, \operatorname{power}\left(g, \operatorname{pastWeight}\left(omega, i, N\right)\right)\right) \land \operatorname{le}\left(\operatorname{power}\left(g, \operatorname{pastWeight}\left(omega, i, N\right)\right), \operatorname{power}\left(rho, N\right)\right)\right) \land \left(\left(\forall omega \in Int \to CuLetter, i \in Int,\; \operatorname{le}\left(0, \operatorname{pastState}\left(omega, i\right)\right) \land \operatorname{le}\left(\operatorname{pastState}\left(omega, i\right), \operatorname{hSide}\left(high\right)\right)\right) \land \left(\left(\forall omega \in Int \to CuLetter, i \in Int, z \in Real,\; \left(\operatorname{le}\left(0, z\right) \land \operatorname{le}\left(z, \operatorname{hSide}\left(high\right)\right)\right) \Rightarrow \operatorname{Tendsto}\left(\left(\operatorname{finitePast}\left(omega, i, N, z\right)\right)_{N \in Nat}, atTop, \operatorname{nhds}\left(\operatorname{pastState}\left(omega, i\right)\right)\right)\right) \land \left(\left(\forall omega \in Int \to CuLetter, i \in Int,\; \operatorname{pastState}\left(omega, \operatorname{add}\left(i, 1\right)\right) = \operatorname{letterMap}\left(\operatorname{apply}\left(omega, i\right), \operatorname{pastState}\left(omega, i\right)\right)\right) \land \left(\left(\forall omega \in Int \to CuLetter, y \in Int \to Real,\; \left(\left(\forall i \in Int,\; \operatorname{le}\left(0, \operatorname{apply}\left(y, i\right)\right) \land \operatorname{le}\left(\operatorname{apply}\left(y, i\right), \operatorname{hSide}\left(high\right)\right)\right) \land \left(\forall i \in Int,\; \operatorname{apply}\left(y, \operatorname{add}\left(i, 1\right)\right) = \operatorname{letterMap}\left(\operatorname{apply}\left(omega, i\right), \operatorname{apply}\left(y, i\right)\right)\right)\right) \Rightarrow y = \operatorname{pastState}\left(omega\right)\right) \land \left(\left(\forall omega \in Int \to CuLetter, nu \in Int \to CuLetter, i \in Int, N \in Nat,\; \left(\forall k \in \operatorname{Fin}\left(N\right),\; \operatorname{apply}\left(omega, \operatorname{subtract}\left(\operatorname{subtract}\left(i, 1\right), k\right)\right) = \operatorname{apply}\left(nu, \operatorname{subtract}\left(\operatorname{subtract}\left(i, 1\right), k\right)\right)\right) \Rightarrow \operatorname{le}\left(\left|\operatorname{subtract}\left(\operatorname{pastState}\left(omega, i\right), \operatorname{pastState}\left(nu, i\right)\right)\right|, \operatorname{multiply}\left(\operatorname{hSide}\left(high\right), \operatorname{power}\left(rho, N\right)\right)\right)\right) \land \left(\left(\forall i \in Int,\; \operatorname{pastState}\left(\operatorname{const}\left(u\right), i\right) = \operatorname{hSide}\left(high\right)\right) \land \left(\left(\forall i \in Int,\; \operatorname{Continuous}\left(\left(\operatorname{pastState}\left(omega, i\right)\right)_{omega \in Int \to CuLetter}\right)\right) \land \left(\left(\forall K \in Nat, d \in Real,\; \operatorname{le}\left(1, K\right) \Rightarrow \left(\operatorname{Nonempty}\left(\operatorname{AuxiliaryLanguage}\left(K, d\right)\right) \land \operatorname{IsCompact}\left(\operatorname{AuxiliaryLanguage}\left(K, d\right)\right)\right)\right) \land \left(\left(\forall omega \in Int \to CuLetter, i \in Int, j \in Int,\; \operatorname{pastState}\left(\operatorname{shift}\left(omega, j\right), i\right) = \operatorname{pastState}\left(omega, \operatorname{add}\left(i, j\right)\right)\right) \land \left(\forall omega \in Int \to CuLetter, j \in Int, K \in Nat, d \in Real,\; \operatorname{member}\left(omega, \operatorname{AuxiliaryLanguage}\left(K, d\right)\right) \Leftrightarrow \operatorname{member}\left(\operatorname{shift}\left(omega, j\right), \operatorname{AuxiliaryLanguage}\left(K, d\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/Bilateral.bilateral_past_state` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The auxiliary letter maps are c: z maps to chi*z and u: z maps to A_H+rho*z, with the original high-side constants. The finite past at i composes the N letters immediately before i in chronological order. Its exact seed difference is g raised to their original 20/6 weight times the seed difference, bounded by rho^N. The zero-seed sequence is increasing and bounded in [0,h_H]; its supremum is the independently defined pastState. Every seed in that interval has the same limit. This state satisfies the letter transition law and is the unique bilateral solution confined to [0,h_H]. Two sequences agreeing on the last N past letters have states differing by at most h_H*rho^N. The all-u state equals h_H. In the formula, Sequence denotes the function of N and const(u) denotes the constant bilateral u sequence.

Matching-past stability gives continuity in the product of the discrete letter spaces. AuxiliaryLanguage forbids K+1 consecutive c letters and checks chi^(K-1)*d before a current c whose preceding K-1 letters are c. For K at least one and every real d, the all-u sequence belongs to this closed compact language. States commute with every integer shift, where shift(omega,j)(n)=omega(n+j), and membership is invariant under those shifts. This language is defined by the independent letter conditions and is not a completion image or an actual literal source.

**Theorem 1.3 (Unique decomposition of arbitrary terminal-u words).**

$$\forall w \in \operatorname{List}\left(CuLetter\right),\; \left(w = nil \lor \operatorname{getLastOption}\left(w\right) = \operatorname{some}\left(u\right)\right) \Rightarrow \left(\exists a \in Nat, xs \in \operatorname{List}\left(Return\right),\; w = \operatorname{append}\left(\operatorname{replicate}\left(a, u\right), \operatorname{executionWord}\left(xs\right)\right) \land \left(\forall ap \in Nat, xp \in \operatorname{List}\left(Return\right),\; w = \operatorname{append}\left(\operatorname{replicate}\left(ap, u\right), \operatorname{executionWord}\left(xp\right)\right) \Rightarrow \left(ap = a \land xp = xs\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/Bilateral.finite_run_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite c/u word that is empty or ends in u has exactly one decomposition into a leading u run and a positive complete return list. The leading run may be empty; the return list may be empty for an all-u word. The existence proof constructs the runs by induction on the literal letters; uniqueness directly reuses the complete execution parser. The displayed two-variable existential with equality of every alternative pair is the unique-existence statement on Nat times List Return. getLastOption denotes getLast?.

**Theorem 1.4 (Independent occurrence guards on canonical complete runs).**

$$\forall K \in Nat, d \in Real, omega \in Int \to CuLetter, i \in Int, xs \in \operatorname{List}\left(Return\right),\; \left(\operatorname{le}\left(1, K\right) \land \left(\operatorname{member}\left(omega, \operatorname{AuxiliaryLanguage}\left(K, d\right)\right) \land \left(\forall k \in \operatorname{Fin}\left(\operatorname{length}\left(\operatorname{executionWord}\left(xs\right)\right)\right),\; \left(\operatorname{lt}\left(\operatorname{add}\left(\operatorname{val}\left(k\right), 1\right), \operatorname{length}\left(\operatorname{executionWord}\left(xs\right)\right)\right) \lor \operatorname{getElem}\left(\operatorname{executionWord}\left(xs\right), k\right) = c\right) \Rightarrow \operatorname{apply}\left(omega, \operatorname{add}\left(i, \operatorname{castInt}\left(\operatorname{val}\left(k\right)\right)\right)\right) = \operatorname{getElem}\left(\operatorname{executionWord}\left(xs\right), k\right)\right)\right)\right) \Rightarrow \operatorname{GuardTrace}\left(K, d, false, high, xs, \operatorname{pastState}\left(omega, i\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/Bilateral.occurrence_run_guards` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The bilateral sequence independently belongs to AuxiliaryLanguage. Its letters agree with the prescribed complete execution word at every position except that the final u may have been appended as a terminal fill. All c letters must still agree. Each run inherits the cap from the original forbidden K+1 c letters. At a run of length K, the original state before its last c is chi^(K-1) times its run-start state, so the independent before-Kth-c guard yields the weak return guard. When another return follows, every intervening u is an original occurrence letter and the exact transition law aligns its next start. No state alignment is claimed across an appended terminal u.

**Theorem 1.5 (Recursive guards at every execution split).**

$$\forall K \in Nat, d \in Real, strict \in Bool, j \in Side, execution \in \operatorname{List}\left(Return\right), D \in Real,\; \operatorname{GuardTrace}\left(K, d, strict, j, execution, D\right) \Leftrightarrow \left(\forall before \in \operatorname{List}\left(Return\right), a \in Return, after \in \operatorname{List}\left(Return\right),\; execution = \operatorname{append}\left(before, \operatorname{cons}\left(a, after\right)\right) \Rightarrow \left(\operatorname{le}\left(\operatorname{r}\left(a\right), K\right) \land \left(\operatorname{r}\left(a\right) = K \Rightarrow \left(\left(strict = true \Rightarrow \operatorname{lt}\left(d, \operatorname{execute}\left(j, before, D\right)\right)\right) \land \left(strict = false \Rightarrow \operatorname{le}\left(d, \operatorname{execute}\left(j, before, D\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/Bilateral.uniform_guard_trace_iff_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural cap K, real threshold d, Boolean strictness, side, finite positive-return list and real initial state D, the recursive GuardTrace holds exactly when each split before ++ a :: after obeys a.r <= K and, when a.r = K, tests the state obtained by executing before from D. The test is d < state when strict is true and d <= state when strict is false; the displayed pair of implications states that Boolean conditional completely. Return carries positive natural r and m. No lower bound on K, restriction to an actual literal starting state, or bound on the list length is assumed. Induction aligns the tail's initial state with returnMap after its first return. This structural equivalence alone does not assert whole-record supply.

**Theorem 1.6 (Exact active costs at every execution split).**

$$\forall j \in Side, budget \in Real, execution \in \operatorname{List}\left(Return\right), D \in Real,\; \operatorname{StrictControl}\left(j, budget, execution, D\right) \Leftrightarrow \left(\forall before \in \operatorname{List}\left(Return\right), a \in Return, after \in \operatorname{List}\left(Return\right),\; execution = \operatorname{append}\left(before, \operatorname{cons}\left(a, after\right)\right) \Rightarrow \operatorname{lt}\left(\operatorname{subtract}\left(lam, \operatorname{multiply}\left(\operatorname{multiply}\left(\operatorname{power}\left(g, 2\right), \operatorname{power}\left(chi, \operatorname{r}\left(a\right)\right)\right), \operatorname{execute}\left(j, before, D\right)\right)\right), budget\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/Bilateral.exact_control_iff_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either side, every real budget and initial state, and every finite list of positive returns, StrictControl is equivalent to testing lam - g^2 * chi^(a.r) * execute(j,before,D) < budget at every split before ++ a :: after of the same execution. StrictControl recursively tests the current cost and continues at returnMap(j,a,D); execute follows that same return map. The constants are T2 = 1 - t and lam = T2 / 10, with the original Fibonacci t, g and chi. The empty list satisfies both sides. The proof uses unbounded list induction and imposes no actual-start, budget-interval or cap hypothesis. It proves no record-error, reset or rate assertion.

## Exact equal-weight source-address application

This application uses the original literal alphabet Label = {L3, L0, L5, L2, L25}. The fixed blocks are U = [L5,L0,L3,L0,L3,L3], V = [L0,L3,L3,L5,L0,L3], and C = [L5,L5,L3,L2,L2,L0,L3,L3,L3,L25,L5,L0,L0,L2,L2,L25,L3,L3,L0,L5]. For side high the block is U and for side low it is V. A positive return a=(m,r) contributes returnWord(j,a) = repeatWord(block(j),m) ++ repeatWord(C,r), with both m and r positive.

The original stem is block(j) ++ C. The external word of an execution is (execution.reverse.map(returnWord(j))).flatten, so packet order is reversed while the literal order inside every repeated block is retained. The original model has empty anchor; the anchored model has anchor equal to the stem. Thus observedPrefix(j,model,execution) is the common stem followed by that external word and the model anchor. The finite source appends the finite tail block(j) ++ repeatWord(C,3) ++ exitPrefix(j), where exitPrefix(high) = [L5,L0] and exitPrefix(low) = [L0]. The source at p is the Label at that finite word position, with L0 as the eventual default outside the word.

Encode c by C and u by block(j). The complete parser `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/Bilateral` supplies the complete_execution_word_parser c^r u^m run decomposition, injectivity of executionWord, and equality of its 20/6 word weight with listWeight. The existing prefix-free decoder `D5/S0/Computability/Coding/PrefixFreeCode` (the uniquelyDecodable_of_isPrefixFree declaration) applies because C, U and V are nonempty and the displayed literal blocks form a prefix-free two-letter code for each side. The lawful monoid-power identity for repeatWord turns every repeated block into the corresponding flattened replicate, so the decoder sees exactly the reversed execution packets.

Fix a common side j and a common model. For two executions xs and ys with equal listWeight, the parser and the block lengths give equal observed-prefix lengths. Equality of their actual source addresses therefore restricts to equality of the two finite observed prefixes at every position before the common tail; no observed-prefix equality is assumed. Cancelling the common stem and the equal model anchor leaves equality of the two external words. Prefix-free unique decoding gives equality of the reversed execution-letter words. Cancelling reversal and applying the complete execution parser then gives equality of the original Return lists. This is the Label source-address injection for both sides, both models, and arbitrary positive lists including the empty list.

This Label-address application is separate from the preceding Color-history injection, whose observations use colorsD and colorsE. It makes no claim about an all-even dictionary, any count, or ActualPairSupply, and it asserts no resource, rate, optimality, or physical-realization property.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/Bilateral.bilateral_past_state`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/Bilateral.complete_execution_word_parser`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/Bilateral.exact_control_iff_split`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/Bilateral.finite_run_decomposition`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/Bilateral.occurrence_run_guards`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/Bilateral.uniform_guard_trace_iff_split`
- Narrative reference: [D5/S0/Computability/Coding/PrefixFreeCode](../../../../S0/Computability/Coding/PrefixFreeCode.md)
