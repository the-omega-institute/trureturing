# Future-Word Information Chain

## Abstract

A recursively nested future word obeys the finite Shannon chain rule: its entropy is the first-readout entropy plus one full-prefix conditional entropy for every later readout.

**Theorem 1.1 (Marginalization preserves nonnegativity).**

$$(\forall x, 0 \leq \operatorname{p}\left(x\right)) \longrightarrow \forall i, 0 \leq \operatorname{marginal}\left(p, i\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/NamingWindow/FutureWordInformationChain.marginal_nonnegative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite second coordinate, the marginal mass at i is the sum of the joint masses p(i,j) over all j. If every joint mass is nonnegative, each term in that finite sum is nonnegative, so the marginal is too.

**Theorem 1.2 (Conditioning preserves nonnegativity).**

$$(\forall x, 0 \leq \operatorname{p}\left(x\right)) \longrightarrow \forall i, j, 0 \leq \operatorname{conditional}\left(p, i, j\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/NamingWindow/FutureWordInformationChain.conditional_nonnegative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A conditional mass divides the nonnegative joint mass p(i,j) by the corresponding marginal mass. The preceding marginal result makes the denominator nonnegative, so real division preserves nonnegativity.

**Theorem 1.3 (The first-readout marginal remains nonnegative).**

$$(\forall w, 0 \leq \operatorname{p}\left(w\right)) \longrightarrow \forall o, 0 \leq \operatorname{firstReadoutMarginal}\left(p, o\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/NamingWindow/FutureWordInformationChain.firstReadoutMarginal_nonnegative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first-readout law is obtained by repeatedly marginalizing the final coordinate of the recursively nested word. Induction on the word depth, using preservation of nonnegativity at each marginalization, shows that every first-readout mass remains nonnegative.

At depth zero the future word is just the readout alphabet, so the first-readout marginal is the original mass function.

**Theorem 1.4 (Earlier conditional entropy is inherited from the prefix).**

$$j < n \longrightarrow \operatorname{prefixConditionalEntropy}\left(p, j\right) = \operatorname{prefixConditionalEntropy}\left(\operatorname{marginal}\left(p\right), j\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/NamingWindow/FutureWordInformationChain.prefixConditionalEntropy_succ_of_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a word extended by one final readout, every conditional-entropy term strictly before the new last index depends only on the preceding prefix. Marginalizing away the final readout therefore leaves that earlier term unchanged.

**Theorem 1.5 (The last prefix-conditional entropy is the outer term).**

$$\operatorname{prefixConditionalEntropy}\left(p, n\right) = \operatorname{conditionalEntropy}\left(p\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/NamingWindow/FutureWordInformationChain.prefixConditionalEntropy_succ_last` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A successor future word is its length-n prefix paired with one final readout. At the new last index, the prefix-conditional term is exactly the conditional entropy of that outer joint pair.

**Theorem 1.6 (Extending a word appends one conditional entropy).**

$$\sum_{j < n + 1} \operatorname{prefixConditionalEntropy}\left(p, j\right) = \sum_{j < n} \operatorname{prefixConditionalEntropy}\left(\operatorname{marginal}\left(p\right), j\right) + \operatorname{conditionalEntropy}\left(p\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/NamingWindow/FutureWordInformationChain.prefixConditionalEntropy_sum_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Splitting the range through the new last index separates the final summand from all earlier summands. The earlier terms are inherited from the marginalized prefix law, while the final term is the outer conditional entropy.

Thus increasing the word depth by one extends the accumulated prefix information by exactly one conditional-entropy contribution.

**Theorem 1.7 (Future-word entropy obeys the full information chain).**

$$\begin{gathered}\forall O: \operatorname{Type}, [\operatorname{Fintype}\left(O\right)],\\{}n: \mathbb{N}, p: \operatorname{FutureWord}\left(O, n\right) \to \mathbb{R},\\{}(\forall w: \operatorname{FutureWord}\left(O, n\right), 0 \leq \operatorname{p}\left(w\right)) \longrightarrow H(p) = H(\operatorname{firstReadoutMarginal}\left(p\right)) + \sum_{j < n} \operatorname{prefixConditionalEntropy}\left(p, j\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/NamingWindow/FutureWordInformationChain.future_word_information_chain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A depth-n future word contains n+1 readouts as recursively nested prefix-output pairs. For any nonnegative mass function on that finite word type, its Shannon entropy equals the entropy of the fully marginalized first readout plus one conditional entropy for each later readout given its complete preceding prefix.

The induction step applies the two-variable entropy chain rule to the outermost prefix-output pair. The induction hypothesis expands the prefix entropy, and the successor-sum identity appends the final conditional term.

No normalization, nonempty-alphabet, or positive-mass assumption is needed. The depth-zero case has no later readouts, so its conditional sum is empty and the identity reduces to the entropy of the original readout law.

## References

- Truth anchor: `D5/S3/Entropy/NamingWindow/FutureWordInformationChain.conditional_nonnegative`
- Truth anchor: `D5/S3/Entropy/NamingWindow/FutureWordInformationChain.firstReadoutMarginal_nonnegative`
- Truth anchor: `D5/S3/Entropy/NamingWindow/FutureWordInformationChain.future_word_information_chain`
- Truth anchor: `D5/S3/Entropy/NamingWindow/FutureWordInformationChain.marginal_nonnegative`
- Truth anchor: `D5/S3/Entropy/NamingWindow/FutureWordInformationChain.prefixConditionalEntropy_succ_last`
- Truth anchor: `D5/S3/Entropy/NamingWindow/FutureWordInformationChain.prefixConditionalEntropy_succ_of_lt`
- Truth anchor: `D5/S3/Entropy/NamingWindow/FutureWordInformationChain.prefixConditionalEntropy_sum_succ`
- Dependency: [D5/S3/Entropy/ConditionalEntropy](../ConditionalEntropy.md)
