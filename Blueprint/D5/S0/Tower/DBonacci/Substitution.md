# D-Bonacci Substitution

## Abstract

One-level refinement of d-bonacci names realizes a uniform finite gap substitution.

Appending a final false digit embeds the old layer without changing values. Deleting the final digit shows that every genuinely new name ends in true and that at most one such value lies inside a coarse adjacent interval.

**Definition 1.1 (D-bonacci level embedding).**

$$\forall d \in N,\; \forall Q \in N,\; \operatorname{levelEmbedding}\left(d, Q, i\right) = \operatorname{indexOf}\left(Q + 1, \operatorname{appendZero}\left(\operatorname{nameAt}\left(d, Q, i\right)\right)\right)$$

*Formalization.* `D5/S0/Tower/DBonacci/Substitution.levelEmbedding` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fine index is obtained by adjoining one final false digit to the coarse name and applying the canonical fine-level index equivalence.

**Theorem 1.2 (Level embedding preserves value).**

$$\forall d \in N,\; \forall Q \in N,\; \operatorname{indexedValue}\left(d, Q + 1, \operatorname{levelEmbedding}\left(d, Q, i\right)\right) = \operatorname{indexedValue}\left(d, Q, i\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacci/Substitution.levelEmbedding_value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The appended false digit contributes zero and every preceding digit retains its exponent.

**Theorem 1.3 (New indices end in true).**

$$\forall j \in \operatorname{fineIndex}\left(d, Q\right),\; \operatorname{isNewIndex}\left(d, Q, j\right) = \operatorname{lastDigitTrue}\left(\operatorname{nameAt}\left(d, Q + 1, j\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacci/Substitution.new_index_iff_last_true` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A fine name ending in false is the extension of its truncation. A name ending in true cannot lie in that image, so the characterization is exact.

**Theorem 1.4 (Positive labels split into top and predecessor).**

$$\forall f \in N,\; \operatorname{gapLength}\left(d, Q, f + 1\right) = \operatorname{gapLength}\left(d, Q + 1, d + \operatorname{neg}\left(1\right)\right) + \operatorname{gapLength}\left(d, Q + 1, f\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacci/Substitution.gapLength_succ_substitution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reciprocal Perron equation identifies one new top-label segment. The remaining reciprocal-power prefix is exactly label f one level finer.

**Theorem 1.5 (General d-bonacci gap substitution).**

$$\forall f \in N,\; \operatorname{substitute}\left(d, f\right) = \operatorname{zeroOrSuccessorReplacement}\left(d, f\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacci/Substitution.dbonacci_gap_substitution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A coarse zero label contains no new name and becomes the single fine label d minus one. A coarse successor label f plus one contains one new name and becomes labels d minus one followed by f.

Finite measurements for d in {2,3,4} and Q in {3,4,5} were evaluated by executable prefix-code enumeration, even-code embedded endpoints, and the frozen fine run-budget gap lists before the general proof. The code scan is proved equal to formal run admissibility. The first whole-word flatMap conjecture failed because a trailing fine gap can lie beyond the last embedded coarse name; the local interval law held.

Repository search found the frozen Golden and Tribonacci refinement templates. Pinned mathlib supplies Fin.snoc, Fin.init, Fin.snoc_init_self, Fin.sum_univ_castSucc, and Fin.card_Ioo. GitHub Lean-code search found uses of those tuple lemmas but no general d-bonacci gap-substitution theorem.

**Theorem 1.6 (Order-three substitution compatibility).**

$$\forall f \in \operatorname{Fin}\left(3\right),\; \operatorname{mapToTribonacci}\left(\operatorname{substitute}\left(3, f\right)\right) = \operatorname{tribonacciSubstitute}\left(\operatorname{mapToTribonacci}\left(f\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacci/Substitution.gapLabelSubstitution_three_compatible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Labels zero, one, and two map respectively to small, combined, and large. Under that explicit map, the general substitution is pointwise equal to the frozen three-letter substitution.

## References

- Truth anchor: `D5/S0/Tower/DBonacci/Substitution.dbonacci_gap_substitution`
- Truth anchor: `D5/S0/Tower/DBonacci/Substitution.gapLabelSubstitution_three_compatible`
- Truth anchor: `D5/S0/Tower/DBonacci/Substitution.gapLength_succ_substitution`
- Truth anchor: `D5/S0/Tower/DBonacci/Substitution.levelEmbedding`
- Truth anchor: `D5/S0/Tower/DBonacci/Substitution.levelEmbedding_value`
- Truth anchor: `D5/S0/Tower/DBonacci/Substitution.new_index_iff_last_true`
- Dependency: [D5/S0/Tower/DBonacci/Gaps](Gaps.md)
- Dependency: [D5/S0/Tower/Tribonacci/Substitution](../Tribonacci/Substitution.md)
