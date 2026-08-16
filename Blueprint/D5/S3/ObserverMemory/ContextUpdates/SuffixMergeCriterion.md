# Suffix Merge Criterion

## Abstract

A context update merges exactly when its retained suffix and next token agree.

**Theorem 1.1 (Context updates agree exactly by coordinates).**

$$\forall Token, Suffix: \operatorname{Type},\ \forall nextToken: Token \to \left(Suffix \to Token\right),\ \forall a, a': Token, s, s': Suffix,\ \operatorname{contextUpdate}\left(nextToken, (a, s)\right) = \operatorname{contextUpdate}\left(nextToken, (a', s')\right) \iff (s = s' \land \operatorname{nextToken}\left(a, s\right) = \operatorname{nextToken}\left(a', s'\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/ContextUpdates/SuffixMergeCriterion.context_update_eq_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite context is split into the oldest token and the suffix that survives the update. The update discards the oldest token, keeps the suffix, and appends the next token generated from both inputs.

Two updated contexts are equal exactly when the retained suffixes are equal and the generated next tokens are equal. This is the two coordinate equality criterion for the successor pair.

This closes qdo-v1 theorem/21.11, atom qdo-residual-1c0abd2fab1f49a70e36c7cd009f5e478bae52045c8aa330123e28c2c5f333ef. Pinned Mathlib provides the exact theorem Prod.mk_inj, which the Lean proof imports and applies directly. Repository search found no duplicate criterion; forward_merge_persistence already covers the source text's later-futures consequence after equality holds.

## References

- Truth anchor: `D5/S3/ObserverMemory/ContextUpdates/SuffixMergeCriterion.context_update_eq_iff`
