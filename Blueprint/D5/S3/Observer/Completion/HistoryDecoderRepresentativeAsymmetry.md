# History Decoder and Fiber Representatives

## Abstract

A forgetful completion map may choose one source representative per scalar fiber, but a nontrivial fiber prevents exact reconstruction of every history.

**Theorem 1.1 (No exact history decoder).**

$$\forall Memory \in Type, Scalar \in Type, forget \in Memory \to Scalar,\; \left(\left(\exists first \in Memory, second \in Memory,\; first \ne second \land \operatorname{forget}\left(first\right) = \operatorname{forget}\left(second\right)\right) \land \operatorname{Surjective}\left(forget\right)\right) \Rightarrow \left(\left(\neg \left(\exists decoder \in Scalar \to Memory,\; \operatorname{LeftInverse}\left(decoder, forget\right)\right)\right) \land \left(\exists representative \in Scalar \to Memory,\; \operatorname{RightInverse}\left(representative, forget\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Completion/HistoryDecoderRepresentativeAsymmetry.no_exact_history_decoder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The forgetful map is supplied directly. A pair of distinct memory states in one scalar fiber witnesses the information loss. Any left inverse would make the forgetful map injective and would therefore identify that distinct pair.

Surjectivity states that every scalar fiber is inhabited. Classical choice then selects one memory representative in every fiber, giving a right inverse. This section does not recover all memory states and so does not contradict the decoder obstruction.

## References

- Truth anchor: `D5/S3/Observer/Completion/HistoryDecoderRepresentativeAsymmetry.no_exact_history_decoder`
