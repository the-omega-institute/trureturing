# Rigid Distinguishing Family Cardinality Bound

## Abstract

Rigid distinguishing continuations are bounded by the output alphabet.

**Theorem 1.1 (A rigid distinguishing family injects into the output alphabet).**

$$\begin{gathered}\forall A, O, I: \operatorname{Type}(),\\{}\forall D: \operatorname{Set}(\operatorname{List}(A)), T: \operatorname{List}(A) \to O,\\{}\forall C: \operatorname{DistinguishingFamily}(D, T, I),\\{}(\operatorname{Fintype}(I) \land \operatorname{Fintype}(O) \land (\forall i: I, x, y: \operatorname{List}(A), (\operatorname{append}(\operatorname{witnessPrefix}(C, i), x) \in D \land \operatorname{append}(\operatorname{witnessPrefix}(C, i), y) \in D) \Rightarrow x = y))\\{}\Rightarrow \operatorname{card}(I) \leq \operatorname{card}(O).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S0/Automata/DistinguishingFamilyCardinalityBound.card_le_card_output_of_rigid_continuations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The types A, O and I range over arbitrary universes. D is a domain of words, T is a total output function, and C is a distinguishing family indexed by I. Fintype denotes a finite-type instance; append is list concatenation.

Rigidity is required only for the family's own prefixes and is displayed explicitly. For a nontrivial index type, continuation_constant constructs one continuation shared by all distinct pairs. Evaluating T after that continuation gives an injection into O. The subsingleton case uses the output T of the empty word.

**Theorem 1.2 (The certificate is bounded by both outputs and states).**

$$\begin{gathered}\forall A, O, I: \operatorname{Type}(),\\{}\forall D: \operatorname{Set}(\operatorname{List}(A)), T: \operatorname{List}(A) \to O,\\{}\forall C: \operatorname{DistinguishingFamily}(D, T, I),\\{}\forall S: \operatorname{Type}(), M: \operatorname{DFAO}(A, O, S),\\{}(\operatorname{Fintype}(I) \land \operatorname{Fintype}(O) \land \operatorname{Fintype}(S) \land \operatorname{CorrectOn}(M, D, T) \land (\forall i: I, x, y: \operatorname{List}(A), (\operatorname{append}(\operatorname{witnessPrefix}(C, i), x) \in D \land \operatorname{append}(\operatorname{witnessPrefix}(C, i), y) \in D) \Rightarrow x = y))\\{}\Rightarrow (\operatorname{card}(I) \leq \operatorname{card}(O) \land \operatorname{card}(I) \leq \operatorname{card}(S)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S0/Automata/DistinguishingFamilyCardinalityBound.distinguishing_certificate_bounded_by_output_alphabet` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

S is an arbitrary state type and M is a DFAO over A with outputs in O. In addition to the finite-type instances, the statement requires CorrectOn(M,D,T) and the same explicit rigidity hypothesis.

The first conjunct uses the cardinality theorem and its live continuation_constant lemma. The second applies the frozen state_lower_bound_of_distinguishing_family theorem. No rigidity property of powers encodings is asserted here.

## References

- Truth anchor: `D5/S0/Automata/DistinguishingFamilyCardinalityBound.card_le_card_output_of_rigid_continuations`
- Truth anchor: `D5/S0/Automata/DistinguishingFamilyCardinalityBound.distinguishing_certificate_bounded_by_output_alphabet`
- Dependency: [D5/S0/Automata/DFAOStateLowerBound](DFAOStateLowerBound.md)
