# Contract Refinement

## Abstract

Strong contracts imply their weaker contract obligations.

**Theorem 1.1 (A strong contract implies the weak contract).**

$$\forall I, O: \operatorname{Type},\ A, Aprime: \operatorname{Set} I, G, Gprime: \operatorname{Set} O, M: I \to O,\ A \subseteq Aprime \land Gprime \subseteq G \land \forall i: I, i \in Aprime \Rightarrow M(i) \in Gprime \Rightarrow \forall i: I, i \in A \Rightarrow M(i) \in G.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Contracts/ContractRefinement.strong_contract_refines_weak` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A contract is represented by an allowed-input set and a guaranteed-output set for an explicit implementation map. The stronger contract accepts at least every input of the weaker one and allows at most its outputs.

The public hypotheses state both subset relations and that the implementation maps every strong-contract input into the strong guarantee. The conclusion is the corresponding weak guarantee for every weak-contract input.

Repository and pinned-library searches found no exact contract refinement theorem. The proof applies the two source subset relations directly.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Contracts/ContractRefinement.strong_contract_refines_weak`
