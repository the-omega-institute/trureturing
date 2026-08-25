# Source Closure Laws

## Abstract

A closure operator is extensive and monotone on source sets.

**Theorem 1.1 (Closure is extensive and monotone).**

$$\forall Carrier: \operatorname{Type}, cl: \operatorname{ClosureOperator}\left(\operatorname{Set}\left(Carrier\right)\right), S, T: \operatorname{Set}\left(Carrier\right),\\{}S \subseteq \operatorname{cl}\left(S\right) \land (S \subseteq T \Rightarrow \operatorname{cl}\left(S\right) \subseteq \operatorname{cl}\left(T\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Closure/SourceClosureLaws.source_closure_extensive_and_monotone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The closure object is the canonical Mathlib ClosureOperator on the source set carrier; no target-defined closure is introduced.

Its first public clause contains every source set in its closure, and its second clause transports every inclusion S subset T to closure S subset closure T.

The proof directly applies ClosureOperator.le_closure and monotone. The pinned repository search found no stronger packaged theorem.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Closure/SourceClosureLaws.source_closure_extensive_and_monotone`
