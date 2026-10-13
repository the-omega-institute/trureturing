# Branch-labeled convergent maximal family on Nat

## Abstract

Branch-labeled convergent maximal family on Nat.

Information audit is unfinished: the exact source scope and compiled Reg attempt do not establish validated raw source reconstruction. The concrete missing evidence for this theorem is tracked in https://github.com/the-omega-institute/trureturing/issues/16293. This does not add a mathematical assumption or claim a complete adaptive-refinement counterexample.

**Theorem 1.1 (Finite unions converge to a common value).**

$$\forall alpha: Type, \forall u: alpha \to unitInterval, \forall F: \operatorname{Set}\left(\operatorname{Set}\left(alpha\right)\right), \forall r: unitInterval, \operatorname{Finite}\left(F\right) \land {\forall A: \operatorname{Set}\left(alpha\right), A \in F \Rightarrow \operatorname{ConvergesOn}\left(u, A, r\right)} \Rightarrow \operatorname{ConvergesOn}\left(u, \operatorname{sUnion}\left(F\right), r\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/AlmostDisjoint/BranchLabeledMaximalFamily.finite_sUnion_converges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any carrier alpha, actual value map u, finite family F and common value r, convergence on every member implies convergence on their set union. The proof bounds the exceptional preimage of each neighborhood by the finite union of the memberwise finite exceptions. This is the original supplier, with identical statement, assumptions and proof, exposed at its owner for direct consumption by same-limit threshold-partitioner pairing. No duplicate proof or forwarding wrapper is added. Its exact Reg source telescope is checked, while faithful finite-family variation/raw source reconstruction remains unfinished under https://github.com/the-omega-institute/trureturing/issues/16293.

**Theorem 1.2 (Same-limit attachment and natural-number presentation).**

$$\exists M: Branch \to \operatorname{Set}\left(Nat\right), {\forall x: Branch, \operatorname{natBranch}\left(x\right) \subseteq \operatorname{M}\left(x\right)} \land {\forall x: Branch, \forall y: Branch, x \neq y \Rightarrow \operatorname{Finite}\left(\operatorname{inter}\left(\operatorname{M}\left(x\right), \operatorname{M}\left(y\right)\right)\right)} \land \operatorname{MADFamily}\left(\operatorname{range}\left(M\right)\right) \land \forall x: Branch, \operatorname{ConvergesOn}\left(natValue, \operatorname{M}\left(x\right), \operatorname{limitValue}\left(x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/AlmostDisjoint/BranchLabeledMaximalFamily.exists_branch_labeled_mad` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Additional members of the maximal family are injected into distinct branches at their actual limits. Their power-set cardinal bound is paired with the exact continuum cardinal of each limit fiber. A branch and its assigned member are united; finite disjoint blocks preserve almost-disjointness and convergence. Every old member lies in a new member, so unrestricted maximality is preserved. The nonempty four-letter word carrier is countably infinite and is transported through an actual equivalence with Nat. The resulting M has each original branch inside its corresponding member, finite intersections for distinct labels, unrestricted maximality, and convergence to the same binary limit. This supplies the initial labeled maximal family for the adaptive compact counterexample. It does not assert that a threshold-separating partitioner has been eliminated, or assert the compact topological counterexample or the base classification.

## References

- Truth anchor: `D5/S3/Topology/AlmostDisjoint/BranchLabeledMaximalFamily.exists_branch_labeled_mad`
- Truth anchor: `D5/S3/Topology/AlmostDisjoint/BranchLabeledMaximalFamily.finite_sUnion_converges`
- Dependency: [D5/S3/Topology/AlmostDisjoint/ConvergentMaximalFamily](ConvergentMaximalFamily.md)
