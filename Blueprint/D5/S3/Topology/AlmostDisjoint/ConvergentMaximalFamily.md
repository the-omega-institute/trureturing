# An unrestricted convergent maximal family

## Abstract

An unrestricted convergent maximal family.

Information audit is unfinished: the exact source scope and compiled Reg attempt do not establish validated raw source reconstruction. The concrete missing evidence for this theorem is tracked in https://github.com/the-omega-institute/trureturing/issues/16293. This does not add a mathematical assumption or claim a complete adaptive-refinement counterexample.

**Theorem 1.1 (Actual maximal family containing the branches).**

$$\exists M: \operatorname{Set}\left(\operatorname{Set}\left(Word\right)\right), \operatorname{range}\left(branchSet\right) \subseteq M \land \operatorname{MADFamily}\left(M\right) \land \forall A: \operatorname{Set}\left(Word\right), A \in M \Rightarrow \exists r: unitInterval, \operatorname{ConvergesOn}\left(wordValue, A, r\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/AlmostDisjoint/ConvergentMaximalFamily.exists_convergent_mad` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Zorn extends the actual four-letter branch family among infinite almost-disjoint sets with convergent word values. Unions of chains preserve those requirements. An arbitrary infinite set almost disjoint from that maximal family has an injective sequence; compactness of unitInterval supplies a strictly increasing convergent subsequence. Its range would be a new convergent member, contradicting maximality. Thus every infinite set has infinite intersection with some member. The unrestricted maximality conclusion is proved rather than supplied as a hypothesis.

## References

- Truth anchor: `D5/S3/Topology/AlmostDisjoint/ConvergentMaximalFamily.exists_convergent_mad`
- Dependency: [D5/S3/Topology/AlmostDisjoint/ConvergentBranches](ConvergentBranches.md)
