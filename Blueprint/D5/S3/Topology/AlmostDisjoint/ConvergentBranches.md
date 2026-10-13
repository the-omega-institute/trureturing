# Four-letter convergent branches

## Abstract

Four-letter convergent branches.

Information audit is unfinished: the exact source scope and compiled Reg attempt do not establish validated raw source reconstruction. The concrete missing evidence for this theorem is tracked in https://github.com/the-omega-institute/trureturing/issues/16293. This does not add a mathematical assumption or claim a complete adaptive-refinement counterexample.

**Theorem 1.1 (The actual four-letter branch system).**

$$\forall n: Nat, {\forall x: Branch, \operatorname{wordValue}\left(\operatorname{wordPrefix}\left(x, n\right)\right) = \operatorname{finiteDyadicSum}\left(x, n\right)} \land {\forall x: Branch, \operatorname{Infinite}\left(\operatorname{branchSet}\left(x\right)\right)} \land {\forall x: Branch, \forall y: Branch, x \neq y \Rightarrow \operatorname{Finite}\left(\operatorname{inter}\left(\operatorname{branchSet}\left(x\right), \operatorname{branchSet}\left(y\right)\right)\right)} \land {\forall x: Branch, \operatorname{ConvergesOn}\left(wordValue, \operatorname{branchSet}\left(x\right), \operatorname{limitValue}\left(x\right)\right)} \land \operatorname{Continuous}\left(limitValue\right) \land \operatorname{Surjective}\left(limitValue\right) \land \forall r: unitInterval, \operatorname{cardinal}\left(\operatorname{fiber}\left(limitValue, r\right)\right) = continuum$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/AlmostDisjoint/ConvergentBranches.branch_system` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A Word is a nonempty list over Bool times Bool. PiNat.res stores reversed prefixes; wordBits reverses the list before its chronological binary interpretation and pads with false. finiteDyadicSum(x,n) denotes the sum over i less than n+1 of the first chronological bit, interpreted in Fin 2, divided by 2 to the i+1. The dyadic identity is an actual finite sum, and the OfDigits tail estimate bounds the prefix error by the inverse of 2 to the prefix length. Branch sets are infinite, distinct branches meet finitely, and their values converge in the finite-exception sense. The binary first-coordinate map is continuous and onto unitInterval; each fiber has cardinal continuum because its second binary coordinate is free.

**Theorem 1.2 (Convergent sequences give finite-exception convergence on their ranges).**

$$\forall alpha: Type, \forall Y: Type, \forall topology: \operatorname{TopologicalSpace}\left(Y\right), \forall f: Nat \to alpha, \forall u: alpha \to Y, \forall r: Y, \operatorname{Tendsto}\left(\operatorname{compose}\left(u, f\right), atTop, \operatorname{nhds}\left(r\right)\right) \Rightarrow \operatorname{ConvergesOn}\left(u, \operatorname{range}\left(f\right), r\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/AlmostDisjoint/ConvergentBranches.convergesOn_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary carriers and an arbitrary target topology, a sequence converging atTop has only finitely many range elements outside any neighborhood of its limit. Repeated values are allowed. This lemma is consumed by the actual branch convergence and compact-interval subsequence construction.

## References

- Truth anchor: `D5/S3/Topology/AlmostDisjoint/ConvergentBranches.branch_system`
- Truth anchor: `D5/S3/Topology/AlmostDisjoint/ConvergentBranches.convergesOn_range`
