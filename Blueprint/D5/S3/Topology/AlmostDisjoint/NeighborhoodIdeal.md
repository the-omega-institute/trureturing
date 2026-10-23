# Neighborhood ideal and common color support

## Abstract

Convergent maximal families have large value neighborhoods and a common threshold color support.

Information audit is unfinished: the exact source scope and compiled Reg attempt do not establish validated raw source reconstruction. The concrete missing evidence for this theorem is tracked in https://github.com/the-omega-institute/trureturing/issues/16293. This does not add a mathematical assumption or claim a complete adaptive-refinement counterexample.

InFiniteUnionIdeal(M,E) means that E is contained in the union of finitely many actual M(x), together with a finite set. ColorSupport(M,u,D) contains the r for which every neighborhood V of r has u-preimage(V) intersected with D outside this ideal. LowerThird is {n : natValue(n) ≤ 1/3}; UpperTwoThirds is {n : natValue(n) < 2/3}. All inequalities concern the real coercion of the unit-interval value. nhds, preimage, inter and compl denote literal Lean neighborhoods and set operations.

**Theorem 1.1 (Actual maximal family with large value neighborhoods).**

$$\exists M: Branch \to \operatorname{Set}\left(Nat\right), {\forall x: Branch, \operatorname{natBranch}\left(x\right) \subseteq \operatorname{M}\left(x\right)} \land {\forall x: Branch, \forall y: Branch, x \neq y \Rightarrow \operatorname{Finite}\left(\operatorname{inter}\left(\operatorname{M}\left(x\right), \operatorname{M}\left(y\right)\right)\right)} \land \operatorname{MADFamily}\left(\operatorname{range}\left(M\right)\right) \land {\forall x: Branch, \operatorname{ConvergesOn}\left(natValue, \operatorname{M}\left(x\right), \operatorname{limitValue}\left(x\right)\right)} \land {\forall r: unitInterval, \forall V: \operatorname{Set}\left(unitInterval\right), V \in \operatorname{nhds}\left(r\right) \Rightarrow \neg\operatorname{InFiniteUnionIdeal}\left(M, \operatorname{preimage}\left(natValue, V\right)\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/AlmostDisjoint/NeighborhoodIdeal.exists_mad_with_no_small_neighborhood` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing branch-labeled convergent maximal family is retained in full. Every value fiber has continuum many branch labels, so a label can be chosen outside any given finite family. Its infinite member has only finitely many points outside the value neighborhood and only finitely many intersections with the proposed cover members. A finite cover plus a finite exceptional set would make that member finite, a contradiction.

**Theorem 1.2 (Exact thresholds force a common color support).**

$$\forall M: Branch \to \operatorname{Set}\left(Nat\right), {\forall r: unitInterval, \forall V: \operatorname{Set}\left(unitInterval\right), V \in \operatorname{nhds}\left(r\right) \Rightarrow \neg\operatorname{InFiniteUnionIdeal}\left(M, \operatorname{preimage}\left(natValue, V\right)\right)} \Rightarrow \forall D: \operatorname{Set}\left(Nat\right), \operatorname{LowerThird}\left(\right) \subseteq D \land D \subseteq \operatorname{UpperTwoThirds}\left(\right) \Rightarrow \operatorname{Nonempty}\left(\operatorname{inter}\left(\operatorname{ColorSupport}\left(M, natValue, D\right), \operatorname{ColorSupport}\left(M, natValue, \operatorname{compl}\left(D\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/AlmostDisjoint/NeighborhoodIdeal.threshold_common_color_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The generated ideal is closed under taking subsets and finite unions. Each color support is closed: a small neighborhood at r contains an open smaller neighborhood witnessing smallness at every point in it. The two supports cover the interval, since two small colored neighborhoods would make their intersection a small uncolored neighborhood.

The lower threshold excludes zero from the complement-color support, and the upper threshold excludes one from the D-color support. Connectedness of unitInterval therefore gives a point in both closed supports. The partitioner diagonal, uncountability and continuum size of both limit-color fibers, separator elimination, compact counterexample, and Ref classification remain unproved.

## References

- Truth anchor: `D5/S3/Topology/AlmostDisjoint/NeighborhoodIdeal.exists_mad_with_no_small_neighborhood`
- Truth anchor: `D5/S3/Topology/AlmostDisjoint/NeighborhoodIdeal.threshold_common_color_support`
- Dependency: [D5/S3/Topology/AlmostDisjoint/BranchLabeledMaximalFamily](BranchLabeledMaximalFamily.md)
