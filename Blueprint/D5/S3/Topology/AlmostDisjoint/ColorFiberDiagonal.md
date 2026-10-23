# The maximality diagonal for color fibers

## Abstract

Every partitioner color support has uncountably many convergent maximal-family labels.

Information audit is unfinished: the exact source scope and compiled Reg attempt do not establish validated raw source reconstruction. The concrete missing evidence for this theorem is tracked in https://github.com/the-omega-institute/trureturing/issues/16293. This does not add a mathematical assumption or claim a complete adaptive-refinement counterexample.

Partitions(M,D) means that for every label i, either M(i) minus D or M(i) intersected with D is finite. Fiber(M,l,D,r) is {i : l(i)=r and M(i) minus D is finite}. ConvergesOn and ColorSupport use the exact finite-exception and finite-union-ideal definitions of the preceding modules. The label type can be any nonempty type, with no countability or descriptive-set assumption.

**Theorem 1.1 (A color support forces an uncountable eventual-color fiber).**

$$\forall Label: Type, \operatorname{Nonempty}\left(Label\right) \Rightarrow \forall M: Label \to \operatorname{Set}\left(Nat\right), \forall u: Nat \to unitInterval, \forall l: Label \to unitInterval, \operatorname{MADFamily}\left(\operatorname{range}\left(M\right)\right) \land {\forall i: Label, \operatorname{ConvergesOn}\left(u, \operatorname{M}\left(i\right), \operatorname{l}\left(i\right)\right)} \Rightarrow \forall D: \operatorname{Set}\left(Nat\right), \operatorname{Partitions}\left(M, D\right) \Rightarrow \forall r: unitInterval, r \in \operatorname{ColorSupport}\left(M, u, D\right) \Rightarrow \neg\operatorname{Countable}\left(\operatorname{Fiber}\left(M, l, D, r\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/AlmostDisjoint/ColorFiberDiagonal.color_support_fiber_uncountable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose the eventual-color fiber were countable and enumerate it, allowing the empty and finite cases through a default label. For every k, ideal support supplies f(k) in D, above k, in the value ball of radius 1/(k+1) at r, and outside the first k enumerated family members. These choices can be made independently. The bound f(k)>k makes its range infinite, and the shrinking balls give convergence to r.

Unrestricted maximality supplies a member meeting that range infinitely. Hausdorff separation forces its existing convergence limit to be r. The partitioner hypothesis and the range's containment in D force that member to have the D color. It therefore occurs in the enumeration, but the diagonal construction leaves only finitely many range points in it. This is a contradiction.

This proves uncountability, not continuum cardinality. The branch-tail F-sigma formula, perfect-set upgrade, separator elimination, actual compact open-map counterexample and full Ref classification remain outstanding. The Reg mirror checks the exact original theorem type only; a faithful four-slot dependent-family registration is unfinished.

## References

- Truth anchor: `D5/S3/Topology/AlmostDisjoint/ColorFiberDiagonal.color_support_fiber_uncountable`
- Dependency: [D5/S3/Topology/AlmostDisjoint/NeighborhoodIdeal](NeighborhoodIdeal.md)
