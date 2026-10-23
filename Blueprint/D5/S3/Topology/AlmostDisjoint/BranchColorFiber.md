# Closed branch-tail slices and continuum color fibers

## Abstract

Actual tree-prefix coding upgrades partitioner color fibers from uncountable to continuum.

Information audit is unfinished: the exact source scope and compiled Reg attempt do not establish validated raw source reconstruction. The concrete missing evidence for this theorem is tracked in https://github.com/the-omega-institute/trureturing/issues/16293. This does not add a mathematical assumption or claim a complete adaptive-refinement counterexample.

Branch is the actual four-letter Cantor space Nat → (Bool × Bool). prefixNat(x,k) is wordEquivNat(wordPrefix(x,k)), and natBranch(x) is the set of these actual natural-number prefixes. Fiber(M,D,r) denotes the subtype {x : Branch : limitValue(x)=r and M(x) minus D is finite}. The theorem requires the same M to contain each corresponding natBranch, be unrestricted maximal almost disjoint, and converge along M(x) to the actual limitValue(x). These correspondences are explicit hypotheses.

**Theorem 1.1 (Every supported eventual-color fiber has continuum cardinality).**

$$\forall M: Branch \to \operatorname{Set}\left(Nat\right), {\forall x: Branch, \operatorname{natBranch}\left(x\right) \subseteq \operatorname{M}\left(x\right)} \land \operatorname{MADFamily}\left(\operatorname{range}\left(M\right)\right) \land {\forall x: Branch, \operatorname{ConvergesOn}\left(natValue, \operatorname{M}\left(x\right), \operatorname{limitValue}\left(x\right)\right)} \Rightarrow \forall D: \operatorname{Set}\left(Nat\right), \operatorname{Partitions}\left(M, D\right) \Rightarrow \forall r: unitInterval, r \in \operatorname{ColorSupport}\left(M, natValue, D\right) \Rightarrow \operatorname{mk}\left(\operatorname{Fiber}\left(M, D, r\right)\right) = continuum$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/AlmostDisjoint/BranchColorFiber.partitioner_fiber_continuum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The enlarged maximal family need not depend continuously or Borel-measurably on its label. The partitioner hypothesis nevertheless recovers an exact finite-prefix description of its color: M(x) minus D is finite if and only if there exists m such that prefixNat(x,k) belongs to D for all k≥m. The forward implication bounds lengths of the finitely many exceptional words. In the reverse implication, the opposite partitioner color would make the infinite original branch finite, using its containment in M(x). Thus the color test is pulled back to the original tree without asserting M(x)=natBranch(x).

TailSlice(D,r,m) is the closed limit fiber intersected with all prefix-color conditions for k≥m. Each prefix-color condition is closed because a finite-coordinate cylinder fixes that literal prefix; the limit fiber is closed by the previously proved continuity of limitValue. The eventual-color fiber is exactly the countable union of these actual closed slices. This proves the required F-sigma regularity rather than assuming that an arbitrary uncountable maximal-family label set is Borel.

The maximality diagonal makes this fiber uncountable, so one closed slice is uncountable. Mathlib's IsClosed.exists_nat_bool_injection_of_not_countable supplies a genuine Cantor injection into that slice. Its cardinal lower bound is continuum, while the upper bound comes from the already checked continuum cardinality of the actual limitValue fiber. No CH or regularity of continuum is used. Separator elimination and the compact open-map counterexample remain outstanding. The Reg mirror checks the exact source telescope; faithful four-slot reconstruction evidence is unfinished.

## References

- Truth anchor: `D5/S3/Topology/AlmostDisjoint/BranchColorFiber.partitioner_fiber_continuum`
- Dependency: [D5/S3/Topology/AlmostDisjoint/ColorFiberDiagonal](ColorFiberDiagonal.md)
