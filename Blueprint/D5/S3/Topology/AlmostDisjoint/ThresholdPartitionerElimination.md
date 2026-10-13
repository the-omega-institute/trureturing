# A convergent maximal family with no threshold partitioner

## Abstract

Same-limit pairing eliminates actual threshold partitioners without regularity of continuum.

Information audit is unfinished. The mirrored attempt retains the complete source certificate and actual family variation, but raw source reconstruction/sourceSelection is absent. The concrete gap is disclosed in https://github.com/the-omega-institute/trureturing/issues/16293. No validated four-slot status is asserted.

L is the literal set of natural numbers n with real natValue(n) <= 1/3; U is the literal set with real natValue(n) < 2/3. Partitions(N,D) means that each actual N(x) is almost contained in D or almost disjoint from D. The final almost-disjoint family is range N. Paired labels can name the same member; the theorem does not assert finite intersections for all distinct labels.

**Theorem 1.1 (Every literal threshold separator is defeated by its own paired stage).**

$$\exists N: Branch \to \operatorname{Set}\left(Nat\right), {\forall x: Branch, \operatorname{natBranch}\left(x\right) \subseteq \operatorname{N}\left(x\right)} \land \operatorname{MADFamily}\left(\operatorname{range}\left(N\right)\right) \land {\forall x: Branch, \operatorname{ConvergesOn}\left(natValue, \operatorname{N}\left(x\right), \operatorname{limitValue}\left(x\right)\right)} \land {\forall r: unitInterval, \forall V: \operatorname{Set}\left(unitInterval\right), V \in \operatorname{nhds}\left(r\right) \Rightarrow \neg\operatorname{InFiniteUnionIdeal}\left(N, \operatorname{preimage}\left(natValue, V\right)\right)} \land \neg{\exists D: \operatorname{Set}\left(Nat\right), \operatorname{Partitions}\left(N, D\right) \land L \subseteq D \land D \subseteq U}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/AlmostDisjoint/ThresholdPartitionerElimination.exists_mad_no_threshold_partitioner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Start with the branch-labeled convergent unrestricted MAD family whose value neighborhoods escape its finite-union ideal. Every actual threshold partitioner has a common value supported by both colors. The exact branch color-fiber theorem gives continuum many labels of each color at that value. The set of all actual partitioners has cardinal at most continuum and is indexed by its initial ordinal.

At every stage, the set of previously chosen endpoints has cardinal below continuum: an initial segment is smaller than its initial ordinal cardinal, and its product with Bool remains smaller than continuum. A well-founded recursion selects one fresh endpoint of each opposite color. This uses neither CH nor regularity of continuum, including when continuum is singular.

The injective endpoint map defines an involution that swaps selected endpoints and fixes unused labels. Both endpoints share their actual limit. Replace M(x) by M(x) union M(mate(x)). Distinct actual merged members have four finite old intersections; every old member lies in a merged member, so unrestricted maximality transfers. The original finite_sUnion_converges supplier proves convergence. Finite union generators produce exactly the same ideal before and after pairing, preserving the no-small-neighborhood clause.

Any final partitioner partitions each old member by containment, hence is one of the enumerated old threshold partitioners. At its own stage, a merged infinite member contains an infinite almost-in part and an infinite almost-out part. Both its intersection and difference with that partitioner are infinite, a contradiction. This is the separator-elimination ingredient for the literal compact tagged-product construction. The compact counterexample, finite-refinement obstruction, base classification, and original Peng dynamical question still require their separate proofs.

## References

- Truth anchor: `D5/S3/Topology/AlmostDisjoint/ThresholdPartitionerElimination.exists_mad_no_threshold_partitioner`
- Dependency: [D5/S3/Topology/AlmostDisjoint/BranchColorFiber](BranchColorFiber.md)
