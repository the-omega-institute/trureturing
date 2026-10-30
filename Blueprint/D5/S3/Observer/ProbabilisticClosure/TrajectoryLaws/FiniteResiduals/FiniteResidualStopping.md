# Finite residuals and actual stopping archives

## Abstract

Joint residual signatures preserve actual finite words; stopped execution has exactly the same observational equivalence.

S and Y are arbitrary finite types. K is the existing FiniteMarkovKernel from S to Y times S: every joint row is nonnegative and sums to one. There is one interface, one everywhere legal action, and no failure terminal. K is time homogeneous. No positivity, full support, rationality, determinism or nonemptiness assumption is added. Empty finite types are included wherever such a normalized kernel exists.

Current observation is constant. Thus residual(K,0,x,xp) is True, exactly equality of the current readout. For a relation R, classMass(K,R,x,y,c) sums K(x,(y,r)) over r related to c. The successor residual retains the preceding relation and requires equality of these joint label/class masses for every label and every class representative. Repeated representatives merely repeat the same equation. Each residual is an equivalence relation. This is the decreasing recursive joint-class chain, independently defined from actual word laws.

wordProb(K,x,[]) is one. wordProb(K,x,y::w) sums K(x,(y,r))*wordProb(K,r,w) over all actual successors. TraceEq(K,n,x,xp) means equality of these probabilities for every word of length at most n. Experiment(Y,n) is a finite tree: stop is allowed at any remaining depth; step chooses its continuation solely from the next actual label. Every finite deterministic prefix-dependent stopping policy has this tree representation, and every such tree is allowed. There is no action choice beyond the unique action and no hidden-state test, class test, law-table access, reset, copying or postselection.

**Theorem 1.1 (Soundness at every horizon).**

$$\forall S:Type, (\forall Y:Type, ([\operatorname{Fintype}(S)] [\operatorname{Fintype}(Y)] \forall K:\operatorname{FiniteMarkovKernel}(S,\operatorname{Prod}(Y,S)), (\forall n:Nat, (\forall x:S, (\forall xp:S, (\operatorname{residual}(K,n,x,xp)\Rightarrow\operatorname{TraceEq}(K,n,x,xp)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteResiduals/FiniteResidualStopping.residual_sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induct on n. At zero only the empty word occurs. For y::w, the induction hypothesis makes r mapped to wordProb(K,r,w) constant on each preceding residual class. Partition the finite successor sum into those classes. Equality of the joint label/class masses makes their weighted sums equal. This grouping is a mathematical integration identity and does not reveal the successor class to the policy.

archiveProb executes the tree chronologically. At stop it gives mass one to the empty suffix. At step its empty suffix has mass zero, and the mass of y::w sums the original joint kernel times the independently executed continuation chosen by y. accepts(E,w) says that w ends at a leaf of this tree, with no earlier stop. Induction on the tree proves archiveProb(K,E,x,w)=wordProb(K,x,w) when accepts(E,w), and zero otherwise. An accepted word has length at most the depth. This proves the word/archive correspondence rather than identifying the two laws by definition.

**Theorem 1.2 (Exact operational stopping characterization).**

$$\forall S:Type, (\forall Y:Type, ([\operatorname{Fintype}(S)] [\operatorname{Fintype}(Y)] \forall K:\operatorname{FiniteMarkovKernel}(S,\operatorname{Prod}(Y,S)), (\forall n:Nat, (\forall x:S, (\forall xp:S, (\operatorname{TraceEq}(K,n,x,xp)\Leftrightarrow\operatorname{StoppingEq}(K,n,x,xp)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteResiduals/FiniteResidualStopping.trace_iff_stopping` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

StoppingEq quantifies over every k at most n, every Experiment(Y,k), and every complete archive word. For the forward direction, use the independently proved accepted-prefix formula and its length bound. For the reverse direction, use the legal tree that continues exactly length(w) steps and then stops. These arguments include immediate stopping, the empty word, horizon zero and branches of zero probability. A suffix discarded by stopping is summed out; no observer operation on that suffix is introduced.

**Theorem 1.3 (The executed archives are probability laws).**

$$\forall S:Type, (\forall Y:Type, ([\operatorname{Fintype}(S)] [\operatorname{Fintype}(Y)] \forall K:\operatorname{FiniteMarkovKernel}(S,\operatorname{Prod}(Y,S)), (\forall n:Nat, (\forall E:\operatorname{Experiment}(Y,n), (\forall x:S, ((\forall w:\operatorname{List}(Y), (0\leq\operatorname{archiveProb}(K,E,x,w)))\land (\forall w:\operatorname{List}(Y), (n<\operatorname{length}(w)\Rightarrow\operatorname{archiveProb}(K,E,x,w)=0))\land \sum_{w\in \operatorname{leaves}(E)}\operatorname{archiveProb}(K,E,x,w)=1))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteResiduals/FiniteResidualStopping.archive_probability_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

leaves(E) is the finite set of complete archive words at which E stops. The first conjunct is pointwise nonnegativity, the second excludes words longer than n, and the last sums the archive probabilities over leaves(E). For step, the prefix sets y::leaves(E(y)) are pairwise disjoint. Their total mass is the sum over y and r of K(x,(y,r)) times the continuation mass one. Row normalization gives one. At stop, the sole leaf is the empty word.

If a constant c is recorded only initially, the complete record is (c,w), with inverse given by the word projection. If it is recorded initially and at every node, the record is (c,map(y mapped to (y,c),w)), again with inverse given by projecting the labels. Both encodings are injective on actual archives, including the empty archive, and pushing any of the finite laws through them preserves and reflects equality. Prefix decisions pull back through these same encodings, so neither convention supplies additional control. This is a finite single-action result; it makes no unrestricted stochastic decoder or semantic-factorization assertion.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteResiduals/FiniteResidualStopping.archive_probability_law`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteResiduals/FiniteResidualStopping.residual_sound`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteResiduals/FiniteResidualStopping.trace_iff_stopping`
- Dependency: [D5/S3/Estimation/DecisionRisk/DescentDefectBounds](../../../../Estimation/DecisionRisk/DescentDefectBounds.md)
