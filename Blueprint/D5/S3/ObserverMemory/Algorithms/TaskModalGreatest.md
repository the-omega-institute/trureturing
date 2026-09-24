# Task-modal equivalence and successor matching

## Abstract

Finite task-modal tests characterize the greatest task-preserving successor equivalence.

**Theorem 1.1 (The greatest stable task equivalence for image-finite transitions).**

$$\begin{gathered}\forall X,U,J,Y,R,f, \operatorname{ImageFinite}(R) \Rightarrow\\{}\operatorname{Equivalence}(\operatorname{TaskModalEq}(R,f)) \land \operatorname{Tasks}(\operatorname{TaskModalEq}(R,f),f) \land \operatorname{Match}(\operatorname{TaskModalEq}(R,f),R) \land\\{}(\forall E, \operatorname{Equivalence}(E) \land \operatorname{Tasks}(E,f) \land \operatorname{Match}(E,R) \Rightarrow \forall x,y, \operatorname{E}(x,y) \Rightarrow \operatorname{TaskModalEq}(R,f,x,y))\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/TaskModalGreatest.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X be any state type, U any action type, J any task-index type, and Y a family of output types indexed by J. Each task f(j) maps X to Y(j). A labelled relation R(u,x,x') describes actual successors. The sole finiteness assumption is that, for every u and x, the set of x' with R(u,x,x') is finite.

TaskFormula is generated independently by truth, every atom f(j)=v, negation, binary conjunction, and existential labelled modalities. Finite conjunctions are iterated binary conjunctions ending in truth. The predicate task_satisfies interprets an atom by equality of the current task value, and a modality by one actual successor satisfying its entire argument. TaskModalEq(R,f) is agreement on every such finite formula.

Tasks(E,f) means that E-related states have equal values for every task. Match(E,R) means that each actual successor of either state has an E-related actual successor of the other, with the same action label. Both conditions are expanded below. TaskModalEq is an equivalence satisfying these conditions and containing every other equivalence satisfying them.

$\begin{gathered}\operatorname{Tasks}(E,f) \iff \forall x,y, \operatorname{E}(x,y) \Rightarrow \forall j, \operatorname{f}(j,x) = \operatorname{f}(j,y)\\{}\operatorname{Match}(E,R) \iff \forall x,y, \operatorname{E}(x,y) \Rightarrow \forall u,\\{}(\forall s, \operatorname{R}(u,x,s) \Rightarrow \exists t, \operatorname{R}(u,y,t) \land \operatorname{E}(s,t)) \land (\forall t, \operatorname{R}(u,y,t) \Rightarrow \exists s, \operatorname{R}(u,x,s) \land \operatorname{E}(s,t))\end{gathered}$

Encode an observation (j,v) as a self-loop present exactly when f(j,x)=v, using the disjoint sum of action labels and dependent task-value pairs. Translate each task atom to its observation diamond of truth. Conversely, translate an observation diamond of a formula to the corresponding task atom conjoined with the translated formula at the same state. Structural induction proves that both translations preserve satisfaction for every formula and every state, without a finiteness assumption.

For Hennessy-Milner formulas, a failed successor match supplies a distinguishing formula for each potential matching successor. Negation orients these formulas, and image-finiteness permits their conjunction. Its diamond contradicts agreement of the source states. An empty set of potential matches gives the empty conjunction, truth. The reverse inclusion follows by induction on Hennessy-Milner formulas and the satisfaction translations.

The state, action, and task families may be infinite. Transitions may branch or be absent. Conjunction inside a modality is tested at one common successor, so agreement of separate possible traces does not replace branching agreement. No conclusion for arbitrary infinitely branching systems is asserted.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/TaskModalGreatest.result`
