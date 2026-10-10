# Physical execution of the stationary table

## Abstract

The total stationary unit table follows every original physical history exactly.

For each original label, induction follows its finite sequence of history events. The control graph may have cycles. Literal waits count actual unit actions, including complete wraps. The table depends only on the charged nominal control state.

**Definition 1.1 (Lossless original event incidences).**

$$\forall P:\mathbb {N},{\forall h:\mathbb {N},{\forall ell:\mathbb {N},{\forall Node:Type,{\forall finiteNode:\operatorname {Fintype}(Node),{\forall eqNode:\operatorname {DecidableEq}(Node),{\forall hP:1<P,{\forall F:\operatorname {PhysicalForest}(P,h,ell,Node,hP),{\operatorname {equivalence}(\operatorname {boundedLabelledEvents}(F,h),\operatorname {supportedHistoryIncidences}(F))}}}}}}}}$$

*Formalization.* `D5/S3/ObserverMemory/Algorithms/FixedForestPhysicalExecution.eventIncidenceEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first carrier consists of pairs (x,i) with x in ZMod(3P), i in Fin h and i<reads(x). The second consists of pairs (x,n) with x in support(n). The forward map keeps x and sends i to event(x,i); the inverse read index is level(n). Event support, support completeness and event levels prove both maps lossless. This equivalence is used to reach each history in the constructed initialized execution. It concerns the existing PhysicalForest event carrier and does not assert an equivalence with an independently formalized source domain.

**Theorem 1.2 (Exact original indexed reads).**

$$\forall P:\mathbb {N},{\forall h:\mathbb {N},{\forall ell:\mathbb {N},{\forall Node:Type,{\forall finiteNode:\operatorname {Fintype}(Node),{\forall eqNode:\operatorname {DecidableEq}(Node),{\forall hP:1<P,{\forall F:\operatorname {PhysicalForest}(P,h,ell,Node,hP),{\forall e:\mathbb {N},{\forall R:\operatorname {Prescribed}(F),{\forall alpha:\operatorname {Assignment}(F,R,e),{{\operatorname {Compatible}(F,R,e)}\implies{\forall x:\operatorname {Label}(P),{\forall i:\mathbb {N},{{i<\operatorname {reads}(F,x)}\implies{\operatorname {runAtOriginalEvent}(F,R,alpha,x,i)=\operatorname {originalPhaseAndPlacedRead}(F,R,alpha,x,i)}}}}}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/FixedForestPhysicalExecution.physical_event_run` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction is on the finite path of each original x. The actual next digit chooses its original placed child at exactly shift+level. Equal physical phase residues do not shorten literal waits.

**Theorem 1.3 (Every literal unit position).**

$$\forall P:\mathbb {N},{\forall h:\mathbb {N},{\forall ell:\mathbb {N},{\forall Node:Type,{\forall finiteNode:\operatorname {Fintype}(Node),{\forall eqNode:\operatorname {DecidableEq}(Node),{\forall hP:1<P,{\forall F:\operatorname {PhysicalForest}(P,h,ell,Node,hP),{\forall e:\mathbb {N},{\forall R:\operatorname {Prescribed}(F),{\forall alpha:\operatorname {Assignment}(F,R,e),{{\operatorname {Compatible}(F,R,e)}\implies{\operatorname {exactLiteralWaitRun}(F,R,alpha)}}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/FixedForestPhysicalExecution.physical_wait_run` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonfinal event and every k below its positive literal delay, execution at eventTime+1+k has phase x+shift+k and the tagged tail with delay-1-k remaining index. The next read has the preserved absolute child digit and deadline.

**Theorem 1.4 (Immediate original fixed output).**

$$\forall P:\mathbb {N},{\forall h:\mathbb {N},{\forall ell:\mathbb {N},{\forall Node:Type,{\forall finiteNode:\operatorname {Fintype}(Node),{\forall eqNode:\operatorname {DecidableEq}(Node),{\forall hP:1<P,{\forall F:\operatorname {PhysicalForest}(P,h,ell,Node,hP),{\forall e:\mathbb {N},{\forall R:\operatorname {Prescribed}(F),{\forall alpha:\operatorname {Assignment}(F,R,e),{{\operatorname {Compatible}(F,R,e)}\implies{\forall x:\operatorname {Label}(P),{\operatorname {runAtStopTime}(F,R,alpha,x)=\operatorname {lastPhaseAndOriginalTerminal}(F,R,alpha,x)}}}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/FixedForestPhysicalExecution.physical_terminal_run` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The final original read immediately selects H_x; the stop time adds one read action and no halt action.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedForestPhysicalExecution.eventIncidenceEquiv`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedForestPhysicalExecution.physical_event_run`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedForestPhysicalExecution.physical_terminal_run`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedForestPhysicalExecution.physical_wait_run`
- Dependency: [D5/S3/ObserverMemory/Algorithms/FixedForestSlotGraph](FixedForestSlotGraph.md)
