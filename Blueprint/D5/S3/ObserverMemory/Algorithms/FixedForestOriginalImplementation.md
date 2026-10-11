# Stationary realization of a fixed physical forest

## Abstract

A feasible original assignment yields a total stationary table faithful to every finite physical history.

For arbitrary P>1, h, ell and e, fix the entire original physical forest and prescribed source identifications, assume structural compatibility and choose any injective same-digit assignment hitting every extra target. The nominal carrier is the disjoint sum Terminal(ZMod(3P)), Read(Unit+Target), Prefix(Fin ell) and Tail(Sigma q, Fin(L(q))). The stationary instruction table sees only this control tag. Wait adds one, read preserves phase and returns the absolute physical digit, and each terminal stores its original x. No time, phase, input label or history is a table input.

Each occupied row requests the source node's literal wait and target, or its original leaf label. H/K and H1/K1 each have a common request. Tail index j means j+1 remaining unit waits; prefix states perform exactly ell unit waits. Unoccupied digits use the existing H_0. All nominal tags are charged, even before reachability is established. Neither read-control acyclicity nor any bound of waits by P is imposed.

OriginalImplementation presents the fixed raw domain on any finite nominal controller. Its fields preserve the entire original word and all-input event configurations, literal continuations, precisely the A/B binary target merge, the common production and resolving targets, resolving separation, distinct prescribed shared rows, J=Xi=1 and the exact actual read count. History and target maps are proof metadata, not stationary table inputs. The record assumes neither Compatible, an assignment, an injection nor a capacity bound.

**Theorem 1.1 (The incompatible raw domain is empty).**

$$\forall P:\mathbb {N},{\forall h:\mathbb {N},{\forall ell:\mathbb {N},{\forall Node:Type,{\forall finiteNode:\operatorname {Fintype}(Node),{\forall eqNode:\operatorname {DecidableEq}(Node),{\forall hP:1<P,{\forall F:\operatorname {PhysicalForest}(P,h,ell,Node,hP),{\forall e:\mathbb {N},{\forall R:\operatorname {Prescribed}(F),{{\operatorname {notCompatible}(F,R,e)}\implies{\operatorname {noOriginalImplementationOnAnyFiniteNominalCarrier}(F,R,e)}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/FixedForestOriginalImplementation.incompatible_domain_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Forced canonical target equality implies actual read-row equality under the prescribed identities. The two prescribed double rows already account for all J+Xi=2 history excess. A failed source compatibility check therefore contradicts an original fixed-domain implementation.

**Theorem 1.2 (The constructed original word facts).**

$$\forall P:\mathbb {N},{\forall h:\mathbb {N},{\forall ell:\mathbb {N},{\forall Node:Type,{\forall finiteNode:\operatorname {Fintype}(Node),{\forall eqNode:\operatorname {DecidableEq}(Node),{\forall hP:1<P,{\forall F:\operatorname {PhysicalForest}(P,h,ell,Node,hP),{\forall e:\mathbb {N},{\forall R:\operatorname {Prescribed}(F),{\forall alpha:\operatorname {Assignment}(F,R,e),{{\operatorname {Compatible}(F,R,e)}\implies{\operatorname {OriginalWordData}(F,\operatorname {controller}(F,R,alpha))}}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/FixedForestOriginalImplementation.wordData` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The table proves all prefix waits, exact read events, all positive inter-read waits and the fixed final halt for every original label. initialize_original_paths converts these facts to Initialized on arbitrary nominal carriers without assuming Initialized or a capacity bound.

**Theorem 1.3 (Every charged tag is reached).**

$$\forall P:\mathbb {N},{\forall h:\mathbb {N},{\forall ell:\mathbb {N},{\forall Node:Type,{\forall finiteNode:\operatorname {Fintype}(Node),{\forall eqNode:\operatorname {DecidableEq}(Node),{\forall hP:1<P,{\forall F:\operatorname {PhysicalForest}(P,h,ell,Node,hP),{\forall e:\mathbb {N},{\forall R:\operatorname {Prescribed}(F),{\forall alpha:\operatorname {Assignment}(F,R,e),{{\operatorname {Compatible}(F,R,e)}\implies{\forall state:\operatorname {State}(F,R,alpha),{\operatorname {Reachable}(F,R,alpha,state)}}}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/FixedForestOriginalImplementation.all_states_reachable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each core target has a physical arrival and each extra has an ordinary arrival. A source request attains every finite joint maximum L and visits its entire tail. Every original label reaches its terminal; every original input visits the common prefix. This proves control-state reachability, without restricting the codomain.

**Theorem 1.4 (Actual rows are the placed histories).**

$$\forall P:\mathbb {N},{\forall h:\mathbb {N},{\forall ell:\mathbb {N},{\forall Node:Type,{\forall finiteNode:\operatorname {Fintype}(Node),{\forall eqNode:\operatorname {DecidableEq}(Node),{\forall hP:1<P,{\forall F:\operatorname {PhysicalForest}(P,h,ell,Node,hP),{\forall e:\mathbb {N},{\forall R:\operatorname {Prescribed}(F),{\forall alpha:\operatorname {Assignment}(F,R,e),{{\operatorname {Compatible}(F,R,e)}\implies{\operatorname {actualRowIffHistoryPlacement}(F,R,alpha)}}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/FixedForestOriginalImplementation.actual_row_correspondence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An actual initialized read occurs at one original event time; conversely every history has a supporting original input. Actual used digit rows are exactly the source placement.

**Theorem 1.5 (Original fixed-domain operational construction).**

$$\forall P:\mathbb {N},{\forall h:\mathbb {N},{\forall ell:\mathbb {N},{\forall Node:Type,{\forall finiteNode:\operatorname {Fintype}(Node),{\forall eqNode:\operatorname {DecidableEq}(Node),{\forall hP:1<P,{\forall F:\operatorname {PhysicalForest}(P,h,ell,Node,hP),{\forall e:\mathbb {N},{\forall R:\operatorname {Prescribed}(F),{\forall alpha:\operatorname {Assignment}(F,R,e),{{\operatorname {Compatible}(F,R,e)}\implies{\operatorname {originalOperationalHandoff}(F,R,alpha)}}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/FixedForestOriginalImplementation.operational_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every compatible physical forest and same-digit assignment at arbitrary P>1, h, ell and e, the existing controller on the full State carrier has an OriginalImplementation and Initialized witness. Every charged state is reachable and its cardinal is 3P+2N+1+ell+2e+sum_q(L(q)-1). The readControl map is the tagged read state of each placed history; requestTarget is the tagged read state of its next target. Literal Waits follows the existing full unit chain. The tagged row injection preserves the exact row and edge images and all edge-fiber cardinalities, so canonical J=Xi=1 become rawJ=rawXi=1 on (readControl(n),color(n)). Binary target equality is exactly the A/B merge, production and resolving requests agree, Z is separate from every binary target and the two shared rows remain distinct. The incompatible branch quantifies over this same OriginalImplementation class.

**Theorem 1.6 (Exact charged nominal capacity).**

$$\forall P:\mathbb {N},{\forall h:\mathbb {N},{\forall ell:\mathbb {N},{\forall Node:Type,{\forall finiteNode:\operatorname {Fintype}(Node),{\forall eqNode:\operatorname {DecidableEq}(Node),{\forall hP:1<P,{\forall F:\operatorname {PhysicalForest}(P,h,ell,Node,hP),{\forall e:\mathbb {N},{\forall R:\operatorname {Prescribed}(F),{\forall alpha:\operatorname {Assignment}(F,R,e),{\operatorname {card}(\operatorname {State}(F,R,alpha))=\operatorname {originalCapacity}(P,ell,e,\operatorname {jointTailExcess}(F,R,alpha))}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/FixedForestOriginalImplementation.nominal_capacity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cardinal is 3P+2N+1+ell+2e+sum_q(L(q)-1), with N=3(P-1). The exact actual read count is N+1+e, and J=s=Xi=1. Three spare digits at one extra target share one joint maximum and are not charged independently.

realize retains OriginalImplementation, Initialized, exact events and unit phases, final outputs, all-tag reachability, three roots, all 3P original leaves, the actual read inventory, the graph statistics and the capacity formula in one construction. The corresponding capacity theorem supplies arbitrary-controller extraction and an attained minimum. The simultaneous e=0 threshold formula is a separate statement.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedForestOriginalImplementation.actual_row_correspondence`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedForestOriginalImplementation.all_states_reachable`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedForestOriginalImplementation.incompatible_domain_empty`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedForestOriginalImplementation.nominal_capacity`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedForestOriginalImplementation.operational_realization`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedForestOriginalImplementation.wordData`
- Dependency: [D5/S3/ObserverMemory/Algorithms/FixedForestPhysicalExecution](FixedForestPhysicalExecution.md)
