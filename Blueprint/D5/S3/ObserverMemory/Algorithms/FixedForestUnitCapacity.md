# Extraction and the attained fixed-forest capacity

## Abstract

The original fixed physical domain has an attained minimum of the joint target tails.

Fix arbitrary P>1, h, ell and e and one complete physical forest with its prescribed identities. OriginalImplementation quantifies over any finite nominal carrier Q and one total stationary table. Its actual history rows and literal requests determine the inventory and assignment. Neither an assignment nor a numerical capacity bound is an implementation premise.

**Definition 1.1 (All actual nonroot targets).**

$$\forall P:\mathbb {N},{\forall h:\mathbb {N},{\forall ell:\mathbb {N},{\forall Node:Type,{[\operatorname {Fintype}(Node)][\operatorname {DecidableEq}(Node)]\forall hP:1<P,{\forall F:\operatorname {PhysicalForest}(P,h,ell,Node,hP),{\forall e:\mathbb {N},{\forall R:\operatorname {Prescribed}(F),{\forall Q:Type_{u},{[\operatorname {Fintype}(Q)][\operatorname {DecidableEq}(Q)]\forall C:\operatorname {Controller}(P,Q),{\forall I:\operatorname {OriginalImplementation}(F,R,C,e),{\operatorname {equivalence}(\operatorname {Target}(F,R,e),\operatorname {NonrootRead}(C,hP,\operatorname {paths}(F,R,I)))}}}}}}}}}}}$$

*Formalization.* `D5/S3/ObserverMemory/Algorithms/FixedForestUnitCapacity.targetEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The forced binary representatives and the resolving target inject into actual nonroot reads. The common first read cannot occur at any later history. Subtracting the forced target count from the actual count N+1+e leaves exactly e targets. Fin e enumerates that entire complement, so the equivalence includes every extra target.

**Definition 1.2 (The original same-digit assignment).**

$$\forall P:\mathbb {N},{\forall h:\mathbb {N},{\forall ell:\mathbb {N},{\forall Node:Type,{[\operatorname {Fintype}(Node)][\operatorname {DecidableEq}(Node)]\forall hP:1<P,{\forall F:\operatorname {PhysicalForest}(P,h,ell,Node,hP),{\forall e:\mathbb {N},{\forall R:\operatorname {Prescribed}(F),{\forall Q:Type_{u},{[\operatorname {Fintype}(Q)][\operatorname {DecidableEq}(Q)]\forall C:\operatorname {Controller}(P,Q),{\forall I:\operatorname {OriginalImplementation}(F,R,C,e),{\operatorname {Assignment}(F,R,e)}}}}}}}}}}}$$

*Formalization.* `D5/S3/ObserverMemory/Algorithms/FixedForestUnitCapacity.assignment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Send each ordinary unary demand to its actual child target and original absolute digit. The two distinct prescribed double rows exhaust rawJ+rawXi=2. An ordinary child cannot share a forced row or another ordinary child's row. Every extra actual read has an incoming physical request; a binary or exceptional request would instead place it in the forced core. Thus the map is injective, preserves digits and hits every extra target.

**Theorem 1.3 (Every internal literal request has its actual target).**

$$\forall P:\mathbb {N},{\forall h:\mathbb {N},{\forall ell:\mathbb {N},{\forall Node:Type,{[\operatorname {Fintype}(Node)][\operatorname {DecidableEq}(Node)]\forall hP:1<P,{\forall F:\operatorname {PhysicalForest}(P,h,ell,Node,hP),{\forall e:\mathbb {N},{\forall R:\operatorname {Prescribed}(F),{\forall Q:Type_{u},{[\operatorname {Fintype}(Q)][\operatorname {DecidableEq}(Q)]\forall C:\operatorname {Controller}(P,Q),{\forall I:\operatorname {OriginalImplementation}(F,R,C,e),{\forall n:Node,{{\operatorname {Internal}(F,n)}\implies{\operatorname {val}(\operatorname {val}(\operatorname {targetEquiv}(F,R,I,\operatorname {nextTarget}(F,R,\operatorname {assignment}(F,R,I),n))))=\operatorname {requestTarget}(I,n)}}}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/FixedForestUnitCapacity.request_target` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Binary requests use their prescribed representative. K uses H's target, and K1 uses H1's resolving target. Every remaining internal node is exactly one ordinary unary demand.

**Theorem 1.4 (One joint maximum equals the actual literal maximum).**

$$\forall P:\mathbb {N},{\forall h:\mathbb {N},{\forall ell:\mathbb {N},{\forall Node:Type,{[\operatorname {Fintype}(Node)][\operatorname {DecidableEq}(Node)]\forall hP:1<P,{\forall F:\operatorname {PhysicalForest}(P,h,ell,Node,hP),{\forall e:\mathbb {N},{\forall R:\operatorname {Prescribed}(F),{\forall Q:Type_{u},{[\operatorname {Fintype}(Q)][\operatorname {DecidableEq}(Q)]\forall C:\operatorname {Controller}(P,Q),{\forall I:\operatorname {OriginalImplementation}(F,R,C,e),{\forall q:\operatorname {Target}(F,R,e),{\operatorname {L}(F,R,\operatorname {assignment}(F,R,I),q)=\operatorname {actualL}(C,hP,\operatorname {paths}(F,R,I),\operatorname {targetEquiv}(F,R,I,q))}}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/FixedForestUnitCapacity.actualL_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A source request attains each finite joint maximum and is an actual Arrival. Conversely any actual arrival starts at one original indexed read and consists of pure waits to the next read. Deterministic first-future-read uniqueness identifies its literal length and actual target. Hence the two maxima agree, including every ordinary request and all three digits of an extra.

**Theorem 1.5 (The lower bound charges the full original Q).**

$$\forall P:\mathbb {N},{\forall h:\mathbb {N},{\forall ell:\mathbb {N},{\forall Node:Type,{[\operatorname {Fintype}(Node)][\operatorname {DecidableEq}(Node)]\forall hP:1<P,{\forall F:\operatorname {PhysicalForest}(P,h,ell,Node,hP),{\forall e:\mathbb {N},{\forall R:\operatorname {Prescribed}(F),{\forall Q:Type_{u},{[\operatorname {Fintype}(Q)][\operatorname {DecidableEq}(Q)]\forall C:\operatorname {Controller}(P,Q),{\forall I:\operatorname {OriginalImplementation}(F,R,C,e),{3P+2{3{P-1}}+1+ell+2e+\sum_{q:\operatorname {Target}(F,R,e)}{\operatorname {L}(F,R,\operatorname {assignment}(F,R,I),q)-1}\le\operatorname {card}(Q)}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/FixedForestUnitCapacity.nominal_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Transport the joint target sum through the actual-target equivalence. The disjoint resource embedding contains all original terminals, all actual reads, the entire common prefix and one longest literal tail per actual nonroot target. Its codomain is the original full Q. Finite cardinality gives the capacity inequality, retaining every unused nominal state.

**Theorem 1.6 (Compatibility and matching characterize existence).**

$$\forall P:\mathbb {N},{\forall h:\mathbb {N},{\forall ell:\mathbb {N},{\forall Node:Type,{[\operatorname {Fintype}(Node)][\operatorname {DecidableEq}(Node)]\forall hP:1<P,{\forall F:\operatorname {PhysicalForest}(P,h,ell,Node,hP),{\forall e:\mathbb {N},{\forall R:\operatorname {Prescribed}(F),{\operatorname {Nonempty}(\operatorname {capacities}(F,R,e))\iff{\operatorname {Compatible}(F,R,e)\land\operatorname {Nonempty}(\operatorname {Assignment}(F,R,e))}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/FixedForestUnitCapacity.original_domain_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every original implementation yields both structural compatibility and the extracted assignment. Conversely a compatible assignment is realized by the existing total stationary construction. The domain is the given fixed forest and identifications; no acquisition strategy is varied.

**Theorem 1.7 (An attained exact nominal minimum).**

$$\forall P:\mathbb {N},{\forall h:\mathbb {N},{\forall ell:\mathbb {N},{\forall Node:Type,{[\operatorname {Fintype}(Node)][\operatorname {DecidableEq}(Node)]\forall hP:1<P,{\forall F:\operatorname {PhysicalForest}(P,h,ell,Node,hP),{\forall e:\mathbb {N},{\forall R:\operatorname {Prescribed}(F),{{{\operatorname {Compatible}(F,R,e)}\land{\operatorname {Nonempty}(\operatorname {Assignment}(F,R,e))}}\implies{\exists alpha:\operatorname {Assignment}(F,R,e),{{\operatorname {Nonempty}(\operatorname {Realization}(F,R,alpha))}\land{\forall beta:\operatorname {Assignment}(F,R,e),{\sum_{q:\operatorname {Target}(F,R,e)}{\operatorname {L}(F,R,alpha,q)-1}\le\sum_{q:\operatorname {Target}(F,R,e)}{\operatorname {L}(F,R,beta,q)-1}}}\land{\operatorname {IsLeast}(\operatorname {capacities}(F,R,e),3P+2{3{P-1}}+1+ell+2e+\sum_{q:\operatorname {Target}(F,R,e)}{\operatorname {L}(F,R,alpha,q)-1})}\land{\forall Q:Type_{u},{[\operatorname {Fintype}(Q)][\operatorname {DecidableEq}(Q)]\forall C:\operatorname {Controller}(P,Q),{{\operatorname {Nonempty}(\operatorname {OriginalImplementation}(F,R,C,e))}\implies{3P+2{3{P-1}}+1+ell+2e+\sum_{q:\operatorname {Target}(F,R,e)}{\operatorname {L}(F,R,alpha,q)-1}\le\operatorname {card}(Q)}}}}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/FixedForestUnitCapacity.attained_fixed_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original assignment class is finite. Choose a minimizer of sum_q(L_alpha(q)-1) using finite minimum selection. Its Realization preserves all original paths, phases, labels and deadlines, the graph statistics, and reachability of all constructed states. Its exact nominal cardinal belongs to the original capacity set. Every competing nominal controller extracts an assignment and is bounded by the full-Q embedding, so the same cardinal is IsLeast. The universal lower bound also quantifies over finite carriers in arbitrary universes.

**Theorem 1.8 (Empty domains have no minimum).**

$$\forall P:\mathbb {N},{\forall h:\mathbb {N},{\forall ell:\mathbb {N},{\forall Node:Type,{[\operatorname {Fintype}(Node)][\operatorname {DecidableEq}(Node)]\forall hP:1<P,{\forall F:\operatorname {PhysicalForest}(P,h,ell,Node,hP),{\forall e:\mathbb {N},{\forall R:\operatorname {Prescribed}(F),{{\neg {{\operatorname {Compatible}(F,R,e)}\land{\operatorname {Nonempty}(\operatorname {Assignment}(F,R,e))}}}\implies{{\operatorname {capacities}(F,R,e)=\emptyset}\land{\forall n:\mathbb {N},{\neg \operatorname {IsLeast}(\operatorname {capacities}(F,R,e),n)}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/FixedForestUnitCapacity.empty_domain_no_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Failure of either the prescribed compatibility check or assignment existence empties the original capacity set. A least element must belong to its set, so no minimum is asserted.

**Theorem 1.9 (The simultaneous threshold formula is the actual operational minimum).**

$$\forall P:\mathbb {N},{\forall h:\mathbb {N},{\forall ell:\mathbb {N},{\forall Node:Type,{[\operatorname {Fintype}(Node)][\operatorname {DecidableEq}(Node)]\forall hP:1<P,{\forall F:\operatorname {PhysicalForest}(P,h,ell,Node,hP),{\forall R:\operatorname {Prescribed}(F),{{{\operatorname {Compatible}(F,R,0)}\land{\forall c:\operatorname {Fin}(3),{\operatorname {A}(F,R,c,1)\le\operatorname {B}(F,R,c,1)}}}\implies{\exists alpha:\operatorname {Assignment}(F,R,0),{{\operatorname {Nonempty}(\operatorname {Realization}(F,R,alpha))}\land{\forall c:\operatorname {Fin}(3),{\forall k:\mathbb {N},{\operatorname {card}(\{ d:\operatorname {ColorDemand}(F,R,c)\mid {k\le\operatorname {delay}(F,\operatorname {val}(\operatorname {val}(d)))}\land{\operatorname {baseline}(F,R,\operatorname {target}(\operatorname {slot}(alpha,\operatorname {val}(d))))<k}\})=[\operatorname {A}(F,R,c,k)-\operatorname {B}(F,R,c,k)]_{+}}}}\land{\sum_{q:\operatorname {Target}(F,R,0)}{\operatorname {L}(F,R,alpha,q)-1}=\operatorname {Ezero}(F,R)+\sum_{c:\operatorname {Fin}(3)}{\sum_{k\in \operatorname {Icc}(2,\operatorname {thresholdMax}(F,R))}{[\operatorname {A}(F,R,c,k)-\operatorname {B}(F,R,c,k)]_{+}}}}\land{\operatorname {IsLeast}(\operatorname {capacities}(F,R,0),3P+2{3{P-1}}+1+ell+\operatorname {Ezero}(F,R)+\sum_{c:\operatorname {Fin}(3)}{\sum_{k\in \operatorname {Icc}(2,\operatorname {thresholdMax}(F,R))}{[\operatorname {A}(F,R,c,k)-\operatorname {B}(F,R,c,k)]_{+}}})}\land{\forall Q:Type_{u},{[\operatorname {Fintype}(Q)][\operatorname {DecidableEq}(Q)]\forall C:\operatorname {Controller}(P,Q),{{\operatorname {Nonempty}(\operatorname {OriginalImplementation}(F,R,C,0))}\implies{3P+2{3{P-1}}+1+ell+\operatorname {Ezero}(F,R)+\sum_{c:\operatorname {Fin}(3)}{\sum_{k\in \operatorname {Icc}(2,\operatorname {thresholdMax}(F,R))}{[\operatorname {A}(F,R,c,k)-\operatorname {B}(F,R,c,k)]_{+}}}\le\operatorname {card}(Q)}}}}\land{\forall c:\operatorname {Fin}(3),{\forall k:\mathbb {N},{{\operatorname {thresholdMax}(F,R)<k}\implies{{\operatorname {A}(F,R,c,k)=0}\land{\operatorname {B}(F,R,c,k)=0}}}}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/FixedForestUnitCapacity.attained_e0_threshold_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At e=0 choose the single descending same-digit assignment. Its joint tail excess is E0+sum_c sum_{2<=k<=thresholdMax}(A(c,k)-B(c,k))_+. Realize that very assignment with the original total unit table. Every competing full nominal carrier extracts an original injection, whose threshold crossings bound the same sum from below. Thus the threshold cardinal belongs to, and is IsLeast of, the original capacity set. The statement retains one alpha for all k and also bounds arbitrary finite Q.

**Theorem 1.10 (The complete integer fixed-forest capacity statement).**

$$\forall p:\mathbb {Z},{\forall hp:1<p,{\forall h:\mathbb {N},{\forall ell:\mathbb {N},{\forall e:\mathbb {N},{\forall Node:Type,{[\operatorname {Fintype}(Node)][\operatorname {DecidableEq}(Node)]\forall F:\operatorname {PhysicalForest}(\operatorname {toNat}(p),h,ell,Node,\operatorname {natGreaterThanOne}(p,hp)),{\forall R:\operatorname {Prescribed}(F),{{\operatorname {intCast}(3\operatorname {toNat}(p))=3p}\land{\operatorname {intCast}(3{\operatorname {toNat}(p)-1})=3{p-1}}\land{\operatorname {Nonempty}(\operatorname {capacities}(F,R,e))\iff{\operatorname {Compatible}(F,R,e)}\land{\operatorname {Nonempty}(\operatorname {Assignment}(F,R,e))}}\land{{{\operatorname {Compatible}(F,R,e)}\land{\operatorname {Nonempty}(\operatorname {Assignment}(F,R,e))}}\implies{\exists alpha:\operatorname {Assignment}(F,R,e),{{\operatorname {Nonempty}(\operatorname {Realization}(F,R,alpha))}\land{\forall beta:\operatorname {Assignment}(F,R,e),{\sum_{q:\operatorname {Target}(F,R,e)}{\operatorname {L}(F,R,alpha,q)-1}\le\sum_{q:\operatorname {Target}(F,R,e)}{\operatorname {L}(F,R,beta,q)-1}}}\land{\operatorname {IsLeast}(\operatorname {capacities}(F,R,e),3\operatorname {toNat}(p)+2{3{\operatorname {toNat}(p)-1}}+1+ell+2e+\sum_{q:\operatorname {Target}(F,R,e)}{\operatorname {L}(F,R,alpha,q)-1})}\land{\forall Q:Type_{u},{[\operatorname {Fintype}(Q)][\operatorname {DecidableEq}(Q)]\forall C:\operatorname {Controller}(\operatorname {toNat}(p),Q),{{\operatorname {Nonempty}(\operatorname {OriginalImplementation}(F,R,C,e))}\implies{3\operatorname {toNat}(p)+2{3{\operatorname {toNat}(p)-1}}+1+ell+2e+\sum_{q:\operatorname {Target}(F,R,e)}{\operatorname {L}(F,R,alpha,q)-1}\le\operatorname {card}(Q)}}}}}}}\land{{\neg {{\operatorname {Compatible}(F,R,e)}\land{\operatorname {Nonempty}(\operatorname {Assignment}(F,R,e))}}}\implies{{\operatorname {capacities}(F,R,e)=\emptyset}\land{\forall n:\mathbb {N},{\neg \operatorname {IsLeast}(\operatorname {capacities}(F,R,e),n)}}}}\land{\operatorname {Nonempty}(\operatorname {capacities}(F,R,0))\iff{\operatorname {Compatible}(F,R,0)}\land{\forall c:\operatorname {Fin}(3),{\operatorname {A}(F,R,c,1)\le\operatorname {B}(F,R,c,1)}}}\land{{{\operatorname {Compatible}(F,R,0)}\land{\forall c:\operatorname {Fin}(3),{\operatorname {A}(F,R,c,1)\le\operatorname {B}(F,R,c,1)}}}\implies{\exists alpha:\operatorname {Assignment}(F,R,0),{{\operatorname {Nonempty}(\operatorname {Realization}(F,R,alpha))}\land{\forall c:\operatorname {Fin}(3),{\forall k:\mathbb {N},{\operatorname {card}(\{ d:\operatorname {ColorDemand}(F,R,c)\mid {k\le\operatorname {delay}(F,\operatorname {val}(\operatorname {val}(d)))}\land{\operatorname {baseline}(F,R,\operatorname {target}(\operatorname {slot}(alpha,\operatorname {val}(d))))<k}\})=[\operatorname {A}(F,R,c,k)-\operatorname {B}(F,R,c,k)]_{+}}}}\land{\sum_{q:\operatorname {Target}(F,R,0)}{\operatorname {L}(F,R,alpha,q)-1}=\operatorname {Ezero}(F,R)+\sum_{c:\operatorname {Fin}(3)}{\sum_{k\in \operatorname {Icc}(2,\operatorname {thresholdMax}(F,R))}{[\operatorname {A}(F,R,c,k)-\operatorname {B}(F,R,c,k)]_{+}}}}\land{\operatorname {IsLeast}(\operatorname {capacities}(F,R,0),3\operatorname {toNat}(p)+2{3{\operatorname {toNat}(p)-1}}+1+ell+\operatorname {Ezero}(F,R)+\sum_{c:\operatorname {Fin}(3)}{\sum_{k\in \operatorname {Icc}(2,\operatorname {thresholdMax}(F,R))}{[\operatorname {A}(F,R,c,k)-\operatorname {B}(F,R,c,k)]_{+}}})}\land{\forall Q:Type_{u},{[\operatorname {Fintype}(Q)][\operatorname {DecidableEq}(Q)]\forall C:\operatorname {Controller}(\operatorname {toNat}(p),Q),{{\operatorname {Nonempty}(\operatorname {OriginalImplementation}(F,R,C,0))}\implies{3\operatorname {toNat}(p)+2{3{\operatorname {toNat}(p)-1}}+1+ell+\operatorname {Ezero}(F,R)+\sum_{c:\operatorname {Fin}(3)}{\sum_{k\in \operatorname {Icc}(2,\operatorname {thresholdMax}(F,R))}{[\operatorname {A}(F,R,c,k)-\operatorname {B}(F,R,c,k)]_{+}}}\le\operatorname {card}(Q)}}}}\land{\forall c:\operatorname {Fin}(3),{\forall k:\mathbb {N},{{\operatorname {thresholdMax}(F,R)<k}\implies{{\operatorname {A}(F,R,c,k)=0}\land{\operatorname {B}(F,R,c,k)=0}}}}}}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/FixedForestUnitCapacity.original_context8319` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each integer p>1, P=toNat(p) preserves M=3p and N=3(p-1) exactly. The same F and prescribed identities determine all e domains. The statement includes existence, the attained joint maximum-tail minimum, empty domains, e=0 numerical feasibility and its attained simultaneous threshold specialization.

Every original x in ZMod(3P) starts in one common initial control state. W adds one phase unit, R preserves the phase and reads floor([s]_(3P)/P), and H_x emits the original x. The finite words have prefix W^ell R followed by positive literal wait/read blocks, at most h reads, and stop immediately after the last read. The full nominal Q includes unused states, all counters, prefix states and terminal labels. The stationary instruction receives no phase, source label, time, history or external register. Singleton continuations, positive literal waits and terminating read-control cycles are allowed.

The complete physical forest retains each (x,i), original labels, absolute phase x+shift modulo 3P, literal waits, child digits, deadlines and exact support intervals within the current digit block. It has three first-read fibers, 3P leaves and N binary nodes. Distinct binary parents A and B share Q, occupying three digits together. Their common digit contains disjoint histories H and K with the same literal request to T. The H1 and K1 children share a digit at T and request the same resolving wait to Z, where their child digits differ. H,K,H1,K1 and the two shared rows are distinct. The repeated edge is precisely w->v, J=s=Xi=1, r=N+1+e, Z is outside the binary targets, and H=A or B and T=Q remain permitted. Incompatible prescribed identities give an empty domain.

The inventory consists of N-1 binary targets, Z and e extra targets. Q has no spare digit; each other binary target and Z has one; each extra has three. Ordinary demands are exactly the unary histories except K,H1,K1, with their literal lengths and absolute child digits retained. Assignments inject these demands into same-digit spares and hit every extra. Binary baselines are maxima of parent literal requests, Z uses the common resolving request, and extras start at one. L_alpha(q) is the maximum of that baseline and all assigned requests to q.

Each compatible feasible assignment produces one total stationary table preserving every original unit action, phase, read index, label, deadline and graph statistic. Every constructed control state is reachable. Its full nominal cardinal is 3P+2N+1+ell+2e+sum_q(L_alpha(q)-1). The minimum is over implementations of this fixed forest and identifications. At e>0 an extra target retains one joint maximum across all its spare digits. At e=0, feasibility is exactly A(c,1)<=B(c,1), subject to the prescribed compatibility, and one descending alpha attains every threshold. The finite sum starts at k=2 and vanishes above the actual maximum literal value.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedForestUnitCapacity.actualL_transport`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedForestUnitCapacity.assignment`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedForestUnitCapacity.attained_e0_threshold_minimum`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedForestUnitCapacity.attained_fixed_minimum`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedForestUnitCapacity.empty_domain_no_minimum`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedForestUnitCapacity.nominal_lower_bound`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedForestUnitCapacity.original_context8319`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedForestUnitCapacity.original_domain_iff`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedForestUnitCapacity.request_target`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedForestUnitCapacity.targetEquiv`
- Dependency: [D5/S3/ObserverMemory/Algorithms/FixedForestThresholdAssignment](FixedForestThresholdAssignment.md)
