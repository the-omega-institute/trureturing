# Simultaneous thresholds of the original literal tails

## Abstract

A single descending same-digit assignment attains every threshold of the fixed forest at e=0.

Take exactly the ordinary unary demands and all original spare slots at e=0. For digit c, ColorDemand and ColorSlot are their full digit fibers. Write n and m for their cardinalities. E0 is sum_q(baseline(q)-1). A(c,k) counts demands with literal length at least k, and B(c,k) counts slots whose target baseline is at least k. Descending order uses permutations of these entire finite carriers, including tied lengths. When n<=m, demand rank i is assigned to slot rank i; the remaining m-n slots are retained and left unused.

**Theorem 1.1 (The exact ranks that cross a threshold).**

$$\forall D:Type,{\forall S:Type,{[\operatorname {Fintype}(D)][\operatorname {Fintype}(S)]\forall a:D\to\mathbb {N},{\forall b:S\to\mathbb {N},{\forall bound:\operatorname {card}(D)\le\operatorname {card}(S),{\forall k:\mathbb {N},{\forall i:\operatorname {Fin}(\operatorname {card}(D)),{{k\le\operatorname {a}(\operatorname {order}(a,i))}\land{\operatorname {b}(\operatorname {map}(a,b,bound,\operatorname {order}(a,i)))<k}\iff{\operatorname {count}(b,k)<i+1}\land{i+1\le\operatorname {count}(a,k)}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/FixedForestThresholdAssignment.increment_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use one-based rank i+1. A crossing occurs precisely at B(k)<i+1<=A(k). The descending rank/count equivalence holds for every threshold, so no threshold-dependent choice of assignment is needed.

**Definition 1.2 (One original same-digit injection).**

$$\forall P:\mathbb {N},{\forall h:\mathbb {N},{\forall ell:\mathbb {N},{\forall Node:Type,{[\operatorname {Fintype}(Node)][\operatorname {DecidableEq}(Node)]\forall hP:1<P,{\forall F:\operatorname {PhysicalForest}(P,h,ell,Node,hP),{\forall R:\operatorname {Prescribed}(F),{{\forall c:\operatorname {Fin}(3),{\operatorname {card}(\operatorname {ColorDemand}(F,R,c))\le\operatorname {card}(\operatorname {ColorSlot}(F,R,c))}}\implies{\operatorname {Assignment}(F,R,0)}}}}}}}}$$

*Formalization.* `D5/S3/ObserverMemory/Algorithms/FixedForestThresholdAssignment.sortedAssignment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sort each demand fiber by literal length and each full spare-slot fiber by target baseline. The first n ranks define an injection in that digit. The disjoint digit fibers combine these injections into one original Assignment. There are no extra targets to hit at e=0. Empty demand fibers and empty slot fibers require no positive-cardinality assumption.

**Theorem 1.3 (All thresholds attained by the same assignment).**

$$\forall P:\mathbb {N},{\forall h:\mathbb {N},{\forall ell:\mathbb {N},{\forall Node:Type,{[\operatorname {Fintype}(Node)][\operatorname {DecidableEq}(Node)]\forall hP:1<P,{\forall F:\operatorname {PhysicalForest}(P,h,ell,Node,hP),{\forall R:\operatorname {Prescribed}(F),{{\forall c:\operatorname {Fin}(3),{\operatorname {card}(\operatorname {ColorDemand}(F,R,c))\le\operatorname {card}(\operatorname {ColorSlot}(F,R,c))}}\implies{\forall c:\operatorname {Fin}(3),{\forall k:\mathbb {N},{\operatorname {card}(\{ d:\operatorname {ColorDemand}(F,R,c)\mid {k\le\operatorname {delay}(F,\operatorname {val}(\operatorname {val}(d)))}\land{\operatorname {baseline}(F,R,\operatorname {target}(\operatorname {slot}(\operatorname {sortedAssignment}(F,R),\operatorname {val}(d))))<k}\})=[\operatorname {A}(F,R,c,k)-\operatorname {B}(F,R,c,k)]_{+}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/FixedForestThresholdAssignment.sorted_thresholds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the same stored sortedAssignment, the number of demands crossing threshold k in digit c is exactly A(c,k)-B(c,k), with truncated natural subtraction. Surplus slots contribute to B even though they are unused. The identity includes k=1 and all ties.

**Theorem 1.4 (Every injection pays the deficit).**

$$\forall P:\mathbb {N},{\forall h:\mathbb {N},{\forall ell:\mathbb {N},{\forall Node:Type,{[\operatorname {Fintype}(Node)][\operatorname {DecidableEq}(Node)]\forall hP:1<P,{\forall F:\operatorname {PhysicalForest}(P,h,ell,Node,hP),{\forall R:\operatorname {Prescribed}(F),{\forall alpha:\operatorname {Assignment}(F,R,0),{\forall c:\operatorname {Fin}(3),{\forall k:\mathbb {N},{[\operatorname {A}(F,R,c,k)-\operatorname {B}(F,R,c,k)]_{+}\le\operatorname {card}(\{ d:\operatorname {ColorDemand}(F,R,c)\mid {k\le\operatorname {delay}(F,\operatorname {val}(\operatorname {val}(d)))}\land{\operatorname {baseline}(F,R,\operatorname {target}(\operatorname {slot}(alpha,\operatorname {val}(d))))<k}\})}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/FixedForestThresholdAssignment.arbitrary_threshold_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Partition high demands into those placed at high baselines and those crossing the threshold. Injectivity bounds the first class by all high-baseline slots. Consequently every original assignment pays at least the same threshold deficit.

**Theorem 1.5 (At most one spare slot per target).**

$$\forall P:\mathbb {N},{\forall h:\mathbb {N},{\forall ell:\mathbb {N},{\forall Node:Type,{[\operatorname {Fintype}(Node)][\operatorname {DecidableEq}(Node)]\forall hP:1<P,{\forall F:\operatorname {PhysicalForest}(P,h,ell,Node,hP),{\forall R:\operatorname {Prescribed}(F),{\forall s:\operatorname {SpareSlot}(F,R,0),{\forall t:\operatorname {SpareSlot}(F,R,0),{{\operatorname {target}(s)=\operatorname {target}(t)}\implies{s=t}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/FixedForestThresholdAssignment.spare_target_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Q has no spare digit. Every other binary target and Z have exactly one. Since e=0 has no extra target, two spare slots with the same target are equal. This is the reason the color contributions can be added without charging a target twice.

**Theorem 1.6 (Original assignment feasibility).**

$$\forall P:\mathbb {N},{\forall h:\mathbb {N},{\forall ell:\mathbb {N},{\forall Node:Type,{[\operatorname {Fintype}(Node)][\operatorname {DecidableEq}(Node)]\forall hP:1<P,{\forall F:\operatorname {PhysicalForest}(P,h,ell,Node,hP),{\forall R:\operatorname {Prescribed}(F),{\operatorname {Nonempty}(\operatorname {Assignment}(F,R,0))\iff\forall c:\operatorname {Fin}(3),{\operatorname {A}(F,R,c,1)\le\operatorname {B}(F,R,c,1)}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/FixedForestThresholdAssignment.assignment_e0_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All ordinary literal lengths and all target baselines are positive, so A(c,1)=n(c) and B(c,1)=m(c). An injection gives n(c)<=m(c). Conversely these inequalities construct the descending original assignment.

**Theorem 1.7 (Thresholds above the actual maximum vanish).**

$$\forall P:\mathbb {N},{\forall h:\mathbb {N},{\forall ell:\mathbb {N},{\forall Node:Type,{[\operatorname {Fintype}(Node)][\operatorname {DecidableEq}(Node)]\forall hP:1<P,{\forall F:\operatorname {PhysicalForest}(P,h,ell,Node,hP),{\forall R:\operatorname {Prescribed}(F),{\forall k:\mathbb {N},{{\operatorname {thresholdMax}(F,R)<k}\implies{\forall c:\operatorname {Fin}(3),{{\operatorname {A}(F,R,c,k)=0}\land{\operatorname {B}(F,R,c,k)=0}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/FixedForestThresholdAssignment.thresholds_vanish` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

thresholdMax is the maximum of the actual ordinary literal lengths and all target baselines. A maximum over an empty demand class is zero. Above this finite maximum both counts are zero. There is no unsupported infinite-sum truncation.

**Theorem 1.8 (The same joint tails as threshold crossings).**

$$\forall P:\mathbb {N},{\forall h:\mathbb {N},{\forall ell:\mathbb {N},{\forall Node:Type,{[\operatorname {Fintype}(Node)][\operatorname {DecidableEq}(Node)]\forall hP:1<P,{\forall F:\operatorname {PhysicalForest}(P,h,ell,Node,hP),{\forall R:\operatorname {Prescribed}(F),{\forall alpha:\operatorname {Assignment}(F,R,0),{\sum_{q:\operatorname {Target}(F,R,0)}{\operatorname {L}(F,R,alpha,q)-1}=\operatorname {Ezero}(F,R)+\sum_{c:\operatorname {Fin}(3)}{\sum_{k\in \operatorname {Icc}(2,\operatorname {thresholdMax}(F,R))}{\operatorname {card}(\{ d:\operatorname {ColorDemand}(F,R,c)\mid {k\le\operatorname {delay}(F,\operatorname {val}(\operatorname {val}(d)))}\land{\operatorname {baseline}(F,R,\operatorname {target}(\operatorname {slot}(alpha,\operatorname {val}(d))))<k}\})}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/FixedForestThresholdAssignment.tail_cost_layers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With at most one ordinary request per target, its increase is the positive part of literal length minus baseline. Count the integer levels crossed by that increase. Positive baselines remove level 1, so the finite sum starts at k=2. Partition the original demands by their absolute digit; the result is exactly sum_q(L_alpha(q)-1).

**Theorem 1.9 (The common assignment minimizes the joint tail cost).**

$$\forall P:\mathbb {N},{\forall h:\mathbb {N},{\forall ell:\mathbb {N},{\forall Node:Type,{[\operatorname {Fintype}(Node)][\operatorname {DecidableEq}(Node)]\forall hP:1<P,{\forall F:\operatorname {PhysicalForest}(P,h,ell,Node,hP),{\forall R:\operatorname {Prescribed}(F),{{\forall c:\operatorname {Fin}(3),{\operatorname {card}(\operatorname {ColorDemand}(F,R,c))\le\operatorname {card}(\operatorname {ColorSlot}(F,R,c))}}\implies{{\sum_{q:\operatorname {Target}(F,R,0)}{\operatorname {L}(F,R,\operatorname {sortedAssignment}(F,R),q)-1}=\operatorname {Ezero}(F,R)+\sum_{c:\operatorname {Fin}(3)}{\sum_{k\in \operatorname {Icc}(2,\operatorname {thresholdMax}(F,R))}{[\operatorname {A}(F,R,c,k)-\operatorname {B}(F,R,c,k)]_{+}}}}\land{\forall beta:\operatorname {Assignment}(F,R,0),{\operatorname {Ezero}(F,R)+\sum_{c:\operatorname {Fin}(3)}{\sum_{k\in \operatorname {Icc}(2,\operatorname {thresholdMax}(F,R))}{[\operatorname {A}(F,R,c,k)-\operatorname {B}(F,R,c,k)]_{+}}}\le\sum_{q:\operatorname {Target}(F,R,0)}{\operatorname {L}(F,R,beta,q)-1}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/FixedForestThresholdAssignment.sorted_cost` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The common sorted assignment attains every threshold lower bound and hence their entire finite sum. The resulting cost is E0+sum_c sum_{2<=k<=thresholdMax}(A(c,k)-B(c,k))_+. This identity concerns the same original target maxima L and is used by the attained minimum of actual stationary implementations. At e>0, a target can have three spare digits and must retain its joint maximum; this color sum does not apply.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedForestThresholdAssignment.arbitrary_threshold_lower`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedForestThresholdAssignment.assignment_e0_iff`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedForestThresholdAssignment.increment_rank`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedForestThresholdAssignment.sortedAssignment`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedForestThresholdAssignment.sorted_cost`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedForestThresholdAssignment.sorted_thresholds`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedForestThresholdAssignment.spare_target_injective`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedForestThresholdAssignment.tail_cost_layers`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedForestThresholdAssignment.thresholds_vanish`
- Dependency: [D5/S3/ObserverMemory/Algorithms/FixedForestOriginalImplementation](FixedForestOriginalImplementation.md)
