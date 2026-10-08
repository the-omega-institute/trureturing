# Odd target rows and exact slot accounting

## Abstract

Directed slot incidence over an odd alphabet forces a deficit at every nonroot target.

Let Q be a finite set of reading controls, p the alphabet size, and G a directed graph on Q times Fin p. Its used slots contain every root digit. Each nonempty successor set has one target control and at most two slots. Successors have used sources and targets, no edge enters the root, and every used nonroot slot has a predecessor. Cycles and multiple predecessors are allowed.

At target q, missing counts unused digits, excess sums incoming cardinalities minus one with natural subtraction, and singles counts one-successor source slots whose unique target is q. These quantities refer to this one graph. The number terminalCount counts used slots with no successor.

**Theorem 1.1 (Incidence identity, binary lower bound, and odd improvement).**

$$\forall p:\mathbb {N},{\forall Q:Type,{[\operatorname {Fintype}(Q)][\operatorname {DecidableEq}(Q)]{\forall G:\operatorname {SlotGraph}(p,Q),{{{2}\le{p}}\implies{\forall P:\mathbb {N},{{{1}\le{P}}\implies{{{\operatorname {terminalCount}(G)}={{p}\times {P}}}\implies{{{{p}\times {\operatorname {card}(Q)}}={{{2}\times {{p}\times {P}}}-{p}+\sum_{q\in Q}\operatorname {excess}(G,q)+\sum_{q\in Q}\operatorname {singles}(G,q)+\sum_{q\in Q}\operatorname {missing}(G,q)}}\land{{{{2}\times {P}}-{1}}\le{\operatorname {card}(Q)}}\land{{\operatorname {Odd}(p)}\implies{{\forall q:Q,{{{q}\neq {\operatorname {root}(G)}}\implies{{1}\le{\operatorname {missing}(G,q)+\operatorname {excess}(G,q)+\operatorname {singles}(G,q)}}}}\land{{{\operatorname {card}(Q)}-{1}}\le{\sum_{q\in Q}\operatorname {missing}(G,q)+\sum_{q\in Q}\operatorname {excess}(G,q)+\sum_{q\in Q}\operatorname {singles}(G,q)}}\land{{{{2}\times {p}}\times {{P}-{1}}}\le{{{p}-{1}}\times {{\operatorname {card}(Q)}-{1}}}}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/OddSlotTargetDeficit.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Double counting the actual edges gives the exact additive identity. When p is odd, a target row of zero deficit would be covered exactly once by pairwise disjoint two-slot successor sets. Its cardinality would be even. Thus each nonroot target contributes at least one. Summing uses unique target ownership, and the final product inequality is equivalent to card Q at least 1 plus 2p(P-1)/(p-1). This statement takes the directed incidence and terminal count as hypotheses; it does not construct them from a stationary controller.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/OddSlotTargetDeficit.result`
