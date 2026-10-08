# StationaryHistorySlotGraph

## Abstract

Original single-collision slot conditions extract actual marked parent and child histories.

**Theorem 1.1 (The actual unique single collision).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{[\operatorname {DecidableEq}(Q)][\operatorname {NeZero}(3\times P)]\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{{{\operatorname {J}(C,hP,I)=1}\land{\operatorname {s}(C,hP,I)=1}}\implies{\exists q:Q,{\exists w:\operatorname {Prod}(Q,\operatorname {Fin}(3)),{\exists v:\operatorname {Prod}(Q,\operatorname {Fin}(3)),{{\operatorname {binaryMultiplicity}(C,hP,I,q)=2}\land{\operatorname {fst}(w)=q}\land{\forall t:Q,{{t\neq q}\implies{\operatorname {binaryMultiplicity}(C,hP,I,t)\le 1}}}\land{2\le \operatorname {card}(\{a\in \operatorname {incoming}(C,hP,I,w)\mid{\operatorname {fst}(a)\in \operatorname {productionRows}(C,hP,I)}\})}\land{\forall z:\operatorname {Prod}(Q,\operatorname {Fin}(3)),{{2\le \operatorname {card}(\operatorname {incoming}(C,hP,I,z))}\implies{z=w}}}\land{\operatorname {resolvingRows}(C,hP,I)=\{v\}}}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryHistorySlotGraph.single_collision_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When J=s=1, exactly one actual target has two binary parents. Their two distinct source rows each supply two child digits in a three-digit target, so they intersect. The whole incoming surplus is spent at that shared slot w. Every other slot has at most one incoming edge. The actual resolving-row count is one, selecting v.

**Theorem 1.2 (Actual histories from unmarked slot conditions).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{[\operatorname {DecidableEq}(Q)][\operatorname {NeZero}(3\times P)]\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{{{\operatorname {J}(C,hP,I)=1}\land{\operatorname {s}(C,hP,I)=1}\land{\operatorname {Xi}(C,hP,I)=1}\land{\forall w:\operatorname {Prod}(Q,\operatorname {Fin}(3)),{\forall v:\operatorname {Prod}(Q,\operatorname {Fin}(3)),{{2\le \operatorname {card}(\{a\in \operatorname {incoming}(C,hP,I,w)\mid{\operatorname {fst}(a)\in \operatorname {productionRows}(C,hP,I)}\})}\implies{{v\in \operatorname {resolvingRows}(C,hP,I)}\implies{{w\in \operatorname {productionRows}(C,hP,I)}\land{w\neq v}\land{\forall n:\operatorname {History}(C,hP,I),{{\operatorname {row}(C,hP,I,n)=w}\implies{{\operatorname {card}(\operatorname {children}(C,hP,I,n))\neq 2}\implies{\operatorname {card}(\operatorname {support}(C,hP,I,n))=1}}}}\land{\forall n:\operatorname {History}(C,hP,I),{{\operatorname {row}(C,hP,I,n)=v}\implies{\operatorname {card}(\operatorname {support}(C,hP,I,n))=1}}}}}}}}}\implies{\exists R:\operatorname {Prescribed}(\operatorname {physicalForest}(C,hP,I)),{{\operatorname {row}(C,hP,I,\operatorname {H}(R))=\operatorname {row}(C,hP,I,\operatorname {K}(R))}\land{\operatorname {row}(C,hP,I,\operatorname {Ha}(R))=\operatorname {row}(C,hP,I,\operatorname {Ka}(R))}\land{\operatorname {row}(C,hP,I,\operatorname {H}(R))\neq \operatorname {row}(C,hP,I,\operatorname {Ha}(R))}\land{\operatorname {card}(\operatorname {support}(C,hP,I,\operatorname {K}(R)))=1}\land{\operatorname {card}(\operatorname {support}(C,hP,I,\operatorname {Ha}(R)))=1}\land{\operatorname {card}(\operatorname {support}(C,hP,I,\operatorname {Ka}(R)))=1}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryHistorySlotGraph.prescribed_of_single_collision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Prescribed contains actual binary parents A,B, a binary history H and unary history K on w, and their unary children H1,K1 on v. In the displayed formula Ha and Ka denote H1 and K1. UnmarkedShape is the following fully quantified source condition: the unique collision slot is producing, differs from the pure resolving slot, every nonbinary history on the collision slot is a singleton, and every history on the resolving slot is a singleton. J=Xi=1 gives total history surplus two, so these two doubled rows exhaust all repeated histories. The selected binary source rows and actual outgoing edges determine the marked parent and child relationships. Their literal waits agree on each common source row, their physical supports are disjoint, and resolving children have different actual digits. The producing history may itself be one of A,B; neither acyclicity nor a different producing target is required.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryHistorySlotGraph.prescribed_of_single_collision`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryHistorySlotGraph.single_collision_rows`
- Dependency: [D5/S3/ObserverMemory/Algorithms/StationaryHistoryCoreData](StationaryHistoryCoreData.md)
