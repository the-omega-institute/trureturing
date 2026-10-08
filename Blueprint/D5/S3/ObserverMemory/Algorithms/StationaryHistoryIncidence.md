# StationaryHistoryIncidence

## Abstract

Actual full histories derive unrestricted slot edges, incidence statistics, and degree balances.

Fix P greater than one, arbitrary finite ell and h, a stationary controller C on Q, and Initialized C hP ell h. The original physical period is 3P and its digit alphabet has three elements. Every original label begins at the same nominal initial state. Waits remain positive literal integers, including modular wraps; singleton continuation and every control cycle terminating on all initialized inputs remain in scope. Only actual read states enter the slot graph. The full nominal carrier Q, including unused states, remains the carrier of C and is not replaced by that graph.

Node is the finite type History C hP I of complete indexed read prefixes from StationaryReadHistory. A node n has slot row(n)=(readControl(n),color(n)). Rows is the image of all nodes; nonroots retains every node with a parent. Edges is the image of nonroot nodes under n maps to (row(parent(n)),row(n)). Equal slot pairs define one graph edge, while their fibers retain every distinct full history. Incoming and outgoing are the edge fibers at their second and first endpoints. J sums incoming degree minus one over actual nonroot rows; Xi sums edge-fiber cardinality minus one over actual edges. These are derived quantities.

**Theorem 1.1 (Actual forest-edge multiplicity).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{[\operatorname {DecidableEq}(Q)][\operatorname {NeZero}(3\times P)]\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{\sum_{z\in \operatorname {nonrootRows}(C,hP,I)}{\operatorname {card}(\{n\in \operatorname {nonroots}(C,hP,I)\mid{\operatorname {row}(C,hP,I,n)=z}\})-1}=\operatorname {J}(C,hP,I)+\operatorname {Xi}(C,hP,I)}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryHistoryIncidence.actual_edge_incidence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The raw_history_surplus supplier is applied to the actual physicalForest and actual row map. The counted fiber consists of different full prefixes, not source visits or repeated drawings.

**Theorem 1.2 (At most two distinct outgoing slots).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{[\operatorname {DecidableEq}(Q)][\operatorname {NeZero}(3\times P)]\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{\forall n:\operatorname {History}(C,hP,I),{\operatorname {card}(\operatorname {outgoing}(C,hP,I,\operatorname {row}(C,hP,I,n)))\le 2}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryHistoryIncidence.outgoing_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One actual source row fixes its literal delay and next read target. Exact reuse of the digit-translation supplier confines all of its children, across every full history and read level, to two absolute target digits. This bound includes pure resolving rows containing several unary histories.

Binaries is the set of histories with exactly two children. ProductionRows is their row image. Binary-row uniqueness makes this image injective. TwoRows consists of actual rows having two distinct outgoing graph edges; resolvingRows is TwoRows minus ProductionRows. Terminal-row uniqueness gives 3P different terminal rows. The three roots have no incoming edge and share the first read control. Writing N=3(P-1), the graph degree balance gives the following exact counts.

**Theorem 1.3 (Production and pure resolving counts).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{[\operatorname {DecidableEq}(Q)][\operatorname {NeZero}(3\times P)]\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{{\operatorname {card}(\operatorname {twoRows}(C,hP,I))=3\times{P-1}+\operatorname {J}(C,hP,I)}\land{\operatorname {card}(\operatorname {productionRows}(C,hP,I))=3\times{P-1}}\land{\operatorname {card}(\operatorname {resolvingRows}(C,hP,I))=\operatorname {J}(C,hP,I)}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryHistoryIncidence.two_outgoing_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The incoming balance is |edges|+3=|rows|+J. The outgoing balance is |edges|+3P=|rows|+|TwoRows|. Their difference forces |TwoRows|=N+J; subtracting N production rows leaves exactly J pure resolving rows.

An actual row representative is a selected full history on that row. Target(z) and literal(z) are its next target and literal wait, independent of the representative on a continuing row. Targets is the set of actual nonfirst read controls. G is the target image of TwoRows. For each q, twoAt(q) is the two-row fiber at q, targetSlots(q) is its nonroot digit-slot fiber, and targetJ(q) sums the incoming surpluses of those slots.

**Theorem 1.4 (Distinct two-row incidence at a target).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{[\operatorname {DecidableEq}(Q)][\operatorname {NeZero}(3\times P)]\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{\forall q:Q,{{2\times\operatorname {card}(\operatorname {twoAt}(C,hP,I,q))\le 3+\operatorname {targetJ}(C,hP,I,q)}\land{\operatorname {card}(\operatorname {twoAt}(C,hP,I,q))-1\le \operatorname {targetJ}(C,hP,I,q)}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryHistoryIncidence.target_incidence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

t different two-outgoing rows give 2t different incoming edges at their common target. At most three digit slots subtract at most three first incidences. Nonnegative surplus gives t-1<=targetJ(q), including t=0 and t=1. Summing these bounds and the actual J balance proves |G|>=N without degree or collision restrictions.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryHistoryIncidence.actual_edge_incidence`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryHistoryIncidence.outgoing_degree`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryHistoryIncidence.target_incidence`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryHistoryIncidence.two_outgoing_count`
- Dependency: [D5/S3/ObserverMemory/Algorithms/FixedForestSlotGraph](FixedForestSlotGraph.md)
- Dependency: [D5/S3/ObserverMemory/Algorithms/StationaryReadHistory](StationaryReadHistory.md)
