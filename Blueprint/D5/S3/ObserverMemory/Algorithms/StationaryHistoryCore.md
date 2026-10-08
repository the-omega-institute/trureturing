# StationaryHistoryCore

## Abstract

Unrestricted actual slot incidence selects structural core targets and literal-tail baselines.

B is the image of all binary histories under nextTarget. Its multiplicity at q counts all binary parents targeting q; s sums multiplicity minus one over B. Thus |B|=N-s. Select exactly s targets from G minus B. For each selected q choose an actual pure resolving row with target q. Core is B union selectedTargets, extras is Targets minus Core, and e=|Targets|-N. Every history on a pure resolving row is unary. The selected rows are distinct because their target identities are distinct.

**Theorem 1.1 (Exact controller-derived core and extras).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{[\operatorname {DecidableEq}(Q)][\operatorname {NeZero}(3\times P)]\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{{\operatorname {card}(\operatorname {B}(C,hP,I))=3\times{P-1}-\operatorname {s}(C,hP,I)}\land{\operatorname {card}(\operatorname {core}(C,hP,I))=3\times{P-1}}\land{\operatorname {card}(\operatorname {extras}(C,hP,I))=\operatorname {e}(C,hP,I)}\land{\operatorname {card}(\operatorname {readStates}(C,hP,I))=3\times{P-1}+1+\operatorname {e}(C,hP,I)}\land{\forall q:Q,{{q\in \operatorname {selectedTargets}(C,hP,I)}\implies{{\operatorname {selectedRow}(C,hP,I,q)\in \operatorname {resolvingRows}(C,hP,I)}\land{\operatorname {target}(C,hP,I,\operatorname {selectedRow}(C,hP,I,q))=q}}}}\land{\forall n:\operatorname {History}(C,hP,I),{{\operatorname {row}(C,hP,I,n)\in \operatorname {resolvingRows}(C,hP,I)}\implies{\operatorname {card}(\operatorname {children}(C,hP,I,n))=1}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryHistoryCore.structural_core` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

These sets and all their counts are obtained from C/I. A further exact equivalence readStateEquiv identifies the finite readStates image with the original ActualRead type. No supplied forest, N-core, read-count, injection, or J/s/Xi equation is a premise.

**Theorem 1.2 (Distinct selected resolving rows).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{[\operatorname {DecidableEq}(Q)][\operatorname {NeZero}(3\times P)]\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{{\operatorname {s}(C,hP,I)\le \operatorname {J}(C,hP,I)}\land{\operatorname {InjOn}(\operatorname {selectedRow}(C,hP,I),\operatorname {selectedTargets}(C,hP,I))}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryHistoryCore.resolving_selection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The selected row's actual next-target identity recovers q, giving injectivity. Their cardinal s is consequently bounded by the already derived resolving-row count J.

For every internal history n the positive representative is 1+((delay(n)-1) mod P). A binary history has representative strictly below P; an internal unary history can have representative P. BinaryBaseline(q) is the maximum of all binary-parent representatives targeting q, with empty maximum zero. Baseline(q) uses this value on B, the selected resolving row's literal wait on selectedTargets, and one elsewhere. TargetRead identifies an actual nonfirst target with the original NonrootRead type. Tail(q) is actualL of that target, the maximum of actual positive literal arrivals. These definitions have no score function parameter.

**Theorem 1.3 (Literal-tail bounds for all baselines).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{[\operatorname {DecidableEq}(Q)][\operatorname {NeZero}(3\times P)]\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{\forall q:Q,{{q\in \operatorname {targets}(C,hP,I)}\implies{{1\le \operatorname {baseline}(C,hP,I,q)}\land{\operatorname {baseline}(C,hP,I,q)\le \operatorname {tail}(C,hP,I,q)}\land{{q\in \operatorname {extras}(C,hP,I)}\implies{\operatorname {baseline}(C,hP,I,q)=1}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryHistoryCore.baseline_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every selected parent's actual indexed run constructs an Arrival in the original controller. The canonical actualL maximum bounds its literal delay and hence its positive representative. Supremum over all binary parents preserves the bound; selected resolving baselines remain literal waits, and extra baselines remain one.

BackgroundParent(n) holds exactly when n is binary or row(n) is the selected row of a selected resolving target. These alternatives cannot coincide. BackgroundChildren(q) retains each full history n targeting q whose unique forest parent is a background parent. BackgroundDigits(q) is its color image, and k(q)=3-|BackgroundDigits(q)|. Only this digit occupancy takes an image: the history collection retains all different prefix identities, including equal-row histories with equal literal waits.

**Theorem 1.4 (Actual core digit occupancy).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{[\operatorname {DecidableEq}(Q)][\operatorname {NeZero}(3\times P)]\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{{\forall q:Q,{{q\in \operatorname {core}(C,hP,I)}\implies{{2\le \operatorname {card}(\operatorname {backgroundDigits}(C,hP,I,q))}\land{\operatorname {k}(C,hP,I,q)\le 1}}}}\land{\forall q:Q,{{q\in \operatorname {extras}(C,hP,I)}\implies{\operatorname {backgroundChildren}(C,hP,I,q)=\operatorname {empty}()}}}\land{\forall q:Q,{\forall n:\operatorname {History}(C,hP,I),{\forall m:\operatorname {History}(C,hP,I),{{{n\in \operatorname {backgroundChildren}(C,hP,I,q)}\land{m\in \operatorname {backgroundChildren}(C,hP,I,q)}\land{\neg {n=m}}}\implies{\operatorname {Disjoint}(\operatorname {indexedSupport}(C,hP,I,n),\operatorname {indexedSupport}(C,hP,I,m))}}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryHistoryCore.background_structure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A binary parent supplies two distinct child digits. A selected pure resolving row supplies its two distinct actual outgoing target digits through all of its unary histories. Thus every core has k in {0,1}; extra targets have no background. Different histories have disjoint original (x,i) event sets even if an ancestor and descendant contain the same original label.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryHistoryCore.background_structure`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryHistoryCore.baseline_bounds`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryHistoryCore.resolving_selection`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryHistoryCore.structural_core`
- Dependency: [D5/S3/ObserverMemory/Algorithms/StationaryHistoryIncidence](StationaryHistoryIncidence.md)
