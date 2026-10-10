# StationaryReadHistory

## Abstract

Actual interval geometry constructs the physical forest and separates binary source rows.

**Theorem 1.1 (Convex physical fibers).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{[\operatorname {NeZero}(3\times P)]\forall n:\operatorname {History}(C,hP,I),{\forall x:\operatorname {ZMod}(3\times P),{\forall y:\operatorname {ZMod}(3\times P),{\forall z:\operatorname {ZMod}(3\times P),{{{{x\in \operatorname {support}(C,hP,I,n)}\land{z\in \operatorname {support}(C,hP,I,n)}}\land{{\operatorname {digit}(hP,y+\operatorname {historyShift}(C,hP,I,n))=\operatorname {color}(C,hP,I,n)}\land{{\operatorname {val}(x+\operatorname {historyShift}(C,hP,I,n))\le \operatorname {val}(y+\operatorname {historyShift}(C,hP,I,n))}\land{\operatorname {val}(y+\operatorname {historyShift}(C,hP,I,n))\le \operatorname {val}(z+\operatorname {historyShift}(C,hP,I,n))}}}}\implies{y\in \operatorname {support}(C,hP,I,n)}}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryReadHistory.history_phase_convex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Within the current absolute digit block, every phase between two supporting phases supports the same complete history. Induction follows the actual parent; inverse translation preserves order between endpoints in one previous digit block because neither block can span a modular wrap.

**Theorem 1.2 (Nonempty actual physical intervals).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{[\operatorname {NeZero}(3\times P)]\forall n:\operatorname {History}(C,hP,I),{\exists ab:\mathbb {N}\times\mathbb {N},{\operatorname {fst}(ab)<\operatorname {snd}(ab)}\land{{\operatorname {snd}(ab)\le P}\land{\forall x:\operatorname {ZMod}(3\times P),{x\in \operatorname {support}(C,hP,I,n)\iff{\operatorname {val}(\operatorname {color}(C,hP,I,n))\times P+\operatorname {fst}(ab)\le \operatorname {val}(x+\operatorname {historyShift}(C,hP,I,n))}\land{\operatorname {val}(x+\operatorname {historyShift}(C,hP,I,n))<\operatorname {val}(\operatorname {color}(C,hP,I,n))\times P+\operatorname {snd}(ab)}}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryReadHistory.history_interval_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The minimum and maximum actual phase values yield lower and upper endpoints with lower<upper<=P. Convexity proves the exact half-open interval; intervalEndpoints chooses that witness, and lower/upper are its projections.

**Theorem 1.3 (PhysicalForest derived from the original controller).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{[\operatorname {NeZero}(3\times P)]\operatorname {PhysicalForest}(P,h,ell,\operatorname {History}(C,hP,I),hP)}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryReadHistory.physicalForest` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

physicalForest constructs every field from the actual full words and indexed reads: parent, roots, color, literal shift/delay, level, original leaf labels, supports, interval endpoints, read counts and events; exact root/first/event/support laws; interval bounds; child shift/level/answer injectivity; indexed successor and immediate last-read stopping; original leaf outputs; positive internal delays; branching<=2 and binary_count=3(P-1). Its roots and leaves remain exactly three and 3P. forestEvent totalizes the natural index only outside the actual read range. No forest, count or injection is supplied as a hypothesis, and no J,s,Xi restriction is used.

**Theorem 1.4 (Binary intervals cross one modular cut).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{[\operatorname {NeZero}(3\times P)]\forall p:\operatorname {History}(C,hP,I),{{\operatorname {card}(\operatorname {children}(C,hP,I,p))=2}\implies{{\operatorname {lower}(C,hP,I,p)<\operatorname {modularCut}(C,hP,I,p)}\land{\operatorname {modularCut}(C,hP,I,p)<\operatorname {upper}(C,hP,I,p)}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryReadHistory.binary_crosses_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

modularCut(p)=P-(delay(p) mod P). Distinct child digits require supporting parent phases on both sides of this cut. Each binary interval contains the cut phase, while a unary interval can remain on either side.

**Theorem 1.5 (One binary history per actual row).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{[\operatorname {NeZero}(3\times P)]\forall n:\operatorname {History}(C,hP,I),{\forall m:\operatorname {History}(C,hP,I),{{{{\operatorname {card}(\operatorname {children}(C,hP,I,n))=2}\land{\operatorname {card}(\operatorname {children}(C,hP,I,m))=2}}\land{{\operatorname {readControl}(C,hP,I,n)=\operatorname {readControl}(C,hP,I,m)}\land{\operatorname {color}(C,hP,I,n)=\operatorname {color}(C,hP,I,m)}}}\implies{n=m}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryReadHistory.binary_row_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Shared continuing rows have equal literal delays and one modular cut. Two binary intervals on that row would contain the same cut phase. Same-control phase separation rules this out. These results supply the actual forest and row geometry; core selection, weighted overlap and the final original83.21 inequality require additional results.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryReadHistory.binary_crosses_cut`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryReadHistory.binary_row_unique`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryReadHistory.history_interval_exists`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryReadHistory.history_phase_convex`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryReadHistory.physicalForest`
- Dependency: [D5/S3/ObserverMemory/Algorithms/StationaryHistoryRows](StationaryHistoryRows.md)
