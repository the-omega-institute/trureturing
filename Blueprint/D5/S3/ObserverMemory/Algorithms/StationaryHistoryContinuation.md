# StationaryHistoryContinuation

## Abstract

Indexed history separation, first-read fibers and positive literal continuation gaps.

**Theorem 1.1 (Original first-read fibers).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{[\operatorname {NeZero}(3\times P)]\forall c:\operatorname {Fin}(3),{\forall x:\operatorname {ZMod}(3\times P),{x\in \operatorname {support}(C,hP,I,\operatorname {root}(C,hP,I,c))\iff\operatorname {digit}(hP,x+ell)=c}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryHistoryContinuation.root_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The root support is exactly the original digit block after the common literal translation ell. No source-dependent preparation is introduced.

**Theorem 1.2 (Phase separation at one control).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{[\operatorname {NeZero}(3\times P)]\forall n:\operatorname {History}(C,hP,I),{\forall m:\operatorname {History}(C,hP,I),{{{n\neq m}\land{\operatorname {readControl}(C,hP,I,n)=\operatorname {readControl}(C,hP,I,m)}}\implies{\operatorname {Disjoint}(\operatorname {phaseSupport}(C,hP,I,n),\operatorname {phaseSupport}(C,hP,I,m))}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryHistoryContinuation.same_control_phase_disjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A common physical phase and read control would give equal initialized configurations. Finite correctness then forces the same original label and time, and hence the same indexed read and full history. This also applies to histories at different levels and to terminating control cycles.

**Theorem 1.3 (Literal read gaps are physical shift increases).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{[\operatorname {NeZero}(3\times P)]\forall x:\operatorname {ZMod}(3\times P),{\forall i:\mathbb {N},{{i+1<\operatorname {reads}(C,hP,I,x)}\implies{{0<\operatorname {readTime}(C,hP,I,x,i+1)-{\operatorname {readTime}(C,hP,I,x,i)+1}}\land{\operatorname {historyShift}(C,hP,I,\operatorname {event}(C,hP,I,(x,i+1)))=\operatorname {historyShift}(C,hP,I,\operatorname {event}(C,hP,I,(x,i)))+\operatorname {readTime}(C,hP,I,x,i+1)-{\operatorname {readTime}(C,hP,I,x,i)+1}}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryHistoryContinuation.literal_shift_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The action immediately after a nonfinal read is a wait. Consecutive read times therefore have a positive intervening literal gap. Time equals shift plus read level, so the shift increases by that entire gap.

**Theorem 1.4 (Singleton continuation stays unary).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{[\operatorname {NeZero}(3\times P)]\forall n:\operatorname {History}(C,hP,I),{{{\operatorname {card}(\operatorname {support}(C,hP,I,n))=1}\land{\neg \operatorname {IsLeaf}(C,hP,I,n)}}\implies{\operatorname {card}(\operatorname {children}(C,hP,I,n))=1}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryHistoryContinuation.singleton_continuation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every child's support is nonempty and lies in its parent's support. When that support is one label, child level and input-index uniqueness force one child. The continuation is kept rather than erased.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryHistoryContinuation.literal_shift_gap`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryHistoryContinuation.root_support`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryHistoryContinuation.same_control_phase_disjoint`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryHistoryContinuation.singleton_continuation`
- Dependency: [D5/S3/ObserverMemory/Algorithms/StationaryHistoryPrefix](StationaryHistoryPrefix.md)
