# Stationary unit control and literal memory

## Abstract

Stationary unit instructions preserve physical phases and force disjoint nominal memory for initialized runs.

A controller consists of one common initial state and a total table on Q. Its instructions are wait(next), read(row), and halt(original label). The table receives no phase, input label, time, read index, or history. Configurations pair a physical element of ZMod(3P) with a control state. A wait adds exactly one to the phase. A read preserves the phase and uses its actual digit floor(val/P) in Fin 3. Halt has no successor.

Initialized supplies a finite correct run for every original label x, starting at phase x and the same initial control. WordShape requires ell initial waits, a first read, a positive wait between consecutive reads, at most h reads, and a final read immediately followed by halt. Stop times and read indices are mathematical indices of actual execution. The total trajectory extension is absorbing at halt and adds no action. Literal waits, wraps, ell at least 3P, singleton continuations, unused nominal states, and terminating cycles of read controls remain allowed.

**Theorem 1.1 (Deterministic finite outcomes).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall c:\operatorname {Configuration}(P,Q),{\forall n:\mathbb {N},{\forall m:\mathbb {N},{\forall x:\operatorname {ZMod}(3\times P),{\forall y:\operatorname {ZMod}(3\times P),{{{\operatorname {FiniteRun}(C,hP,c,n,x)}\land{\operatorname {FiniteRun}(C,hP,c,m,y)}}\implies{{n=m}\land{x=y}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryUnitControl.finite_run_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two finite executions from the same physical configuration have the same stop time and stored output. An earlier claimed halt contradicts the other execution's nonhalting prefix; equal stop times have equal labels.

**Theorem 1.2 (Original inputs and event times are separated).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{\forall x:\operatorname {ZMod}(3\times P),{\forall y:\operatorname {ZMod}(3\times P),{\forall t:\mathbb {N},{\forall v:\mathbb {N},{{{t\le \operatorname {length}(I,x)}\land{v\le \operatorname {length}(I,y)}\land{\operatorname {run}(C,hP,(x,\operatorname {initial}(C)),t)=\operatorname {run}(C,hP,(y,\operatorname {initial}(C)),v)}}\implies{{x=y}\land{t=v}}}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryUnitControl.initialized_configuration_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equal configurations on any two initialized paths force equality of their original labels and times. The proof compares the finite suffixes of those same paths. Different input labels cannot share an output; a repeated configuration on one finite path cannot reach its first halt.

**Theorem 1.3 (Every literal wait is an actual unit action).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall d:\mathbb {N},{\forall q:Q,{\forall target:Q,{{\operatorname {Waits}(C,d,q,target)}\implies{\forall s:\operatorname {ZMod}(3\times P),{\operatorname {run}(C,hP,(s,q),d)=(s+d,target)}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryUnitControl.waits_physical_execution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A chain of d waits moves phase s to s+d in ZMod(3P) and reaches its specified control target. The natural d counts actual unit actions; only the physical phase is modular, so full wraps do not shorten a chain.

**Theorem 1.4 (An intersecting wait has one first future read).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{\forall C:\operatorname {Controller}(P,Q),{\forall d:\mathbb {N},{\forall e:\mathbb {N},{\forall q:Q,{\forall target:Q,{\forall other:Q,{{{\operatorname {Waits}(C,d,q,target)}\land{\operatorname {Waits}(C,e,q,other)}\land{\operatorname {IsRead}(C,target)}\land{\operatorname {IsRead}(C,other)}}\implies{{d=e}\land{target=other}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryUnitControl.waits_to_read_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two pure wait paths from one control state to read states have equal literal lengths and the same read target. At each unit position the stationary instruction determines the successor. A read instruction cannot also be a wait, excluding unequal first-read distances.

**Theorem 1.5 (Distinct unit positions in a wait chain).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{\forall C:\operatorname {Controller}(P,Q),{\forall d:\mathbb {N},{\forall q:Q,{\forall target:Q,{{{\operatorname {Waits}(C,d,q,target)}\land{\operatorname {IsRead}(C,target)}}\implies{\operatorname {Injective}(i:\operatorname {Fin}(d)\mapsto\operatorname {iterate}(\operatorname {waitNext}(C),\operatorname {val}(i),q))}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryUnitControl.waits_chain_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The map from Fin d to successive wait controls is injective when the chain ends at a read. Equal internal states would give equal remaining first-read distances and therefore equal unit positions.

**Theorem 1.6 (The prefix covers every phase).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{\forall x:\operatorname {ZMod}(3\times P),{\forall t:\mathbb {N},{{t\le ell}\implies{\operatorname {run}(C,hP,(x,\operatorname {initial}(C)),t)=(x+t,\operatorname {prefixState}(C,hP,t))}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryUnitControl.initialized_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For t at most ell, every original x has phase x+t and the same prefix control. This includes the first read at t=ell, even when the prefix wraps around the physical circle several times.

**Theorem 1.7 (No later return to a prefix or first-read control).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{\forall x:\operatorname {ZMod}(3\times P),{\forall i:\mathbb {N},{\forall t:\mathbb {N},{{{i\le ell}\land{i<t}\land{t\le \operatorname {length}(I,x)}}\implies{\operatorname {control}(\operatorname {run}(C,hP,(x,\operatorname {initial}(C)),t))\neq\operatorname {prefixState}(C,hP,i)}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryUnitControl.prefix_first_read_no_return` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A later occurrence of a prefix control has the same phase as the earlier occurrence for y=phase-i. The exact initialized premise for that original y supplies the comparison path. Configuration uniqueness then contradicts the different times; no original input is discarded.

**Theorem 1.8 (Every nonroot read has a positive incoming literal tail).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{\forall q:\operatorname {NonrootRead}(C,hP,I),{\exists d:\mathbb {N},\operatorname {Nonempty}(\operatorname {Arrival}(C,hP,I,\operatorname {control}(q),d))}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryUnitControl.nonroot_has_arrival` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose an actual occurrence of a nonroot read and the greatest earlier read index on its original input path. Every intervening instruction is a wait, and the word conditions force a positive gap. Arrival retains that original input, the source read time, the literal length, the unit chain, and the exact target occurrence.

**Theorem 1.9 (The finite arrival inventory contains exactly the literal arrivals).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{\forall q:Q,{\forall d:\mathbb {N},{d\in \operatorname {arrivalLengths}(C,hP,I,q)\iff\operatorname {Nonempty}(\operatorname {Arrival}(C,hP,I,q,d))}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryUnitControl.mem_arrival_lengths` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite inventory ranges over the stopping times of all original inputs. An arrival's positive literal length is below its own input's stop time, so every actual arrival appears. This membership characterization connects original forest requests to actualL.

**Theorem 1.10 (Disjoint resource embedding into the full nominal carrier).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{\operatorname {Nonempty}(\operatorname {Embedding}(\operatorname {Resource}(C,hP,I),Q))}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryUnitControl.full_nominal_resource_embedding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Resource is the tagged sum of ZMod(3P), all actual read controls, Fin ell, and the pairs (q,i) with q a nonroot actual read and i in Fin(actualL(q)). The finite set of realized incoming lengths defines actualL by its maximum, and longestArrival chooses an actual request attaining it. Terminal labels separate the original outputs. Instruction kinds separate terminal, read, and wait controls. First-future-read uniqueness separates different target tails and separates every nonroot tail from the common prefix. Within a tail, remaining distances separate positions. The codomain is Q itself. Thus unused nominal states remain charged. For finite Q, finite cardinality applied to this embedding gives 3P+r+ell+sum_q actualL(q) at most card Q. The embedding also holds without a finiteness assumption on Q.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryUnitControl.finite_run_unique`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryUnitControl.full_nominal_resource_embedding`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryUnitControl.initialized_configuration_unique`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryUnitControl.initialized_prefix`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryUnitControl.mem_arrival_lengths`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryUnitControl.nonroot_has_arrival`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryUnitControl.prefix_first_read_no_return`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryUnitControl.waits_chain_injective`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryUnitControl.waits_physical_execution`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryUnitControl.waits_to_read_unique`
