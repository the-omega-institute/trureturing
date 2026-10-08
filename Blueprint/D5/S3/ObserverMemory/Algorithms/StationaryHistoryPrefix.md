# StationaryHistoryPrefix

## Abstract

Actual complete action prefixes, indexed reads, roots, and original terminal histories.

Fix P greater than one, one controller C on the full nominal carrier Q, and Initialized C hP ell h. Every original x in ZMod(3P) starts at the common initial control and physical phase x. Wait adds one, read returns the absolute digit floor(val/P), and halt stores an original label. Each path has ell initial waits, a first read, positive literal waits between reads, at most h reads, and halt immediately after its final read. Long waits, modular wraps, singleton continuations, unused nominal states, and control cycles which terminate on all initialized inputs are retained.

Action records wait, read with its actual answer, or halt with its stored label. Trace x t records every action before time t. The finite ordered set readTimes x enumerates all actual read times; reads x is its cardinality. Event is the dependent pair (x,i), with i in Fin(reads x). Its full eventWord ends at that read and includes all previous waits and answers. History is the finite image of these words; word(n) means its full list n.val. Drawing an existing path again introduces no node. Sharing a row or a wait length does not identify two different full words. In a physical-phase expression, every natural shift is cast into ZMod(3P); the shift itself remains a literal natural number.

**Theorem 1.1 (Exact prefix replay).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall x:\operatorname {ZMod}(3\times P),{\forall t:\mathbb {N},{\operatorname {run}(C,hP,(x,\operatorname {initial}(C)),t)=(x+\operatorname {shift}(\operatorname {trace}(C,hP,x,t)),\operatorname {replay}(C,\operatorname {initial}(C),\operatorname {trace}(C,hP,x,t)))}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryHistoryPrefix.trace_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Replay is the left fold of the controller transition over the complete action and answer word. The list fold concatenation law separates the earlier prefix from its next action, so induction on time reconstructs the control. The physical phase is x plus the number of literal wait actions; reads and absorbing halts contribute no physical increment.

**Theorem 1.2 (Every history has an indexed occurrence).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{[\operatorname {NeZero}(3\times P)]\operatorname {Surjective}(\operatorname {event}(C,hP,I))}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryHistoryPrefix.event_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

History is the finite image of full indexed read prefixes. Every history therefore has an original input and read index producing it.

**Theorem 1.3 (One history per read index of an input).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{[\operatorname {NeZero}(3\times P)]\forall x:\operatorname {ZMod}(3\times P),{\operatorname {Injective}((i:\operatorname {Fin}(\operatorname {reads}(C,hP,I,x))\mapsto\operatorname {event}(C,hP,I,(x,i))))}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryHistoryPrefix.event_input_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a fixed original input, equal full prefixes have equal lengths and read times. The increasing enumeration of read times then gives the same read index.

**Theorem 1.4 (An indexed prefix reconstructs its read).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{\forall v:\operatorname {Event}(C,hP,I),{{\operatorname {run}(C,hP,(\operatorname {fst}(v),\operatorname {initial}(C)),\operatorname {readTime}(C,hP,I,\operatorname {fst}(v),\operatorname {snd}(v)))=(\operatorname {fst}(v)+\operatorname {shift}(\operatorname {dropLast}(\operatorname {eventWord}(C,hP,I,v))),\operatorname {replay}(C,\operatorname {initial}(C),\operatorname {dropLast}(\operatorname {eventWord}(C,hP,I,v))))}\land{\operatorname {eventWord}(C,hP,I,v)=\operatorname {append}(\operatorname {dropLast}(\operatorname {eventWord}(C,hP,I,v)),\operatorname {singleton}(\operatorname {read}(\operatorname {digit}(hP,\operatorname {fst}(\operatorname {run}(C,hP,(\operatorname {fst}(v),\operatorname {initial}(C)),\operatorname {readTime}(C,hP,I,\operatorname {fst}(v),\operatorname {snd}(v))))))))}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryHistoryPrefix.event_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Removing the last action leaves the exact pre-read trace. Replay reconstructs its configuration, and the final recorded answer is the actual absolute digit there.

**Theorem 1.5 (Configuration of a supporting label).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{[\operatorname {NeZero}(3\times P)]\forall n:\operatorname {History}(C,hP,I),{\forall x:\operatorname {ZMod}(3\times P),{{x\in \operatorname {support}(C,hP,I,n)}\implies{\operatorname {run}(C,hP,(x,\operatorname {initial}(C)),\operatorname {time}(C,hP,I,n))=(x+\operatorname {historyShift}(C,hP,I,n),\operatorname {readControl}(C,hP,I,n))}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryHistoryPrefix.history_configuration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Support consists exactly of original labels whose indexed read produces this full prefix. Time is word length minus one, level is the number of recorded reads minus one, and historyShift counts every literal wait.

**Theorem 1.6 (Unique prefix parent).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{[\operatorname {NeZero}(3\times P)]\forall x:\operatorname {ZMod}(3\times P),{\forall i:\mathbb {N},{{i+1<\operatorname {reads}(C,hP,I,x)}\implies{\operatorname {parent}(C,hP,I,\operatorname {event}(C,hP,I,(x,i+1)))=\operatorname {some}(\operatorname {event}(C,hP,I,(x,i)))}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryHistoryPrefix.parent_successor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The parent truncates the full word to the greatest earlier read position. It is defined from the word itself, so every nonroot history has one parent regardless of row sharing or repeated control states.

**Theorem 1.7 (Exactly the first-answer roots).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{[\operatorname {NeZero}(3\times P)]\forall n:\operatorname {History}(C,hP,I),{\operatorname {parent}(C,hP,I,n)=\operatorname {none}()\iff\exists c:\operatorname {Fin}(3),n=\operatorname {root}(C,hP,I,c)}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryHistoryPrefix.roots_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The three roots are ell literal waits followed by one read with answer c. Every answer occurs because all original input phases are initialized.

**Theorem 1.8 (Literal time accounting).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{[\operatorname {NeZero}(3\times P)]\forall n:\operatorname {History}(C,hP,I),{\operatorname {time}(C,hP,I,n)=\operatorname {historyShift}(C,hP,I,n)+\operatorname {level}(C,hP,I,n)}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryHistoryPrefix.history_time_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Before the current read, each live action is either one wait or an earlier read. Thus time equals physical shift plus read level, without reducing the shift modulo P or modulo 3P.

**Theorem 1.9 (Actual graph leaves).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{[\operatorname {NeZero}(3\times P)]\forall n:\operatorname {History}(C,hP,I),{\operatorname {IsLeaf}(C,hP,I,n)\iff\exists x:\operatorname {ZMod}(3\times P),\operatorname {instruction}(C,\operatorname {replay}(C,\operatorname {initial}(C),\operatorname {word}(n)))=\operatorname {halt}(x)}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryHistoryPrefix.leaf_iff_terminal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

IsLeaf means that no actual history has this prefix as parent. It is equivalent to halt immediately after the recorded read. A nonfinal read has a later actual child even when its support is a singleton.

**Theorem 1.10 (Every leaf emits its original supporting label).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{[\operatorname {NeZero}(3\times P)]\forall n:\operatorname {History}(C,hP,I),{\forall x:\operatorname {ZMod}(3\times P),{{{\operatorname {IsLeaf}(C,hP,I,n)}\land{x\in \operatorname {support}(C,hP,I,n)}}\implies{\operatorname {instruction}(C,\operatorname {replay}(C,\operatorname {initial}(C),\operatorname {word}(n)))=\operatorname {halt}(x)}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryHistoryPrefix.leaf_original` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A supporting occurrence of a graph leaf is that input's final read. Its post-read instruction halts with the same original label.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryHistoryPrefix.event_input_injective`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryHistoryPrefix.event_reconstruction`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryHistoryPrefix.event_surjective`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryHistoryPrefix.history_configuration`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryHistoryPrefix.history_time_decomposition`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryHistoryPrefix.leaf_iff_terminal`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryHistoryPrefix.leaf_original`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryHistoryPrefix.parent_successor`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryHistoryPrefix.roots_exact`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryHistoryPrefix.trace_reconstruction`
- Dependency: [D5/S3/ObserverMemory/Algorithms/FixedForestTargetInventory](FixedForestTargetInventory.md)
- Dependency: [D5/S3/ObserverMemory/Algorithms/StationaryUnitControl](StationaryUnitControl.md)
