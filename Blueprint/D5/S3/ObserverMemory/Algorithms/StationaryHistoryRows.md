# StationaryHistoryRows

## Abstract

Actual row execution and branching from original histories.

The following constructions use the same arbitrary Initialized C. For each parent with actual children, delay is the full natural gap time(child)-(time(parent)+1), and nextTarget is the child's actual read control. These definitions choose one actual child, then prove independence of that choice. They are totalized on leaves, where no arrival is requested. All subtraction in natural-time expressions is natural subtraction. NeZero(3P) follows from P>1. A source row is the pair (readControl,color); physical supports are phases at the current read, while indexed supports retain (original input,read index).

**Theorem 1.1 (Actual consecutive-read wait chain).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{\forall x:\operatorname {ZMod}(3\times P),{\forall i:\mathbb {N},{{i+1<\operatorname {reads}(C,hP,I,x)}\implies{\operatorname {Waits}(C,\operatorname {readTime}(C,hP,I,x,i+1)-{\operatorname {readTime}(C,hP,I,x,i)+1},\operatorname {replay}(C,\operatorname {initial}(C),\operatorname {eventWord}(C,hP,I,(x,i))),\operatorname {control}(\operatorname {run}(C,hP,(x,\operatorname {initial}(C)),\operatorname {readTime}(C,hP,I,x,i+1))))}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryHistoryRows.event_arrival` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There is no intervening read between two consecutive indexed reads, and no halt occurs in this live segment. The original trajectory_waits theorem converts those actual wait instructions into the literal chain.

**Theorem 1.2 (Recorded answer selects the actual row).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{[\operatorname {NeZero}(3\times P)]\forall n:\operatorname {History}(C,hP,I),{\exists row:\operatorname {Fin}(3)\to Q,{\operatorname {instruction}(C,\operatorname {readControl}(C,hP,I,n))=\operatorname {read}(row)}\land{\operatorname {postControl}(C,hP,I,n)=\operatorname {row}(\operatorname {color}(C,hP,I,n))}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryHistoryRows.history_row_execution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pre-read control has a read instruction. Replaying the complete word ends at that instruction's successor for the recorded absolute answer.

**Theorem 1.3 (Every child has a positive actual arrival).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{[\operatorname {NeZero}(3\times P)]\forall n:\operatorname {History}(C,hP,I),{\forall p:\operatorname {History}(C,hP,I),{{\operatorname {parent}(C,hP,I,n)=\operatorname {some}(p)}\implies{{0<\operatorname {time}(C,hP,I,n)-{\operatorname {time}(C,hP,I,p)+1}}\land{{\operatorname {Waits}(C,\operatorname {time}(C,hP,I,n)-{\operatorname {time}(C,hP,I,p)+1},\operatorname {postControl}(C,hP,I,p),\operatorname {readControl}(C,hP,I,n))}\land{\operatorname {IsRead}(C,\operatorname {readControl}(C,hP,I,n))}}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryHistoryRows.child_arrival` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The canonical prefix parent is the immediately preceding indexed read. WordShape gives a positive literal gap, and the actual next read is the endpoint.

**Theorem 1.4 (One literal wait and target per continuing row).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{[\operatorname {NeZero}(3\times P)]\forall n:\operatorname {History}(C,hP,I),{\forall m:\operatorname {History}(C,hP,I),{\forall a:\operatorname {History}(C,hP,I),{\forall b:\operatorname {History}(C,hP,I),{{{{\operatorname {parent}(C,hP,I,a)=\operatorname {some}(n)}\land{\operatorname {parent}(C,hP,I,b)=\operatorname {some}(m)}}\land{{\operatorname {readControl}(C,hP,I,n)=\operatorname {readControl}(C,hP,I,m)}\land{\operatorname {color}(C,hP,I,n)=\operatorname {color}(C,hP,I,m)}}}\implies{{\operatorname {time}(C,hP,I,a)-{\operatorname {time}(C,hP,I,n)+1}=\operatorname {time}(C,hP,I,b)-{\operatorname {time}(C,hP,I,m)+1}}\land{\operatorname {readControl}(C,hP,I,a)=\operatorname {readControl}(C,hP,I,b)}}}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryHistoryRows.same_row_arrival` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same source control and answer determine the same post-read control. Deterministic first-future-read uniqueness forces equal literal waits and equal read targets even across different levels or terminating control cycles.

**Theorem 1.5 (A terminal row has one full history).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{[\operatorname {NeZero}(3\times P)]\forall n:\operatorname {History}(C,hP,I),{\forall m:\operatorname {History}(C,hP,I),{{{\operatorname {IsLeaf}(C,hP,I,n)}\land{{\operatorname {readControl}(C,hP,I,n)=\operatorname {readControl}(C,hP,I,m)}\land{\operatorname {color}(C,hP,I,n)=\operatorname {color}(C,hP,I,m)}}}\implies{n=m}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryHistoryRows.terminal_row_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A common row has one post-read instruction. If it halts, correctness forces a common original label; both histories are that label's final indexed read.

**Theorem 1.6 (The complete child word retains the literal waits).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{[\operatorname {NeZero}(3\times P)]\forall n:\operatorname {History}(C,hP,I),{\forall p:\operatorname {History}(C,hP,I),{{\operatorname {parent}(C,hP,I,n)=\operatorname {some}(p)}\implies{\operatorname {word}(n)=\operatorname {append}(\operatorname {append}(\operatorname {word}(p),\operatorname {replicate}(\operatorname {time}(C,hP,I,n)-{\operatorname {time}(C,hP,I,p)+1},\operatorname {wait}())),\operatorname {singleton}(\operatorname {read}(\operatorname {color}(C,hP,I,n))))}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryHistoryRows.child_word` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A child is its complete parent word, every intervening unit wait, and one read with its actual answer. No modular reduction shortens this word.

**Theorem 1.7 (One child per absolute answer).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{[\operatorname {NeZero}(3\times P)]\forall p:\operatorname {History}(C,hP,I),{\forall n:\operatorname {History}(C,hP,I),{\forall m:\operatorname {History}(C,hP,I),{{{{\operatorname {parent}(C,hP,I,n)=\operatorname {some}(p)}\land{\operatorname {parent}(C,hP,I,m)=\operatorname {some}(p)}}\land{\operatorname {color}(C,hP,I,n)=\operatorname {color}(C,hP,I,m)}}\implies{n=m}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryHistoryRows.child_digit_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The parent's row fixes the literal continuation. Equal next answers therefore give equal complete words, hence the same actual history.

**Theorem 1.8 (Chosen arrivals are independent of the child).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{[\operatorname {NeZero}(3\times P)]\forall n:\operatorname {History}(C,hP,I),{\forall p:\operatorname {History}(C,hP,I),{{\operatorname {parent}(C,hP,I,n)=\operatorname {some}(p)}\implies{{0<\operatorname {delay}(C,hP,I,p)}\land{{\operatorname {time}(C,hP,I,n)-{\operatorname {time}(C,hP,I,p)+1}=\operatorname {delay}(C,hP,I,p)}\land{{\operatorname {readControl}(C,hP,I,n)=\operatorname {nextTarget}(C,hP,I,p)}\land{\operatorname {historyShift}(C,hP,I,n)=\operatorname {historyShift}(C,hP,I,p)+\operatorname {delay}(C,hP,I,p)}}}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryHistoryRows.child_delay_target` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every actual child has the chosen positive literal delay and next target. Its physical shift increases by the entire delay, including every wrap.

**Theorem 1.9 (Actual delay and target cohere on a shared row).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{[\operatorname {NeZero}(3\times P)]\forall n:\operatorname {History}(C,hP,I),{\forall m:\operatorname {History}(C,hP,I),{{{\operatorname {Nonempty}(\operatorname {children}(C,hP,I,n))}\land{{\operatorname {readControl}(C,hP,I,n)=\operatorname {readControl}(C,hP,I,m)}\land{\operatorname {color}(C,hP,I,n)=\operatorname {color}(C,hP,I,m)}}}\implies{{\operatorname {delay}(C,hP,I,n)=\operatorname {delay}(C,hP,I,m)}\land{\operatorname {nextTarget}(C,hP,I,n)=\operatorname {nextTarget}(C,hP,I,m)}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryHistoryRows.row_delay_target` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One continuing history forces every history on its actual row to continue: a terminal history there would force them to be the same history. They have one literal delay and one read target while retaining their identities.

**Theorem 1.10 (Every supporting input continues).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{[\operatorname {NeZero}(3\times P)]\forall p:\operatorname {History}(C,hP,I),{\forall x:\operatorname {ZMod}(3\times P),{{{\operatorname {Nonempty}(\operatorname {children}(C,hP,I,p))}\land{x\in \operatorname {support}(C,hP,I,p)}}\implies{\exists n:\operatorname {History}(C,hP,I),{\operatorname {parent}(C,hP,I,n)=\operatorname {some}(p)}\land{x\in \operatorname {support}(C,hP,I,n)}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryHistoryRows.support_successor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the parent has an actual child, its post-read control is not a halt. Every input in that parent has its own indexed successor read, including singleton continuations.

**Theorem 1.11 (Exact translated child fiber).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{[\operatorname {NeZero}(3\times P)]\forall n:\operatorname {History}(C,hP,I),{\forall p:\operatorname {History}(C,hP,I),{\forall x:\operatorname {ZMod}(3\times P),{{\operatorname {parent}(C,hP,I,n)=\operatorname {some}(p)}\implies{x\in \operatorname {support}(C,hP,I,n)\iff{x\in \operatorname {support}(C,hP,I,p)}\land{\operatorname {digit}(hP,x+\operatorname {historyShift}(C,hP,I,n))=\operatorname {color}(C,hP,I,n)}}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryHistoryRows.child_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The child consists exactly of parent labels whose phase at its next read has the child's absolute answer. The fiber is derived from actual successors.

**Theorem 1.12 (At most two actual children).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{[\operatorname {NeZero}(3\times P)]\forall p:\operatorname {History}(C,hP,I),{\operatorname {card}(\operatorname {children}(C,hP,I,p))\le 2}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryHistoryRows.branching` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A literal translation of one digit block yields two possible next digits, separated by the residue cut. Child-answer injectivity gives at most two nonempty children.

**Theorem 1.13 (Exactly 3(P-1) binary full histories).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{[\operatorname {NeZero}(3\times P)]\operatorname {card}(\operatorname {filter}(\operatorname {univ}(),n:\operatorname {History}(C,hP,I)\mapsto\operatorname {card}(\operatorname {children}(C,hP,I,n))=2))=3\times{P-1}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryHistoryRows.binary_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each actual nonroot has one parent. Summing child counts and retaining the unary histories gives leaves minus roots as the binary count: 3P-3.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryHistoryRows.binary_count`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryHistoryRows.branching`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryHistoryRows.child_arrival`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryHistoryRows.child_delay_target`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryHistoryRows.child_digit_injective`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryHistoryRows.child_support`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryHistoryRows.child_word`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryHistoryRows.event_arrival`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryHistoryRows.history_row_execution`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryHistoryRows.row_delay_target`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryHistoryRows.same_row_arrival`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryHistoryRows.support_successor`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryHistoryRows.terminal_row_unique`
- Dependency: [D5/S3/ObserverMemory/Algorithms/StationaryHistoryData](StationaryHistoryData.md)
