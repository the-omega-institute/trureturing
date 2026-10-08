# Actual weighted history overlap

## Abstract

Actual full-history multiplicity gives a background-sensitive retained-weight inequality for every original initialized controller.

Fix an arbitrary integer P greater than one, represented in Lean by its positive natural value, arbitrary finite ell and h, a full finite nominal carrier Q, Controller P Q, and Initialized C hP ell h. Each original label in ZMod(3P) starts at the same initial control. The exact action word is W^ell R(W^+R)*, with at most h reads and immediate stopping after the last read. All positive literal waits, singleton continuations, and cycles terminating for every initialized label are retained. Unused nominal states remain charged. No supplied forest, row acyclicity, bounded wait, fixed P, injection, or J/s/Xi equation is a premise. NeZero(3P) and DecidableEq Q are representation instances; the original finite carrier supplies Fintype Q for the final charge.

All inventories below use the same C/hP/I. Node is its actual full History type, Event is a label together with its actual read index, and row(n)=(readControl(n),color(n)). The actual unique parent map determines children. The inherited score-independent core is the union of all binary targets and s distinct selected pure resolving targets. Its cardinal is N=3(P-1); extras are the remaining e targets. Binary baselines are maxima of all positive representatives 1+((delta-1) mod P), selected resolving baselines are their literal waits, and extras have baseline one. Tail(q)=L_q is the original actualL longest literal arrival. Every baseline l_q lies in [1,L_q].

BackgroundParent(n) means n is binary or lies on a selected pure resolving source row. OrdinaryParent(n) means n has exactly one child and is not a background parent. Ordinary is the subtype of all these actual parent histories. OrdinaryChild selects the unique child, not a row or a weight representative. OrdinaryChildren(q) is its target-q image. BackgroundChildren(q) includes every child of a background parent.

**Theorem 1.1 (Unique-parent child inventory).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{[\operatorname {DecidableEq}(Q)][\operatorname {NeZero}(3\times P)]\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{\forall q:Q,{{\{n\in \operatorname {nonroots}(C,hP,I)\mid{\operatorname {readControl}(C,hP,I,n)=q}\}=\operatorname {union}(\operatorname {backgroundChildren}(C,hP,I,q),\operatorname {ordinaryChildren}(C,hP,I,q))}\land{\operatorname {Disjoint}(\operatorname {backgroundChildren}(C,hP,I,q),\operatorname {ordinaryChildren}(C,hP,I,q))}\land{\operatorname {Injective}(\operatorname {ordinaryChild}(C,hP,I))}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryWeightedHistoryOverlap.actual_child_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every nonroot history has one original forest parent. Branching is at most two; a nonbackground internal parent is consequently unary. Unique parents make the ordinary child map injective and the two inventories disjoint. Equal rows, equal positive delays, or repeated drawings never identify different ordinary histories.

**Theorem 1.2 (Indexed occurrence separation).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{[\operatorname {DecidableEq}(Q)][\operatorname {NeZero}(3\times P)]\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{{\forall v:\operatorname {Event}(C,hP,I),{\exists! n:\operatorname {Node}(C,hP,I),{v\in \operatorname {indexedSupport}(C,hP,I,n)}}}\land{\forall n:\operatorname {Node}(C,hP,I),{\forall m:\operatorname {Node}(C,hP,I),{{n\neq m}\implies{\operatorname {Disjoint}(\operatorname {indexedSupport}(C,hP,I,n),\operatorname {indexedSupport}(C,hP,I,m))}}}}\land{\forall d:\operatorname {Ordinary}(C,hP,I),{\forall dprime:\operatorname {Ordinary}(C,hP,I),{{d\neq dprime}\implies{\operatorname {Disjoint}(\operatorname {indexedSupport}(C,hP,I,\operatorname {ordinaryChild}(C,hP,I,d)),\operatorname {indexedSupport}(C,hP,I,\operatorname {ordinaryChild}(C,hP,I,dprime)))}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryWeightedHistoryOverlap.actual_indexed_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The event stores (x,i), and its full prefix is uniquely determined. An ancestor and descendant containing the same label still use different indices. The ordinary child injectivity transports the original indexed-history separation without erasing equal-row occurrences. Each classified event therefore retains one full-history identity.

**Theorem 1.3 (Background and ordinary indexed events).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{[\operatorname {DecidableEq}(Q)][\operatorname {NeZero}(3\times P)]\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{\forall q:Q,{{\{v\in \operatorname {Event}(C,hP,I)\mid{{\operatorname {parent}(C,hP,I,\operatorname {event}(C,hP,I,v))\neq \operatorname {none}()}\land{\operatorname {readControl}(C,hP,I,\operatorname {event}(C,hP,I,v))=q}}\}=\operatorname {union}(\operatorname {backgroundEvents}(C,hP,I,q),\operatorname {ordinaryEvents}(C,hP,I,q))}\land{\operatorname {Disjoint}(\operatorname {backgroundEvents}(C,hP,I,q),\operatorname {ordinaryEvents}(C,hP,I,q))}\land{\forall v:\operatorname {Event}(C,hP,I),{\exists! n:\operatorname {Node}(C,hP,I),{v\in \operatorname {indexedSupport}(C,hP,I,n)}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryWeightedHistoryOverlap.actual_event_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

BackgroundEvents(q) and OrdinaryEvents(q) filter actual indexed occurrences by membership of their full prefix in the corresponding child inventory. Pulling back the unique-parent partition proves exact coverage and disjointness. The root events remain the original first-read events; every later occurrence is in this partition.

Let f range over real-valued functions on positive integers. Score(f,d) is internally the nonnegative real conversion of f(d) for d>0, with zero only as a total-function default at d=0. Every ordinary literal delta is positive, so under nonnegativity this is exactly f(delta). Weight(d)=Score(f,delta_d). Demands(q,c) is the finite subtype inventory of all ordinary parent histories whose child has slot (q,c). Af sums weights over every ordinary history. a(q,c) sums weights in Demands(q,c); m(q,c) is its finite maximum, with empty maximum zero. Distinct identities with equal weights contribute separately to Af and a. For an occupied background digit z=a; for a free digit z=a-m. Zf sums z over every actual nonfirst target and all three digits. Retained(q) sums m over the background-free digits.

**Theorem 1.4 (Exact retained weights and literal fidelity).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{[\operatorname {DecidableEq}(Q)][\operatorname {NeZero}(3\times P)]\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{\forall f:\operatorname {PNat}()\Rightarrow\operatorname {Real}(),{{\operatorname {Af}(C,hP,I,f)=\operatorname {Zf}(C,hP,I,f)+\sum_{q\in \operatorname {targets}(C,hP,I)}{\operatorname {retained}(C,hP,I,f,q)}}\land{0\le \operatorname {Zf}(C,hP,I,f)}\land{\forall q:Q,{\forall c:\operatorname {Fin}(3),{\operatorname {a}(C,hP,I,f,q,c)=\operatorname {z}(C,hP,I,f,q,c)+\operatorname {if}(c\in \operatorname {backgroundDigits}(C,hP,I,q),0,\operatorname {m}(C,hP,I,f,q,c))}}}\land{\forall q:Q,{\forall c:\operatorname {Fin}(3),{{\operatorname {demands}(C,hP,I,q,c)=\operatorname {empty}()}\implies{\operatorname {m}(C,hP,I,f,q,c)=0}}}}\land{{\forall x:\operatorname {PNat}(),{0\le \operatorname {f}(x)}}\implies{{\operatorname {Af}(C,hP,I,f)=\sum_{d\in \operatorname {Ordinary}(C,hP,I)}{\operatorname {f}(\operatorname {delay}(C,hP,I,\operatorname {val}(d)))}}\land{\forall q:Q,{\forall c:\operatorname {Fin}(3),{\operatorname {a}(C,hP,I,f,q,c)=\sum_{d\in \operatorname {demands}(C,hP,I,q,c)}{\operatorname {f}(\operatorname {delay}(C,hP,I,\operatorname {val}(d)))}}}}}}\land{{\operatorname {f}(1)=0}\implies{\forall d:\operatorname {Ordinary}(C,hP,I),{{\operatorname {delay}(C,hP,I,\operatorname {val}(d))=1}\implies{\operatorname {weight}(C,hP,I,f,d)=0}}}}\land{\forall d:\operatorname {Ordinary}(C,hP,I),{\forall dprime:\operatorname {Ordinary}(C,hP,I),{{\operatorname {row}(C,hP,I,\operatorname {val}(d))=\operatorname {row}(C,hP,I,\operatorname {val}(dprime))}\implies{\operatorname {delay}(C,hP,I,\operatorname {val}(d))=\operatorname {delay}(C,hP,I,\operatorname {val}(dprime))}}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryWeightedHistoryOverlap.retained_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite fiber summation counts each actual ordinary history once. Maximum is at most the nonnegative sum, so free-slot subtraction is the exact real difference and Zf is nonnegative. Summing the slot identity gives Af=Zf+sum Retained. The same result exposes the exact positive-literal sums, empty maxima, zero weight for literal wait one when f(1)=0, and original same-source-row delay coherence. The wait-one histories remain in Ordinary; no restricted zero-correction transport is asserted.

**Theorem 1.5 (One spare core digit).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{[\operatorname {DecidableEq}(Q)][\operatorname {NeZero}(3\times P)]\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{\forall f:\operatorname {PNat}()\Rightarrow\operatorname {Real}(),{{\forall x:\operatorname {PNat}(),{0\le \operatorname {f}(x)}}\implies{{\operatorname {Monotone}(f)}\implies{{\operatorname {LipschitzWith}(1,f)}\implies{\forall q:Q,{{q\in \operatorname {core}(C,hP,I)}\implies{\operatorname {retained}(C,hP,I,f,q)\le \operatorname {k}(C,hP,I,q)\times \operatorname {score}(f,\operatorname {baseline}(C,hP,I,q))+{\operatorname {tail}(C,hP,I,q)-\operatorname {baseline}(C,hP,I,q)}}}}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryWeightedHistoryOverlap.core_retained_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each actual ordinary delay at q is at most its original longest tail L_q. Monotonicity bounds every maximum by f(L_q). The actual core has k_q<=1; if k_q=0 no ordinary weight remains, and if k_q=1 the positive-integer Lipschitz bound gives f(L_q)<=f(l_q)+(L_q-l_q). No reduced wait is charged as a literal tail.

**Theorem 1.6 (Three-digit extra target bound).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{[\operatorname {DecidableEq}(Q)][\operatorname {NeZero}(3\times P)]\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{\forall f:\operatorname {PNat}()\Rightarrow\operatorname {Real}(),{{\forall x:\operatorname {PNat}(),{0\le \operatorname {f}(x)}}\implies{{\operatorname {Monotone}(f)}\implies{{\forall L:\operatorname {PNat}(),{3\times \operatorname {f}(L)\le L+1}}\implies{\forall q:Q,{{q\in \operatorname {extras}(C,hP,I)}\implies{\operatorname {retained}(C,hP,I,f,q)\le \operatorname {tail}(C,hP,I,q)+1}}}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryWeightedHistoryOverlap.extra_retained_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An extra target has no background digits. Its three retained maxima are individually bounded by f(L_q), and the contract 3f(L)<=L+1 pays their total with one joint longest target tail, irrespective of history multiplicity.

E=sum over all Targets of (L_q-1); E0=sum over Core of (l_q-1). These are natural sums with no negative truncation on actual targets, because 1<=l_q<=L_q. The inherited target set is exactly the disjoint union Core and Extras, with |Extras|=e.

**Theorem 1.7 (Every actual tail is charged once).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{[\operatorname {DecidableEq}(Q)][\operatorname {NeZero}(3\times P)]\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{\operatorname {E}(C,hP,I)+2\times \operatorname {e}(C,hP,I)=\operatorname {E0}(C,hP,I)+\sum_{q\in \operatorname {core}(C,hP,I)}{\operatorname {tail}(C,hP,I,q)-\operatorname {baseline}(C,hP,I,q)}+\sum_{q\in \operatorname {extras}(C,hP,I)}{\operatorname {tail}(C,hP,I,q)+1}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryWeightedHistoryOverlap.exact_tail_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a core, L_q-1=(l_q-1)+(L_q-l_q). Each extra has L_q-1 plus its own two units from 2e, yielding L_q+1. The disjoint actual partition ensures that every target and tail growth is charged exactly once.

**Theorem 1.8 (Original overlap correction and full nominal charge).**

$$\forall P:\mathbb {N},{\forall Q:Type_{u},{[\operatorname {DecidableEq}(Q)][\operatorname {NeZero}(3\times P)]\forall C:\operatorname {Controller}(P,Q),{\forall hP:1<P,{\forall ell:\mathbb {N},{\forall h:\mathbb {N},{\forall I:\operatorname {Initialized}(C,hP,ell,h),{[\operatorname {Fintype}(Q)]\forall f:\operatorname {PNat}()\Rightarrow\operatorname {Real}(),{{\operatorname {Admissible}(f)}\implies{{\operatorname {E0}(C,hP,I)+\operatorname {Af}(C,hP,I,f)-\sum_{q\in \operatorname {core}(C,hP,I)}{\operatorname {k}(C,hP,I,q)\times \operatorname {score}(f,\operatorname {baseline}(C,hP,I,q))}-\operatorname {Zf}(C,hP,I,f)\le \operatorname {E}(C,hP,I)+2\times \operatorname {e}(C,hP,I)}\land{3\times P+2\times 3\times {P-1}+1+2\times \operatorname {e}(C,hP,I)+ell+\operatorname {E}(C,hP,I)\le \operatorname {card}(Q)}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/StationaryWeightedHistoryOverlap.necessary_inequality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Admissible means f is nonnegative and monotone on positive integers, LipschitzWith 1, f(1)=0, and 3f(L)<=L+1 for every positive L. The retained identity, core/extra bounds, and exact tail decomposition yield E+2e>=E0+Af-sum_core k_q f(l_q)-Zf. Score(f,l_q) equals the literal positive f(l_q). The exact target-to-NonrootRead equivalence and the full nominal resource embedding then charge all terminal states, actual reads, common-prefix positions and longest wait-chain units against full Q, including unused states.

This is the necessary general overlap bound, with unrestricted J, s and Xi. Zf remains present for multiple collisions. The original 83.12/82.14 restricted zero-correction transport, occupied-digit equality and injection of remaining demands are separate obligations. No synthesis, sufficiency or unconditional nine-point capacity twenty-nine assertion follows here.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryWeightedHistoryOverlap.actual_child_partition`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryWeightedHistoryOverlap.actual_event_partition`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryWeightedHistoryOverlap.actual_indexed_partition`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryWeightedHistoryOverlap.core_retained_bound`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryWeightedHistoryOverlap.exact_tail_decomposition`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryWeightedHistoryOverlap.extra_retained_bound`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryWeightedHistoryOverlap.necessary_inequality`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/StationaryWeightedHistoryOverlap.retained_identity`
- Dependency: [D5/S3/ObserverMemory/Algorithms/StationaryHistorySlotGraph](StationaryHistorySlotGraph.md)
