# A waiting lower bound for arbitrary initial record targets

## Abstract

Arbitrary initial record labels require first-window waiting and binary depth.

**Definition 1.1 (The joint original record of a literal history).**

$$(\forall (k:\mathbb{N}), ((\forall (hk:0 < k), ((\forall (w:\operatorname{List}(\operatorname{Bool})), (\operatorname{OriginalRecord}(k,hk,w) = \operatorname{map}(\operatorname{eval}(\operatorname{scanner}(k,hk),w),(\lambda (tail:\operatorname{Fin}(k)), ((\operatorname{value}(k,0,w),\operatorname{cast}(\operatorname{length}(w),\operatorname{ZMod}(k + 1)),\operatorname{val}(tail)))))))))))$$

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalNarrowCost.OriginalRecord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The accepted record consists of the original low-bit-first scalar value, the literal word length modulo k+1, and the scanner's actual final run of ones. All three coordinates come from the same word. A rejected word has record none.

**Definition 1.2 (Uniform success on the whole initial free-value fiber).**

$$(\forall (Y:\operatorname{Type}), ((\forall (k:\mathbb{N}), ((\forall (m:\mathbb{N}), ((\forall (hk:0 < k), ((\forall (a:\operatorname{Bool}), ((\forall (f:\operatorname{Option}(\operatorname{LiveRecord}(k)) \to Y), ((\forall (v:\operatorname{ZMod}(2)), ((\forall (d:\mathbb{N}), (\operatorname{OriginalFiberFeasible}(k,m,hk,a,f,v,d) = (\exists (pi:\operatorname{Selector}(m,Y)), (((\forall (y:\operatorname{Option}(\operatorname{ZMod}(2))), ((\forall (archive:\operatorname{Archive}(m)), ((\forall (B:\operatorname{Fin}(m) \to \operatorname{Bool}), (((pi\left(y, archive\right) = \operatorname{inr}(B)) \implies (((a = \operatorname{true}) \implies (\operatorname{DBonacciAdmissible}(k,m,B))))))))))) \land pi\left(\operatorname{none}, []\right) = \operatorname{inl}(f\left(\operatorname{none}\right)) \land (\forall (history:\operatorname{List}(\operatorname{AllowedBlock}(k,m,a))), (\operatorname{let} w=\operatorname{flatMap}(history,(\lambda (action:\operatorname{AllowedBlock}(k,m,a)), (\operatorname{ofFn}(\operatorname{val}(action))))) \operatorname{in} (((\operatorname{output}(k,hk,w) = \operatorname{some}(v)) \implies ((\exists (c:\mathbb{N}), ((c \leq d \land \operatorname{execute}(k,hk,pi,d,w,\operatorname{some}(v),[]) = \operatorname{some}((f\left(\operatorname{OriginalRecord}(k,hk,w)\right),c)))))))))))))))))))))))))))))$$

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalNarrowCost.OriginalFiberFeasible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

One selector receives the free initial endpoint and a chronological archive of complete issued words with their endpoint replies. At each step it either stops or appends every position of its chosen word before reading the new endpoint. The target is f of the INITIAL joint record throughout execution. Correctness quantifies every actual initial history of AllowedBlock actions in the fixed-value fiber, including every realizable initial tail. No phase or tail is revealed.

When a is true, every word chosen by the selector is internally admissible; when a is false, every complete Boolean word is allowed. The scanner still checks actual seams in either alphabet. The initial rejection stops freely with f(none). Each issued block costs one, including zero words, padding, and rejected blocks. Early stops may use less than the uniform budget d.

**Definition 1.3 (Least uniform acquisition cost, with infinity allowed).**

$$(\forall (Y:\operatorname{Type}), ((\forall (k:\mathbb{N}), ((\forall (m:\mathbb{N}), ((\forall (hk:0 < k), ((\forall (a:\operatorname{Bool}), ((\forall (f:\operatorname{Option}(\operatorname{LiveRecord}(k)) \to Y), ((\forall (v:\operatorname{ZMod}(2)), (\operatorname{OriginalFiberCost}(k,m,hk,a,f,v) = \operatorname{iInf}((\lambda (budget:\operatorname{Subtype}((\lambda (d:\mathbb{N}), (\operatorname{OriginalFiberFeasible}(k,m,hk,a,f,v,d))))), (\operatorname{cast}(\operatorname{val}(budget),\operatorname{ENat}))))))))))))))))))$$

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalNarrowCost.OriginalFiberCost` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cost is the infimum in ENat of all feasible natural budgets. If there is no feasible budget, the infimum of the empty family is infinity.

**Theorem 1.4 (First-window waiting plus binary discrimination).**

$$(\forall (Y:\operatorname{Type}), ((\forall (k:\mathbb{N}), ((\forall (m:\mathbb{N}), ((((2 \leq k \land 1 \leq m \land m < k + 1)) \implies ((\forall (f:\operatorname{Option}(\operatorname{LiveRecord}(k)) \to Y), ((\forall (v:\operatorname{ZMod}(2)), ((\forall (a:\operatorname{Bool}), (\operatorname{let} g=\operatorname{gcd}(m,k + 1) \operatorname{in} (\operatorname{let} u=\operatorname{div}(m,g) \operatorname{in} (\operatorname{let} p=\operatorname{div}(k + 1,g) \operatorname{in} (\operatorname{let} h=\operatorname{div}(p,u) \operatorname{in} (\operatorname{let} q=(\lambda (j:\operatorname{Fin}(u)), (\operatorname{some}((v,-\operatorname{cast}(\operatorname{val}(j) \cdot g,\operatorname{ZMod}(k + 1)),0)))) \operatorname{in} (\operatorname{let} n=\operatorname{card}(\operatorname{range}((\lambda (j:\operatorname{Fin}(u)), (f\left(q\left(j\right)\right))))) \operatorname{in} (((3 \leq n) \implies (\operatorname{cast}(\operatorname{natSub}(h + \operatorname{clog}(2,n),1),\operatorname{ENat}) \leq \operatorname{OriginalFiberCost}(k,m,\operatorname{positivek},a,f,v)))))))))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalNarrowCost.original_cost_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here g=gcd(m,k+1), u=m/g, p=(k+1)/g, and h=p/u uses natural floor division. There are u tail-zero sources q(j), indexed by j in Fin u, and n is the number of distinct INITIAL labels f(q(j)). Nat.clog(2,n) is the ceiling binary logarithm; positivek denotes the positivity proof implied by k>=2. The target f is otherwise arbitrary and may depend on the INITIAL tail.

Every q(j) is realized by an actual allowed history. A successful lawful selector gives a decision tree with the same finite budget, the same complete-word actions, and the same endpoint-dependent continuation. Uniform rejection of the first word would erase all distinct labels. Otherwise its two successful replies split the label image, so one child retains at least ceiling(n/2) labels, hence at least two.

The coefficients vanish at every continuation position from m through h*m-1 for all selected phases. The sources in the chosen child have the same current value and tail. Any subsequent adaptive words therefore give a shared chronological archive for h-1 paid steps, or reject all these sources together. Uniform rejection and an early stop cannot recover their distinct INITIAL labels. After that shared prefix, binary branching needs at least clog(2,ceiling(n/2)) further words. The integer logarithm recurrence yields h+clog(2,n)-1.

No lower bound g>=2 or root first-zero condition is required. The case g=1 is included. When h=1 the quiet prefix has length zero and the estimate is the binary depth bound. The inequality also holds for targets whose cost is infinity.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalNarrowCost.OriginalFiberCost`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalNarrowCost.OriginalFiberFeasible`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalNarrowCost.OriginalRecord`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalNarrowCost.original_cost_lower`
- Dependency: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NarrowWindowCost](NarrowWindowCost.md)
- Dependency: [D5/S3/ObserverMemory/Algorithms/KBonacciIrreversibleAcquisition](../KBonacciIrreversibleAcquisition.md)
