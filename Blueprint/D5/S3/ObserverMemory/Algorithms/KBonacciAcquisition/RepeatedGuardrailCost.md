# Exact cost of repeated guarded phase queries

## Abstract

Guarded INITIAL phase labels have exact paid repeated-query cost.

**Theorem 1.1 (A guarded family of arbitrary initial labels).**

$$(\forall (Y:\operatorname{Type}), ((\forall (g:\mathbb{N}), ((\forall (u:\mathbb{N}), ((\forall (h:\mathbb{N}), ((\forall (rho:\mathbb{N}), ((((2 \leq g \land 2 \leq u \land 1 \leq h \land 1 \leq rho \land rho < u \land \operatorname{Coprime}\left(u, rho\right))) \implies (\operatorname{let} p=h \cdot u + rho \operatorname{in} (\operatorname{let} k=\operatorname{natSub}\left(g \cdot p, 1\right) \operatorname{in} (\operatorname{let} m=g \cdot u \operatorname{in} ((\forall (labels:\operatorname{Fin}\left(p\right) \to Y), (\operatorname{let} n=\operatorname{card}\left(\operatorname{range}\left(labels\right)\right) \operatorname{in} (\operatorname{let} R=\operatorname{natSub}\left(\operatorname{clog}\left(2, n\right), 1\right) \operatorname{in} (\operatorname{let} M=\operatorname{natSub}\left(u, R \cdot rho\right) \operatorname{in} (\operatorname{let} A=labels\left(0\right) \operatorname{in} ((\forall (f:\operatorname{Option}\left(\operatorname{LiveRecord}\left(k\right)\right) \to Y), ((\forall (v:\operatorname{ZMod}\left(2\right)), ((\forall (a:\operatorname{Bool}), ((((3 \leq n \land (\forall (j:\operatorname{Fin}\left(p\right)), (((labels\left(j\right) \ne A) \implies ((1 \leq \operatorname{val}\left(j\right) \land \operatorname{val}\left(j\right) \leq M))))) \land (\forall (j:\operatorname{Fin}\left(p\right)), ((\forall (s:\mathbb{N}), (((s < k) \implies (f\left(\operatorname{some}\left((v,-\operatorname{cast}\left(\operatorname{val}\left(j\right) \cdot g, \operatorname{ZMod}\left(k + 1\right)\right),s)\right)\right) = labels\left(j\right))))))))) \implies (\operatorname{OriginalFiberCost}\left(k, m, \operatorname{positivek}, a, f, v\right) = \operatorname{cast}\left(R \cdot h + 1, \operatorname{ENat}\right))))))))))))))))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/RepeatedGuardrailCost.original_repeated_guardrail_cost` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The codomain Y is arbitrary. The finite image of labels has n distinct elements. Write p=h*u+rho, T=g*p, k=T-1, and m=g*u. Coprimality gives gcd(m,T)=g, and m<T. The initial phase indexed by j is -j*g modulo T. The function f has the same prescribed label at every legal tail of each such phase in the fixed initial value fiber v. Its value at none is arbitrary, and the selector returns that value freely on initial rejection. No condition is imposed on other value fibers. The symbol positivek denotes the proof of 0<k derived from the displayed parameter bounds.

The Boolean parameter a is localAlphabet. When it is true, the alphabet contains exactly the internally admissible Boolean words of length m; when it is false, every Boolean word of length m is available. Initial histories are finite lists of blocks from that alphabet, flattened and evaluated by the original scalar and scanner. A natural budget b is feasible when one selector emits words from the alphabet, returns f(none) on free initial rejection, and succeeds within b paid words for every such initial history whose endpoint output is some v. Success means returning f of that INITIAL record, with early stopping permitted. OriginalFiberCost is the infimum, in ENat, of all these feasible natural budgets; an empty set gives infinity.

Let A be the label at phase zero, R=clog(2,n)-1, and M=u-R*rho, with natural subtraction. Every phase with a label different from A lies at an index from 1 through M. Choosing one index for each label, and index zero for A, injects the label image into 0 through M. Thus M>=n-1>=2. In particular R*rho<u, M+R*rho=u, and R*rho+2<=u; the guard is derived from the support condition.

For the lower bound choose actual complete-word initial histories with the same value and tail zero, one for each label. Throughout the first R*h paid blocks, every nonzero coefficient of these phases has block index divisible by h. On any shared chronological archive the current scalar and tail are common. A silent block preserves a common scalar endpoint. The scanner either accepts every candidate with a common new tail or rejects them all. An early stop or uniform absorbing rejection can identify only one label. An active block has at most two successful scalar endpoints. Induction on the actual execute function produces a binary transcript with at most R questions, counting every intervening paid word. Its leaves number at most 2^R, whereas n>2^R. Every feasible finite budget is therefore at least R*h+1.

For the upper bound assign distinct R+1 bit codes to the initial labels, with the code of A equal to zero. At paid block index ell*h, for ell from 0 through R, place a pulse at local position (j+ell*rho)*g-1 exactly when the ell-th bit of label j is one. Every other position is zero. The guard places each pulse in the complete word. Its absolute position is ell*T+j*g-1, so the scalar endpoint difference reads exactly that INITIAL code bit. The word starts with zero, its pulses are separated by at least g, and its terminal tail is at most one. The same word is internally admissible and safe from every legal old tail. Between query words issue h-1 complete zero words. All padding and waiting words are paid and recorded.

The selector receives the free initial value and the chronological archive of complete issued words with their endpoint outputs. It chooses the next word from the archive length. After R*h+1 words it matches the archive to the unique initial label code. Differences of successive query endpoints recover every coordinate of that code. The result is the label of the INITIAL record throughout the execution. The construction works in both complete-word alphabets, with all actual initial histories and tails in scope. The infimum in ENat includes possible infinite costs; this family has the displayed finite cost. The proof also includes h=1 and R=1.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/RepeatedGuardrailCost.original_repeated_guardrail_cost`
- Dependency: [D5/S3/Observer/Budget/WorstCaseDepthInformationLowerBound](../../../Observer/Budget/WorstCaseDepthInformationLowerBound.md)
- Dependency: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalNarrowCost](OriginalNarrowCost.md)
