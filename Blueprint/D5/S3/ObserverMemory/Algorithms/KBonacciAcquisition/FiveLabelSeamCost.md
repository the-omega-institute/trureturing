# Five labels across an actual terminal seam

## Abstract

Five initial phase labels have exact paid seam cost h plus two.

**Theorem 1.1 (Exact acquisition cost of five initial phase labels).**

$$(\forall (Y:\operatorname{Type}), ((\forall (g:\mathbb{N}), ((\forall (h:\mathbb{N}), ((((2 \leq g \land 1 \leq h)) \implies (\operatorname{let} p=5 \cdot h + 1 \operatorname{in} (\operatorname{let} k=\operatorname{natSub}\left(g \cdot p, 1\right) \operatorname{in} (\operatorname{let} m=5 \cdot g \operatorname{in} ((\forall (labels:\operatorname{Fin}\left(5\right) \to Y), (((\operatorname{Injective}\left(labels\right)) \implies ((\forall (f:\operatorname{Option}\left(\operatorname{LiveRecord}\left(k\right)\right) \to Y), ((\forall (v:\operatorname{ZMod}\left(2\right)), ((\forall (a:\operatorname{Bool}), ((((\forall (j:\operatorname{Fin}\left(p\right)), ((\forall (s:\mathbb{N}), (((s < k) \implies (f\left(\operatorname{some}\left((v,-\operatorname{cast}\left(\operatorname{val}\left(j\right) \cdot g, \operatorname{ZMod}\left(k + 1\right)\right),s)\right)\right) = labels\left(\operatorname{index}\left(\operatorname{val}\left(j\right)\right)\right)))))))) \implies (\operatorname{OriginalFiberCost}\left(k, m, \operatorname{positivek}, a, f, v\right) = \operatorname{cast}\left(h + 2, \operatorname{ENat}\right))))))))))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FiveLabelSeamCost.original_five_label_seam_cost` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let g be at least two and h be at least one. Set p=5h+1, T=gp, k=T-1 and m=5g. The five entries of labels are distinct. Phase -jg modulo T has label j for j=1,2,3,4 and label zero for every other j. In the fixed initial value fiber v, this prescription holds at every legal initial tail s<k. The function f is arbitrary elsewhere, including its label at rejection. The parameter a selects either the complete Boolean block alphabet or its locally admissible subalphabet.

The cost is the least uniform bound for a single archive-only selector on all actual finite initial block histories. Empty and rejected histories remain included. The initial output is free, every issued complete block is paid, and labels always refer to the initial joint record. The symbol positivek is the proof of positivity following from the parameter bounds. The function index returns its natural argument as an element of Fin 5 when it is below five, and zero otherwise.

For the upper bound issue pulses at positions 2g-1 and 3g-1, then h-1 all-zero blocks, then pulses at 2g-1, 4g-1 and 5g-1, and finally a leading one followed by m-1 zeros. The middle pulse combines two possible second queries; the additional pulses vanish on the opposite initial class. The three differences for the five label classes are 000, 010, 100, 110 and 011. The middle word ends in one and the final word begins in one. Their crossing run has length two, strictly below k, and the remainder of the final word clears the tail. All h+2 complete blocks are charged, including every waiting block.

For the lower bound the five initial phases with indices zero through four have five distinct labels at tail zero. Their actual joint histories are covered by the original first-window waiting and binary-discrimination lower bound. Since the first window has width five and the first revisit occurs after h blocks, this gives h+clog(2,5)-1=h+2. The case h=1 has no waiting blocks and still uses three paid blocks.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FiveLabelSeamCost.original_five_label_seam_cost`
- Dependency: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FullPositiveWindowPrice](FullPositiveWindowPrice.md)
